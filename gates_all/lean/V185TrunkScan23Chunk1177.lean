import V185TrunkScan23Chunk1176

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6972993 : List Nat := [1, 2, 5, 1, 1, 1, 1, 2, 4, 3, 2]
def baseStart_6972993 : Nat := 118140960795 + 6972993 * 2 ^ 59
def prefixEnd_6972993 : Nat := 4983230072969 + 3 ^ 40 * 6972993 * 2
def baseEnd_6972993 : Nat := 3580497009436741866519295

theorem tailTrace_6972993 : CollatzResearch.WordTrace tailWord_6972993 prefixEnd_6972993 3580497009436741866519295 := by
  unfold tailWord_6972993
  simp only [CollatzResearch.WordTrace]
  refine ⟨254325948427044728237723633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169550632284696485491815755 254325948427044728237723633)
  ·
    refine ⟨190744461320283546178292725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254325948427044728237723633 190744461320283546178292725)
    ·
      refine ⟨17882293248776582454214943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 190744461320283546178292725 17882293248776582454214943)
      ·
        refine ⟨26823439873164873681322415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17882293248776582454214943 26823439873164873681322415)
        ·
          refine ⟨40235159809747310521983623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26823439873164873681322415 40235159809747310521983623)
          ·
            refine ⟨60352739714620965782975435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40235159809747310521983623 60352739714620965782975435)
            ·
              refine ⟨90529109571931448674463153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60352739714620965782975435 90529109571931448674463153)
              ·
                refine ⟨67896832178948586505847365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90529109571931448674463153 67896832178948586505847365)
                ·
                  refine ⟨12730656033552859969846381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67896832178948586505847365 12730656033552859969846381)
                  ·
                    refine ⟨4773996012582322488692393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12730656033552859969846381 4773996012582322488692393)
                    ·
                      refine ⟨3580497009436741866519295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4773996012582322488692393 3580497009436741866519295)
                      ·
                        rfl

theorem cell23_6972993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 2, 4, 3, 2].length) (baseStart_6972993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6972993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6972993 prefixEnd_6972993 := by exact prefixLift 6972993
  have htrace : WordTrace (prefixWord ++ tailWord_6972993) baseStart_6972993 baseEnd_6972993 := by
    simpa [prefixWord, tailWord_6972993, baseEnd_6972993] using wordTrace_append hprefix tailTrace_6972993
  have hstable : (prefixWord ++ tailWord_6972993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6972993).length < 2 ^ (prefixWord ++ tailWord_6972993).sum := by decide
  have hdescent : baseEnd_6972993 < baseStart_6972993 := by decide
  rcases family_descends (prefixWord ++ tailWord_6972993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6973010 : List Nat := [3, 2, 2, 1, 2, 3, 2, 1, 2, 3, 2]
def baseStart_6973010 : Nat := 118140960795 + 6973010 * 2 ^ 59
def prefixEnd_6973010 : Nat := 4983230072969 + 3 ^ 40 * 6973010 * 2
def baseEnd_6973010 : Nat := 3580505738607868300006717

theorem tailTrace_6973010 : CollatzResearch.WordTrace tailWord_6973010 prefixEnd_6973010 3580505738607868300006717 := by
  unfold tailWord_6973010
  simp only [CollatzResearch.WordTrace]
  refine ⟨63581642116995785035273121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169551045645322093427394989 63581642116995785035273121)
  ·
    refine ⟨47686231587746838776454841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63581642116995785035273121 47686231587746838776454841)
    ·
      refine ⟨35764673690810129082341131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47686231587746838776454841 35764673690810129082341131)
      ·
        refine ⟨53647010536215193623511697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35764673690810129082341131 53647010536215193623511697)
        ·
          refine ⟨40235257902161395217633773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53647010536215193623511697 40235257902161395217633773)
          ·
            refine ⟨15088221713310523206612665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40235257902161395217633773 15088221713310523206612665)
            ·
              refine ⟨11316166284982892404959499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15088221713310523206612665 11316166284982892404959499)
              ·
                refine ⟨16974249427474338607439249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11316166284982892404959499 16974249427474338607439249)
                ·
                  refine ⟨12730687070605753955579437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16974249427474338607439249 12730687070605753955579437)
                  ·
                    refine ⟨4774007651477157733342289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12730687070605753955579437 4774007651477157733342289)
                    ·
                      refine ⟨3580505738607868300006717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4774007651477157733342289 3580505738607868300006717)
                      ·
                        rfl

theorem cell23_6973010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 2, 1, 2, 3, 2].length) (baseStart_6973010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6973010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6973010 prefixEnd_6973010 := by exact prefixLift 6973010
  have htrace : WordTrace (prefixWord ++ tailWord_6973010) baseStart_6973010 baseEnd_6973010 := by
    simpa [prefixWord, tailWord_6973010, baseEnd_6973010] using wordTrace_append hprefix tailTrace_6973010
  have hstable : (prefixWord ++ tailWord_6973010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6973010).length < 2 ^ (prefixWord ++ tailWord_6973010).sum := by decide
  have hdescent : baseEnd_6973010 < baseStart_6973010 := by decide
  rcases family_descends (prefixWord ++ tailWord_6973010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6973020 : List Nat := [2, 2, 4, 1, 2, 2, 3, 1, 1, 5]
def baseStart_6973020 : Nat := 118140960795 + 6973020 * 2 ^ 59
def prefixEnd_6973020 : Nat := 4983230072969 + 3 ^ 40 * 6973020 * 2
def baseEnd_6973020 : Nat := 1193503624471471086960557

theorem tailTrace_6973020 : CollatzResearch.WordTrace tailWord_6973020 prefixEnd_6973020 1193503624471471086960557 := by
  unfold tailWord_6973020
  simp only [CollatzResearch.WordTrace]
  refine ⟨127163466598973455924478257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169551288798631274565971009 127163466598973455924478257)
  ·
    refine ⟨95372599949230091943358693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127163466598973455924478257 95372599949230091943358693)
    ·
      refine ⟨17882362490480642239379755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95372599949230091943358693 17882362490480642239379755)
      ·
        refine ⟨26823543735720963359069633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17882362490480642239379755 26823543735720963359069633)
        ·
          refine ⟨20117657801790722519302225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26823543735720963359069633 20117657801790722519302225)
          ·
            refine ⟨15088243351343041889476669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20117657801790722519302225 15088243351343041889476669)
            ·
              refine ⟨5658091256753640708553751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15088243351343041889476669 5658091256753640708553751)
              ·
                refine ⟨8487136885130461062830627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5658091256753640708553751 8487136885130461062830627)
                ·
                  refine ⟨12730705327695691594245941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8487136885130461062830627 12730705327695691594245941)
                  ·
                    refine ⟨1193503624471471086960557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12730705327695691594245941 1193503624471471086960557)
                    ·
                      rfl

theorem cell23_6973020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 3, 1, 1, 5].length) (baseStart_6973020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6973020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6973020 prefixEnd_6973020 := by exact prefixLift 6973020
  have htrace : WordTrace (prefixWord ++ tailWord_6973020) baseStart_6973020 baseEnd_6973020 := by
    simpa [prefixWord, tailWord_6973020, baseEnd_6973020] using wordTrace_append hprefix tailTrace_6973020
  have hstable : (prefixWord ++ tailWord_6973020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6973020).length < 2 ^ (prefixWord ++ tailWord_6973020).sum := by decide
  have hdescent : baseEnd_6973020 < baseStart_6973020 := by decide
  rcases family_descends (prefixWord ++ tailWord_6973020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6973029 : List Nat := [1, 3, 1, 3, 3, 12]
def baseStart_6973029 : Nat := 118140960795 + 6973029 * 2 ^ 59
def prefixEnd_6973029 : Nat := 4983230072969 + 3 ^ 40 * 6973029 * 2
def baseEnd_6973029 : Nat := 14734631665597957718803

theorem tailTrace_6973029 : CollatzResearch.WordTrace tailWord_6973029 prefixEnd_6973029 14734631665597957718803 := by
  unfold tailWord_6973029
  simp only [CollatzResearch.WordTrace]
  refine ⟨254327261454914306386034141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169551507636609537590689427 254327261454914306386034141)
  ·
    refine ⟨95372723045592864894762803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 254327261454914306386034141 95372723045592864894762803)
    ·
      refine ⟨143059084568389297342144205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95372723045592864894762803 143059084568389297342144205)
      ·
        refine ⟨53647156713145986503304077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143059084568389297342144205 53647156713145986503304077)
        ·
          refine ⟨20117683767429744938739029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53647156713145986503304077 20117683767429744938739029)
          ·
            refine ⟨14734631665597957718803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 20117683767429744938739029 14734631665597957718803)
            ·
              rfl

theorem cell23_6973029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 12].length) (baseStart_6973029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6973029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6973029 prefixEnd_6973029 := by exact prefixLift 6973029
  have htrace : WordTrace (prefixWord ++ tailWord_6973029) baseStart_6973029 baseEnd_6973029 := by
    simpa [prefixWord, tailWord_6973029, baseEnd_6973029] using wordTrace_append hprefix tailTrace_6973029
  have hstable : (prefixWord ++ tailWord_6973029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6973029).length < 2 ^ (prefixWord ++ tailWord_6973029).sum := by decide
  have hdescent : baseEnd_6973029 < baseStart_6973029 := by decide
  rcases family_descends (prefixWord ++ tailWord_6973029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6973034 : List Nat := [3, 1, 3, 2, 1, 4, 2, 2, 1, 1, 3]
def baseStart_6973034 : Nat := 118140960795 + 6973034 * 2 ^ 59
def prefixEnd_6973034 : Nat := 4983230072969 + 3 ^ 40 * 6973034 * 2
def baseEnd_6973034 : Nat := 3580518062143576206106607

theorem tailTrace_6973034 : CollatzResearch.WordTrace tailWord_6973034 prefixEnd_6973034 3580518062143576206106607 := by
  unfold tailWord_6973034
  simp only [CollatzResearch.WordTrace]
  refine ⟨63581860954974048059991539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169551629213264128159977437 63581860954974048059991539)
  ·
    refine ⟨95372791432461072089987309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63581860954974048059991539 95372791432461072089987309)
    ·
      refine ⟨35764796787172902033745241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95372791432461072089987309 35764796787172902033745241)
      ·
        refine ⟨26823597590379676525308931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35764796787172902033745241 26823597590379676525308931)
        ·
          refine ⟨40235396385569514787963397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26823597590379676525308931 40235396385569514787963397)
          ·
            refine ⟨7544136822294284022743137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40235396385569514787963397 7544136822294284022743137)
            ·
              refine ⟨5658102616720713017057353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7544136822294284022743137 5658102616720713017057353)
              ·
                refine ⟨4243576962540534762793015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5658102616720713017057353 4243576962540534762793015)
                ·
                  refine ⟨6365365443810802144189523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4243576962540534762793015 6365365443810802144189523)
                  ·
                    refine ⟨9548048165716203216284285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6365365443810802144189523 9548048165716203216284285)
                    ·
                      refine ⟨3580518062143576206106607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9548048165716203216284285 3580518062143576206106607)
                      ·
                        rfl

theorem cell23_6973034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 2, 2, 1, 1, 3].length) (baseStart_6973034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6973034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6973034 prefixEnd_6973034 := by exact prefixLift 6973034
  have htrace : WordTrace (prefixWord ++ tailWord_6973034) baseStart_6973034 baseEnd_6973034 := by
    simpa [prefixWord, tailWord_6973034, baseEnd_6973034] using wordTrace_append hprefix tailTrace_6973034
  have hstable : (prefixWord ++ tailWord_6973034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6973034).length < 2 ^ (prefixWord ++ tailWord_6973034).sum := by decide
  have hdescent : baseEnd_6973034 < baseStart_6973034 := by decide
  rcases family_descends (prefixWord ++ tailWord_6973034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6973053 : List Nat := [1, 4, 1, 1, 4, 2, 2, 1, 1, 2, 4]
def baseStart_6973053 : Nat := 118140960795 + 6973053 * 2 ^ 59
def prefixEnd_6973053 : Nat := 4983230072969 + 3 ^ 40 * 6973053 * 2
def baseEnd_6973053 : Nat := 3580527818276011631769019

theorem tailTrace_6973053 : CollatzResearch.WordTrace tailWord_6973053 prefixEnd_6973053 3580527818276011631769019 := by
  unfold tailWord_6973053
  simp only [CollatzResearch.WordTrace]
  refine ⟨254328136806827358484907813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169552091204551572323271875 254328136806827358484907813)
  ·
    refine ⟨47686525651280129715920215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 254328136806827358484907813 47686525651280129715920215)
    ·
      refine ⟨71529788476920194573880323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47686525651280129715920215 71529788476920194573880323)
      ·
        refine ⟨107294682715380291860820485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71529788476920194573880323 107294682715380291860820485)
        ·
          refine ⟨20117753009133804723903841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 107294682715380291860820485 20117753009133804723903841)
          ·
            refine ⟨15088314756850353542927881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20117753009133804723903841 15088314756850353542927881)
            ·
              refine ⟨11316236067637765157195911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15088314756850353542927881 11316236067637765157195911)
              ·
                refine ⟨16974354101456647735793867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11316236067637765157195911 16974354101456647735793867)
                ·
                  refine ⟨25461531152184971603690801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16974354101456647735793867 25461531152184971603690801)
                  ·
                    refine ⟨19096148364138728702768101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25461531152184971603690801 19096148364138728702768101)
                    ·
                      refine ⟨3580527818276011631769019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19096148364138728702768101 3580527818276011631769019)
                      ·
                        rfl

theorem cell23_6973053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 2, 1, 1, 2, 4].length) (baseStart_6973053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6973053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6973053 prefixEnd_6973053 := by exact prefixLift 6973053
  have htrace : WordTrace (prefixWord ++ tailWord_6973053) baseStart_6973053 baseEnd_6973053 := by
    simpa [prefixWord, tailWord_6973053, baseEnd_6973053] using wordTrace_append hprefix tailTrace_6973053
  have hstable : (prefixWord ++ tailWord_6973053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6973053).length < 2 ^ (prefixWord ++ tailWord_6973053).sum := by decide
  have hdescent : baseEnd_6973053 < baseStart_6973053 := by decide
  rcases family_descends (prefixWord ++ tailWord_6973053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6973059 : List Nat := [1, 1, 1, 3, 3, 1, 1, 1, 4, 7]
def baseStart_6973059 : Nat := 118140960795 + 6973059 * 2 ^ 59
def prefixEnd_6973059 : Nat := 4983230072969 + 3 ^ 40 * 6973059 * 2
def baseEnd_6973059 : Nat := 1193510299719979536097997

theorem tailTrace_6973059 : CollatzResearch.WordTrace tailWord_6973059 prefixEnd_6973059 1193510299719979536097997 := by
  unfold tailWord_6973059
  simp only [CollatzResearch.WordTrace]
  refine ⟨254328355644805621509626231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169552237096537081006417487 254328355644805621509626231)
  ·
    refine ⟨381492533467208432264439347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254328355644805621509626231 381492533467208432264439347)
    ·
      refine ⟨572238800200812648396659021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 381492533467208432264439347 572238800200812648396659021)
      ·
        refine ⟨214589550075304743148747133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 572238800200812648396659021 214589550075304743148747133)
        ·
          refine ⟨80471081278239278680780175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 214589550075304743148747133 80471081278239278680780175)
          ·
            refine ⟨120706621917358918021170263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80471081278239278680780175 120706621917358918021170263)
            ·
              refine ⟨181059932876038377031755395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120706621917358918021170263 181059932876038377031755395)
              ·
                refine ⟨271589899314057565547633093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 181059932876038377031755395 271589899314057565547633093)
                ·
                  refine ⟨50923106121385793540181205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 271589899314057565547633093 50923106121385793540181205)
                  ·
                    refine ⟨1193510299719979536097997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50923106121385793540181205 1193510299719979536097997)
                    ·
                      rfl

theorem cell23_6973059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 4, 7].length) (baseStart_6973059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6973059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6973059 prefixEnd_6973059 := by exact prefixLift 6973059
  have htrace : WordTrace (prefixWord ++ tailWord_6973059) baseStart_6973059 baseEnd_6973059 := by
    simpa [prefixWord, tailWord_6973059, baseEnd_6973059] using wordTrace_append hprefix tailTrace_6973059
  have hstable : (prefixWord ++ tailWord_6973059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6973059).length < 2 ^ (prefixWord ++ tailWord_6973059).sum := by decide
  have hdescent : baseEnd_6973059 < baseStart_6973059 := by decide
  rcases family_descends (prefixWord ++ tailWord_6973059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6973074 : List Nat := [3, 2, 3, 1, 4, 1, 2, 1, 1, 1, 4]
def baseStart_6973074 : Nat := 118140960795 + 6973074 * 2 ^ 59
def prefixEnd_6973074 : Nat := 4983230072969 + 3 ^ 40 * 6973074 * 2
def baseEnd_6973074 : Nat := 3580538601369756049606423

theorem tailTrace_6973074 : CollatzResearch.WordTrace tailWord_6973074 prefixEnd_6973074 3580538601369756049606423 := by
  unfold tailWord_6973074
  simp only [CollatzResearch.WordTrace]
  refine ⟨63582225684937819767855569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169552601826500852714281517 63582225684937819767855569)
  ·
    refine ⟨47686669263703364825891677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63582225684937819767855569 47686669263703364825891677)
    ·
      refine ⟨17882500973888761809709379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47686669263703364825891677 17882500973888761809709379)
      ·
        refine ⟨26823751460833142714564069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17882500973888761809709379 26823751460833142714564069)
        ·
          refine ⟨5029453398906214258980763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26823751460833142714564069 5029453398906214258980763)
          ·
            refine ⟨7544180098359321388471145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5029453398906214258980763 7544180098359321388471145)
            ·
              refine ⟨5658135073769491041353359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7544180098359321388471145 5658135073769491041353359)
              ·
                refine ⟨8487202610654236562030039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5658135073769491041353359 8487202610654236562030039)
                ·
                  refine ⟨12730803915981354843045059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8487202610654236562030039 12730803915981354843045059)
                  ·
                    refine ⟨19096205873972032264567589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12730803915981354843045059 19096205873972032264567589)
                    ·
                      refine ⟨3580538601369756049606423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19096205873972032264567589 3580538601369756049606423)
                      ·
                        rfl

theorem cell23_6973074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 2, 1, 1, 1, 4].length) (baseStart_6973074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6973074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6973074 prefixEnd_6973074 := by exact prefixLift 6973074
  have htrace : WordTrace (prefixWord ++ tailWord_6973074) baseStart_6973074 baseEnd_6973074 := by
    simpa [prefixWord, tailWord_6973074, baseEnd_6973074] using wordTrace_append hprefix tailTrace_6973074
  have hstable : (prefixWord ++ tailWord_6973074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6973074).length < 2 ^ (prefixWord ++ tailWord_6973074).sum := by decide
  have hdescent : baseEnd_6973074 < baseStart_6973074 := by decide
  rcases family_descends (prefixWord ++ tailWord_6973074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6973106 : List Nat := [3, 2, 1, 1, 1, 2, 4, 1, 2, 6]
def baseStart_6973106 : Nat := 118140960795 + 6973106 * 2 ^ 59
def prefixEnd_6973106 : Nat := 4983230072969 + 3 ^ 40 * 6973106 * 2
def baseEnd_6973106 : Nat := 1193518344250233308135425

theorem tailTrace_6973106 : CollatzResearch.WordTrace tailWord_6973106 prefixEnd_6973106 1193518344250233308135425 := by
  unfold tailWord_6973106
  simp only [CollatzResearch.WordTrace]
  refine ⟨63582517468908837134146793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169553379917090232357724781 63582517468908837134146793)
  ·
    refine ⟨47686888101681627850610095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63582517468908837134146793 47686888101681627850610095)
    ·
      refine ⟨71530332152522441775915143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47686888101681627850610095 71530332152522441775915143)
      ·
        refine ⟨107295498228783662663872715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71530332152522441775915143 107295498228783662663872715)
        ·
          refine ⟨160943247343175493995809073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107295498228783662663872715 160943247343175493995809073)
          ·
            refine ⟨120707435507381620496856805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160943247343175493995809073 120707435507381620496856805)
            ·
              refine ⟨22632644157634053843160651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 120707435507381620496856805 22632644157634053843160651)
              ·
                refine ⟨33948966236451080764740977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22632644157634053843160651 33948966236451080764740977)
                ·
                  refine ⟨25461724677338310573555733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33948966236451080764740977 25461724677338310573555733)
                  ·
                    refine ⟨1193518344250233308135425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25461724677338310573555733 1193518344250233308135425)
                    ·
                      rfl

theorem cell23_6973106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 1, 2, 6].length) (baseStart_6973106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6973106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6973106 prefixEnd_6973106 := by exact prefixLift 6973106
  have htrace : WordTrace (prefixWord ++ tailWord_6973106) baseStart_6973106 baseEnd_6973106 := by
    simpa [prefixWord, tailWord_6973106, baseEnd_6973106] using wordTrace_append hprefix tailTrace_6973106
  have hstable : (prefixWord ++ tailWord_6973106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6973106).length < 2 ^ (prefixWord ++ tailWord_6973106).sum := by decide
  have hdescent : baseEnd_6973106 < baseStart_6973106 := by decide
  rcases family_descends (prefixWord ++ tailWord_6973106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6973214 : List Nat := [4, 3, 2, 2, 1, 1, 1, 1, 2, 3, 3]
def baseStart_6973214 : Nat := 118140960795 + 6973214 * 2 ^ 59
def prefixEnd_6973214 : Nat := 4983230072969 + 3 ^ 40 * 6973214 * 2
def baseEnd_6973214 : Nat := 3580610488661385501855779

theorem tailTrace_6973214 : CollatzResearch.WordTrace tailWord_6973214 prefixEnd_6973214 3580610488661385501855779 := by
  unfold tailWord_6973214
  simp only [CollatzResearch.WordTrace]
  refine ⟨31791751119905510372689837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 169556005972829388654345797 31791751119905510372689837)
  ·
    refine ⟨11921906669964566389758689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31791751119905510372689837 11921906669964566389758689)
    ·
      refine ⟨8941430002473424792319017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11921906669964566389758689 8941430002473424792319017)
      ·
        refine ⟨6706072501855068594239263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8941430002473424792319017 6706072501855068594239263)
        ·
          refine ⟨10059108752782602891358895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6706072501855068594239263 10059108752782602891358895)
          ·
            refine ⟨15088663129173904337038343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10059108752782602891358895 15088663129173904337038343)
            ·
              refine ⟨22632994693760856505557515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15088663129173904337038343 22632994693760856505557515)
              ·
                refine ⟨33949492040641284758336273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22632994693760856505557515 33949492040641284758336273)
                ·
                  refine ⟨25462119030480963568752205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33949492040641284758336273 25462119030480963568752205)
                  ·
                    refine ⟨9548294636430361338282077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25462119030480963568752205 9548294636430361338282077)
                    ·
                      refine ⟨3580610488661385501855779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9548294636430361338282077 3580610488661385501855779)
                      ·
                        rfl

theorem cell23_6973214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_6973214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6973214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6973214 prefixEnd_6973214 := by exact prefixLift 6973214
  have htrace : WordTrace (prefixWord ++ tailWord_6973214) baseStart_6973214 baseEnd_6973214 := by
    simpa [prefixWord, tailWord_6973214, baseEnd_6973214] using wordTrace_append hprefix tailTrace_6973214
  have hstable : (prefixWord ++ tailWord_6973214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6973214).length < 2 ^ (prefixWord ++ tailWord_6973214).sum := by decide
  have hdescent : baseEnd_6973214 < baseStart_6973214 := by decide
  rcases family_descends (prefixWord ++ tailWord_6973214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6973220 : List Nat := [2, 3, 1, 3, 2, 1, 1, 1, 1, 6, 2]
def baseStart_6973220 : Nat := 118140960795 + 6973220 * 2 ^ 59
def prefixEnd_6973220 : Nat := 4983230072969 + 3 ^ 40 * 6973220 * 2
def baseEnd_6973220 : Nat := 3580613569545312478380751

theorem tailTrace_6973220 : CollatzResearch.WordTrace tailWord_6973220 prefixEnd_6973220 3580613569545312478380751 := by
  unfold tailWord_6973220
  simp only [CollatzResearch.WordTrace]
  refine ⟨127167113898611173003118557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169556151864814897337491409 127167113898611173003118557)
  ·
    refine ⟨47687667711979189876169459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127167113898611173003118557 47687667711979189876169459)
    ·
      refine ⟨71531501567968784814254189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47687667711979189876169459 71531501567968784814254189)
      ·
        refine ⟨26824313087988294305345321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71531501567968784814254189 26824313087988294305345321)
        ·
          refine ⟨20118234815991220729008991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26824313087988294305345321 20118234815991220729008991)
          ·
            refine ⟨30177352223986831093513487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20118234815991220729008991 30177352223986831093513487)
            ·
              refine ⟨45266028335980246640270231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30177352223986831093513487 45266028335980246640270231)
              ·
                refine ⟨67899042503970369960405347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45266028335980246640270231 67899042503970369960405347)
                ·
                  refine ⟨101848563755955554940608021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67899042503970369960405347 101848563755955554940608021)
                  ·
                    refine ⟨4774151426060416637841001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 101848563755955554940608021 4774151426060416637841001)
                    ·
                      refine ⟨3580613569545312478380751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4774151426060416637841001 3580613569545312478380751)
                      ·
                        rfl

theorem cell23_6973220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 1, 1, 6, 2].length) (baseStart_6973220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6973220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6973220 prefixEnd_6973220 := by exact prefixLift 6973220
  have htrace : WordTrace (prefixWord ++ tailWord_6973220) baseStart_6973220 baseEnd_6973220 := by
    simpa [prefixWord, tailWord_6973220, baseEnd_6973220] using wordTrace_append hprefix tailTrace_6973220
  have hstable : (prefixWord ++ tailWord_6973220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6973220).length < 2 ^ (prefixWord ++ tailWord_6973220).sum := by decide
  have hdescent : baseEnd_6973220 < baseStart_6973220 := by decide
  rcases family_descends (prefixWord ++ tailWord_6973220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6973237 : List Nat := [1, 3, 3, 1, 4, 2, 1, 1, 2, 1, 4]
def baseStart_6973237 : Nat := 118140960795 + 6973237 * 2 ^ 59
def prefixEnd_6973237 : Nat := 4983230072969 + 3 ^ 40 * 6973237 * 2
def baseEnd_6973237 : Nat := 3580622298716438911868173

theorem tailTrace_6973237 : CollatzResearch.WordTrace tailWord_6973237 prefixEnd_6973237 3580622298716438911868173 := by
  unfold tailWord_6973237
  simp only [CollatzResearch.WordTrace]
  refine ⟨254334847838160757909605965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169556565225440505273070643 254334847838160757909605965)
  ·
    refine ⟨95375567939310284216102237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 254334847838160757909605965 95375567939310284216102237)
    ·
      refine ⟨35765837977241356581038339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95375567939310284216102237 35765837977241356581038339)
      ·
        refine ⟨53648756965862034871557509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35765837977241356581038339 53648756965862034871557509)
        ·
          refine ⟨10059141931099131538417033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53648756965862034871557509 10059141931099131538417033)
          ·
            refine ⟨7544356448324348653812775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10059141931099131538417033 7544356448324348653812775)
            ·
              refine ⟨11316534672486522980719163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7544356448324348653812775 11316534672486522980719163)
              ·
                refine ⟨16974802008729784471078745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11316534672486522980719163 16974802008729784471078745)
                ·
                  refine ⟨12731101506547338353309059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16974802008729784471078745 12731101506547338353309059)
                  ·
                    refine ⟨19096652259821007529963589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12731101506547338353309059 19096652259821007529963589)
                    ·
                      refine ⟨3580622298716438911868173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19096652259821007529963589 3580622298716438911868173)
                      ·
                        rfl

theorem cell23_6973237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 1, 1, 2, 1, 4].length) (baseStart_6973237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6973237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6973237 prefixEnd_6973237 := by exact prefixLift 6973237
  have htrace : WordTrace (prefixWord ++ tailWord_6973237) baseStart_6973237 baseEnd_6973237 := by
    simpa [prefixWord, tailWord_6973237, baseEnd_6973237] using wordTrace_append hprefix tailTrace_6973237
  have hstable : (prefixWord ++ tailWord_6973237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6973237).length < 2 ^ (prefixWord ++ tailWord_6973237).sum := by decide
  have hdescent : baseEnd_6973237 < baseStart_6973237 := by decide
  rcases family_descends (prefixWord ++ tailWord_6973237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6973240 : List Nat := [2, 1, 2, 1, 3, 3, 3, 1, 2, 2, 3]
def baseStart_6973240 : Nat := 118140960795 + 6973240 * 2 ^ 59
def prefixEnd_6973240 : Nat := 4983230072969 + 3 ^ 40 * 6973240 * 2
def baseEnd_6973240 : Nat := 3580623839158402400130659

theorem tailTrace_6973240 : CollatzResearch.WordTrace tailWord_6973240 prefixEnd_6973240 3580623839158402400130659 := by
  unfold tailWord_6973240
  simp only [CollatzResearch.WordTrace]
  refine ⟨127167478628574944710982587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169556638171433259614643449 127167478628574944710982587)
  ·
    refine ⟨190751217942862417066473881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127167478628574944710982587 190751217942862417066473881)
    ·
      refine ⟨143063413457146812799855411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190751217942862417066473881 143063413457146812799855411)
      ·
        refine ⟨214595120185720219199783117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143063413457146812799855411 214595120185720219199783117)
        ·
          refine ⟨80473170069645082199918669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 214595120185720219199783117 80473170069645082199918669)
          ·
            refine ⟨30177438776116905824969501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80473170069645082199918669 30177438776116905824969501)
            ·
              refine ⟨11316539541043839684363563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30177438776116905824969501 11316539541043839684363563)
              ·
                refine ⟨16974809311565759526545345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11316539541043839684363563 16974809311565759526545345)
                ·
                  refine ⟨12731106983674319644909009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16974809311565759526545345 12731106983674319644909009)
                  ·
                    refine ⟨9548330237755739733681757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12731106983674319644909009 9548330237755739733681757)
                    ·
                      refine ⟨3580623839158402400130659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9548330237755739733681757 3580623839158402400130659)
                      ·
                        rfl

theorem cell23_6973240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 3, 1, 2, 2, 3].length) (baseStart_6973240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6973240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6973240 prefixEnd_6973240 := by exact prefixLift 6973240
  have htrace : WordTrace (prefixWord ++ tailWord_6973240) baseStart_6973240 baseEnd_6973240 := by
    simpa [prefixWord, tailWord_6973240, baseEnd_6973240] using wordTrace_append hprefix tailTrace_6973240
  have hstable : (prefixWord ++ tailWord_6973240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6973240).length < 2 ^ (prefixWord ++ tailWord_6973240).sum := by decide
  have hdescent : baseEnd_6973240 < baseStart_6973240 := by decide
  rcases family_descends (prefixWord ++ tailWord_6973240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6973254 : List Nat := [6, 1, 1, 2, 1, 1, 1, 2, 2, 4, 2]
def baseStart_6973254 : Nat := 118140960795 + 6973254 * 2 ^ 59
def prefixEnd_6973254 : Nat := 4983230072969 + 3 ^ 40 * 6973254 * 2
def baseEnd_6973254 : Nat := 3580631027887565345355595

theorem tailTrace_6973254 : CollatzResearch.WordTrace tailWord_6973254 prefixEnd_6973254 3580631027887565345355595 := by
  unfold tailWord_6973254
  simp only [CollatzResearch.WordTrace]
  refine ⟨7947983371221849056655463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 169556978586066113208649877 7947983371221849056655463)
  ·
    refine ⟨11921975056832773584983195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7947983371221849056655463 11921975056832773584983195)
    ·
      refine ⟨17882962585249160377474793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11921975056832773584983195 17882962585249160377474793)
      ·
        refine ⟨13412221938936870283106095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17882962585249160377474793 13412221938936870283106095)
        ·
          refine ⟨20118332908405305424659143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13412221938936870283106095 20118332908405305424659143)
          ·
            refine ⟨30177499362607958136988715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20118332908405305424659143 30177499362607958136988715)
            ·
              refine ⟨45266249043911937205483073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30177499362607958136988715 45266249043911937205483073)
              ·
                refine ⟨33949686782933952904112305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45266249043911937205483073 33949686782933952904112305)
                ·
                  refine ⟨25462265087200464678084229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33949686782933952904112305 25462265087200464678084229)
                  ·
                    refine ⟨4774174703850087127140793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25462265087200464678084229 4774174703850087127140793)
                    ·
                      refine ⟨3580631027887565345355595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4774174703850087127140793 3580631027887565345355595)
                      ·
                        rfl

theorem cell23_6973254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 2, 2, 4, 2].length) (baseStart_6973254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6973254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6973254 prefixEnd_6973254 := by exact prefixLift 6973254
  have htrace : WordTrace (prefixWord ++ tailWord_6973254) baseStart_6973254 baseEnd_6973254 := by
    simpa [prefixWord, tailWord_6973254, baseEnd_6973254] using wordTrace_append hprefix tailTrace_6973254
  have hstable : (prefixWord ++ tailWord_6973254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6973254).length < 2 ^ (prefixWord ++ tailWord_6973254).sum := by decide
  have hdescent : baseEnd_6973254 < baseStart_6973254 := by decide
  rcases family_descends (prefixWord ++ tailWord_6973254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6973280 : List Nat := [2, 1, 1, 3, 3, 2, 1, 2, 1, 5, 2]
def baseStart_6973280 : Nat := 118140960795 + 6973280 * 2 ^ 59
def prefixEnd_6973280 : Nat := 4983230072969 + 3 ^ 40 * 6973280 * 2
def baseEnd_6973280 : Nat := 3580644378384582243630475

theorem tailTrace_6973280 : CollatzResearch.WordTrace tailWord_6973280 prefixEnd_6973280 3580644378384582243630475 := by
  unfold tailWord_6973280
  simp only [CollatzResearch.WordTrace]
  refine ⟨127168208088502488126710647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169557610784669984168947529 127168208088502488126710647)
  ·
    refine ⟨190752312132753732190065971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127168208088502488126710647 190752312132753732190065971)
    ·
      refine ⟨286128468199130598285098957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190752312132753732190065971 286128468199130598285098957)
      ·
        refine ⟨107298175574673974356912109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 286128468199130598285098957 107298175574673974356912109)
        ·
          refine ⟨40236815840502740383842041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107298175574673974356912109 40236815840502740383842041)
          ·
            refine ⟨30177611880377055287881531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40236815840502740383842041 30177611880377055287881531)
            ·
              refine ⟨45266417820565582931822297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30177611880377055287881531 45266417820565582931822297)
              ·
                refine ⟨33949813365424187198866723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45266417820565582931822297 33949813365424187198866723)
                ·
                  refine ⟨50924720048136280798300085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33949813365424187198866723 50924720048136280798300085)
                  ·
                    refine ⟨4774192504512776324840633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50924720048136280798300085 4774192504512776324840633)
                    ·
                      refine ⟨3580644378384582243630475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4774192504512776324840633 3580644378384582243630475)
                      ·
                        rfl

theorem cell23_6973280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 2, 1, 5, 2].length) (baseStart_6973280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6973280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6973280 prefixEnd_6973280 := by exact prefixLift 6973280
  have htrace : WordTrace (prefixWord ++ tailWord_6973280) baseStart_6973280 baseEnd_6973280 := by
    simpa [prefixWord, tailWord_6973280, baseEnd_6973280] using wordTrace_append hprefix tailTrace_6973280
  have hstable : (prefixWord ++ tailWord_6973280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6973280).length < 2 ^ (prefixWord ++ tailWord_6973280).sum := by decide
  have hdescent : baseEnd_6973280 < baseStart_6973280 := by decide
  rcases family_descends (prefixWord ++ tailWord_6973280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6973333 : List Nat := [1, 3, 2, 1, 1, 3, 4, 8]
def baseStart_6973333 : Nat := 118140960795 + 6973333 * 2 ^ 59
def prefixEnd_6973333 : Nat := 4983230072969 + 3 ^ 40 * 6973333 * 2
def baseEnd_6973333 : Nat := 132617466402195205046953

theorem tailTrace_6973333 : CollatzResearch.WordTrace tailWord_6973333 prefixEnd_6973333 132617466402195205046953 := by
  unfold tailWord_6973333
  simp only [CollatzResearch.WordTrace]
  refine ⟨254338349245812966305100653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169558899497208644203400435 254338349245812966305100653)
  ·
    refine ⟨95376880967179862364412745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 254338349245812966305100653 95376880967179862364412745)
    ·
      refine ⟨71532660725384896773309559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95376880967179862364412745 71532660725384896773309559)
      ·
        refine ⟨107298991088077345159964339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71532660725384896773309559 107298991088077345159964339)
        ·
          refine ⟨160948486632116017739946509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107298991088077345159964339 160948486632116017739946509)
          ·
            refine ⟨60355682487043506652479941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 160948486632116017739946509 60355682487043506652479941)
            ·
              refine ⟨11316690466320657497339989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60355682487043506652479941 11316690466320657497339989)
              ·
                refine ⟨132617466402195205046953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11316690466320657497339989 132617466402195205046953)
                ·
                  rfl

theorem cell23_6973333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 4, 8].length) (baseStart_6973333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6973333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6973333 prefixEnd_6973333 := by exact prefixLift 6973333
  have htrace : WordTrace (prefixWord ++ tailWord_6973333) baseStart_6973333 baseEnd_6973333 := by
    simpa [prefixWord, tailWord_6973333, baseEnd_6973333] using wordTrace_append hprefix tailTrace_6973333
  have hstable : (prefixWord ++ tailWord_6973333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6973333).length < 2 ^ (prefixWord ++ tailWord_6973333).sum := by decide
  have hdescent : baseEnd_6973333 < baseStart_6973333 := by decide
  rcases family_descends (prefixWord ++ tailWord_6973333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6973337 : List Nat := [1, 2, 1, 2, 1, 3, 6, 1, 2, 4]
def baseStart_6973337 : Nat := 118140960795 + 6973337 * 2 ^ 59
def prefixEnd_6973337 : Nat := 4983230072969 + 3 ^ 40 * 6973337 * 2
def baseEnd_6973337 : Nat := 1193557882260629506872571

theorem tailTrace_6973337 : CollatzResearch.WordTrace tailWord_6973337 prefixEnd_6973337 1193557882260629506872571 := by
  unfold tailWord_6973337
  simp only [CollatzResearch.WordTrace]
  refine ⟨254338495137798474988246265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169558996758532316658830843 254338495137798474988246265)
  ·
    refine ⟨190753871353348856241184699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254338495137798474988246265 190753871353348856241184699)
    ·
      refine ⟨286130807030023284361777049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190753871353348856241184699 286130807030023284361777049)
      ·
        refine ⟨214598105272517463271332787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 286130807030023284361777049 214598105272517463271332787)
        ·
          refine ⟨321897157908776194906999181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214598105272517463271332787 321897157908776194906999181)
          ·
            refine ⟨120711434215791073090124693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 321897157908776194906999181 120711434215791073090124693)
            ·
              refine ⟨5658348478865206551099595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 120711434215791073090124693 5658348478865206551099595)
              ·
                refine ⟨8487522718297809826649393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5658348478865206551099595 8487522718297809826649393)
                ·
                  refine ⟨6365642038723357369987045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8487522718297809826649393 6365642038723357369987045)
                  ·
                    refine ⟨1193557882260629506872571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6365642038723357369987045 1193557882260629506872571)
                    ·
                      rfl

theorem cell23_6973337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 6, 1, 2, 4].length) (baseStart_6973337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6973337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6973337 prefixEnd_6973337 := by exact prefixLift 6973337
  have htrace : WordTrace (prefixWord ++ tailWord_6973337) baseStart_6973337 baseEnd_6973337 := by
    simpa [prefixWord, tailWord_6973337, baseEnd_6973337] using wordTrace_append hprefix tailTrace_6973337
  have hstable : (prefixWord ++ tailWord_6973337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6973337).length < 2 ^ (prefixWord ++ tailWord_6973337).sum := by decide
  have hdescent : baseEnd_6973337 < baseStart_6973337 := by decide
  rcases family_descends (prefixWord ++ tailWord_6973337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6973340 : List Nat := [2, 2, 3, 3, 1, 1, 2, 1, 1, 1, 6]
def baseStart_6973340 : Nat := 118140960795 + 6973340 * 2 ^ 59
def prefixEnd_6973340 : Nat := 4983230072969 + 3 ^ 40 * 6973340 * 2
def baseEnd_6973340 : Nat := 3580675187223852008880199

theorem tailTrace_6973340 : CollatzResearch.WordTrace tailWord_6973340 prefixEnd_6973340 3580675187223852008880199 := by
  unfold tailWord_6973340
  simp only [CollatzResearch.WordTrace]
  refine ⟨127169302278393803250302737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169559069704525071000403649 127169302278393803250302737)
  ·
    refine ⟨95376976708795352437727053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127169302278393803250302737 95376976708795352437727053)
    ·
      refine ⟨35766366265798257164147645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95376976708795352437727053 35766366265798257164147645)
      ·
        refine ⟨13412387349674346436555367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35766366265798257164147645 13412387349674346436555367)
        ·
          refine ⟨20118581024511519654833051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13412387349674346436555367 20118581024511519654833051)
          ·
            refine ⟨30177871536767279482249577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20118581024511519654833051 30177871536767279482249577)
            ·
              refine ⟨22633403652575459611687183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30177871536767279482249577 22633403652575459611687183)
              ·
                refine ⟨33950105478863189417530775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22633403652575459611687183 33950105478863189417530775)
                ·
                  refine ⟨50925158218294784126296163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33950105478863189417530775 50925158218294784126296163)
                  ·
                    refine ⟨76387737327442176189444245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50925158218294784126296163 76387737327442176189444245)
                    ·
                      refine ⟨3580675187223852008880199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76387737327442176189444245 3580675187223852008880199)
                      ·
                        rfl

theorem cell23_6973340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_6973340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6973340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6973340 prefixEnd_6973340 := by exact prefixLift 6973340
  have htrace : WordTrace (prefixWord ++ tailWord_6973340) baseStart_6973340 baseEnd_6973340 := by
    simpa [prefixWord, tailWord_6973340, baseEnd_6973340] using wordTrace_append hprefix tailTrace_6973340
  have hstable : (prefixWord ++ tailWord_6973340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6973340).length < 2 ^ (prefixWord ++ tailWord_6973340).sum := by decide
  have hdescent : baseEnd_6973340 < baseStart_6973340 := by decide
  rcases family_descends (prefixWord ++ tailWord_6973340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6973358 : List Nat := [4, 1, 5, 1, 1, 1, 3, 1, 1, 5]
def baseStart_6973358 : Nat := 118140960795 + 6973358 * 2 ^ 59
def prefixEnd_6973358 : Nat := 4983230072969 + 3 ^ 40 * 6973358 * 2
def baseEnd_6973358 : Nat := 1193561476625210979485039

theorem tailTrace_6973358 : CollatzResearch.WordTrace tailWord_6973358 prefixEnd_6973358 1193561476625210979485039 := by
  unfold tailWord_6973358
  simp only [CollatzResearch.WordTrace]
  refine ⟨31792407633840299446845091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 169559507380481597049840485 31792407633840299446845091)
  ·
    refine ⟨47688611450760449170267637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31792407633840299446845091 47688611450760449170267637)
    ·
      refine ⟨4470807323508792109712591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 47688611450760449170267637 4470807323508792109712591)
      ·
        refine ⟨6706210985263188164568887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4470807323508792109712591 6706210985263188164568887)
        ·
          refine ⟨10059316477894782246853331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6706210985263188164568887 10059316477894782246853331)
          ·
            refine ⟨15088974716842173370279997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10059316477894782246853331 15088974716842173370279997)
            ·
              refine ⟨5658365518815815013854999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15088974716842173370279997 5658365518815815013854999)
              ·
                refine ⟨8487548278223722520782499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5658365518815815013854999 8487548278223722520782499)
                ·
                  refine ⟨12731322417335583781173749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8487548278223722520782499 12731322417335583781173749)
                  ·
                    refine ⟨1193561476625210979485039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12731322417335583781173749 1193561476625210979485039)
                    ·
                      rfl

theorem cell23_6973358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_6973358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6973358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6973358 prefixEnd_6973358 := by exact prefixLift 6973358
  have htrace : WordTrace (prefixWord ++ tailWord_6973358) baseStart_6973358 baseEnd_6973358 := by
    simpa [prefixWord, tailWord_6973358, baseEnd_6973358] using wordTrace_append hprefix tailTrace_6973358
  have hstable : (prefixWord ++ tailWord_6973358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6973358).length < 2 ^ (prefixWord ++ tailWord_6973358).sum := by decide
  have hdescent : baseEnd_6973358 < baseStart_6973358 := by decide
  rcases family_descends (prefixWord ++ tailWord_6973358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6973394 : List Nat := [3, 2, 2, 3, 2, 1, 2, 1, 1, 3, 3]
def baseStart_6973394 : Nat := 118140960795 + 6973394 * 2 ^ 59
def prefixEnd_6973394 : Nat := 4983230072969 + 3 ^ 40 * 6973394 * 2
def baseEnd_6973394 : Nat := 3580702915179194797604951

theorem tailTrace_6973394 : CollatzResearch.WordTrace tailWord_6973394 prefixEnd_6973394 3580702915179194797604951 := by
  unfold tailWord_6973394
  simp only [CollatzResearch.WordTrace]
  refine ⟨63585143524647993430767809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169560382732394649148714157 63585143524647993430767809)
  ·
    refine ⟨47688857643485995073075857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63585143524647993430767809 47688857643485995073075857)
    ·
      refine ⟨35766643232614496304806893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47688857643485995073075857 35766643232614496304806893)
      ·
        refine ⟨13412491212230436114302585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35766643232614496304806893 13412491212230436114302585)
        ·
          refine ⟨10059368409172827085726939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13412491212230436114302585 10059368409172827085726939)
          ·
            refine ⟨15089052613759240628590409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10059368409172827085726939 15089052613759240628590409)
            ·
              refine ⟨11316789460319430471442807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15089052613759240628590409 11316789460319430471442807)
              ·
                refine ⟨16975184190479145707164211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11316789460319430471442807 16975184190479145707164211)
                ·
                  refine ⟨25462776285718718560746317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16975184190479145707164211 25462776285718718560746317)
                  ·
                    refine ⟨9548541107144519460279869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25462776285718718560746317 9548541107144519460279869)
                    ·
                      refine ⟨3580702915179194797604951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9548541107144519460279869 3580702915179194797604951)
                      ·
                        rfl

theorem cell23_6973394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_6973394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6973394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6973394 prefixEnd_6973394 := by exact prefixLift 6973394
  have htrace : WordTrace (prefixWord ++ tailWord_6973394) baseStart_6973394 baseEnd_6973394 := by
    simpa [prefixWord, tailWord_6973394, baseEnd_6973394] using wordTrace_append hprefix tailTrace_6973394
  have hstable : (prefixWord ++ tailWord_6973394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6973394).length < 2 ^ (prefixWord ++ tailWord_6973394).sum := by decide
  have hdescent : baseEnd_6973394 < baseStart_6973394 := by decide
  rcases family_descends (prefixWord ++ tailWord_6973394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6973423 : List Nat := [1, 1, 2, 1, 4, 2, 1, 2, 9]
def baseStart_6973423 : Nat := 118140960795 + 6973423 * 2 ^ 59
def prefixEnd_6973423 : Nat := 4983230072969 + 3 ^ 40 * 6973423 * 2
def baseEnd_6973423 : Nat := 397857534013130576015813

theorem tailTrace_6973423 : CollatzResearch.WordTrace tailWord_6973423 prefixEnd_6973423 397857534013130576015813 := by
  unfold tailWord_6973423
  simp only [CollatzResearch.WordTrace]
  refine ⟨254341631815486911675876923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169561087876991274450584615 254341631815486911675876923)
  ·
    refine ⟨381512447723230367513815385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254341631815486911675876923 381512447723230367513815385)
    ·
      refine ⟨286134335792422775635361539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 381512447723230367513815385 286134335792422775635361539)
      ·
        refine ⟨429201503688634163453042309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286134335792422775635361539 429201503688634163453042309)
        ·
          refine ⟨80475281941618905647445433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 429201503688634163453042309 80475281941618905647445433)
          ·
            refine ⟨60356461456214179235584075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80475281941618905647445433 60356461456214179235584075)
            ·
              refine ⟨90534692184321268853376113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60356461456214179235584075 90534692184321268853376113)
              ·
                refine ⟨67901019138240951640032085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90534692184321268853376113 67901019138240951640032085)
                ·
                  refine ⟨397857534013130576015813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 67901019138240951640032085 397857534013130576015813)
                  ·
                    rfl

theorem cell23_6973423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 2, 9].length) (baseStart_6973423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6973423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6973423 prefixEnd_6973423 := by exact prefixLift 6973423
  have htrace : WordTrace (prefixWord ++ tailWord_6973423) baseStart_6973423 baseEnd_6973423 := by
    simpa [prefixWord, tailWord_6973423, baseEnd_6973423] using wordTrace_append hprefix tailTrace_6973423
  have hstable : (prefixWord ++ tailWord_6973423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6973423).length < 2 ^ (prefixWord ++ tailWord_6973423).sum := by decide
  have hdescent : baseEnd_6973423 < baseStart_6973423 := by decide
  rcases family_descends (prefixWord ++ tailWord_6973423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6973451 : List Nat := [1, 1, 1, 1, 6, 1, 5, 1, 2, 2, 2]
def baseStart_6973451 : Nat := 118140960795 + 6973451 * 2 ^ 59
def prefixEnd_6973451 : Nat := 4983230072969 + 3 ^ 40 * 6973451 * 2
def baseEnd_6973451 : Nat := 3580732183576501074592189

theorem tailTrace_6973451 : CollatzResearch.WordTrace tailWord_6973451 prefixEnd_6973451 3580732183576501074592189 := by
  unfold tailWord_6973451
  simp only [CollatzResearch.WordTrace]
  refine ⟨254342653059385472457896207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169561768706256981638597471 254342653059385472457896207)
  ·
    refine ⟨381513979589078208686844311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254342653059385472457896207 381513979589078208686844311)
    ·
      refine ⟨572270969383617313030266467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 381513979589078208686844311 572270969383617313030266467)
      ·
        refine ⟨858406454075425969545399701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 572270969383617313030266467 858406454075425969545399701)
        ·
          refine ⟨40237802534785592322440611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 858406454075425969545399701 40237802534785592322440611)
          ·
            refine ⟨60356703802178388483660917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40237802534785592322440611 60356703802178388483660917)
            ·
              refine ⟨5658440981454223920343211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 60356703802178388483660917 5658440981454223920343211)
              ·
                refine ⟨8487661472181335880514817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5658440981454223920343211 8487661472181335880514817)
                ·
                  refine ⟨6365746104136001910386113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8487661472181335880514817 6365746104136001910386113)
                  ·
                    refine ⟨4774309578102001432789585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6365746104136001910386113 4774309578102001432789585)
                    ·
                      refine ⟨3580732183576501074592189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4774309578102001432789585 3580732183576501074592189)
                      ·
                        rfl

theorem cell23_6973451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 5, 1, 2, 2, 2].length) (baseStart_6973451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6973451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6973451 prefixEnd_6973451 := by exact prefixLift 6973451
  have htrace : WordTrace (prefixWord ++ tailWord_6973451) baseStart_6973451 baseEnd_6973451 := by
    simpa [prefixWord, tailWord_6973451, baseEnd_6973451] using wordTrace_append hprefix tailTrace_6973451
  have hstable : (prefixWord ++ tailWord_6973451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6973451).length < 2 ^ (prefixWord ++ tailWord_6973451).sum := by decide
  have hdescent : baseEnd_6973451 < baseStart_6973451 := by decide
  rcases family_descends (prefixWord ++ tailWord_6973451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6973494 : List Nat := [5, 1, 2, 1, 1, 1, 2, 1, 2, 5, 2]
def baseStart_6973494 : Nat := 118140960795 + 6973494 * 2 ^ 59
def prefixEnd_6973494 : Nat := 4983230072969 + 3 ^ 40 * 6973494 * 2
def baseEnd_6973494 : Nat := 3580754263244644406354491

theorem tailTrace_6973494 : CollatzResearch.WordTrace tailWord_6973494 prefixEnd_6973494 3580754263244644406354491 := by
  unfold tailWord_6973494
  simp only [CollatzResearch.WordTrace]
  refine ⟨15896513837389355675106971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 169562814265486460534474357 15896513837389355675106971)
  ·
    refine ⟨23844770756084033512660457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15896513837389355675106971 23844770756084033512660457)
    ·
      refine ⟨17883578067063025134495343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23844770756084033512660457 17883578067063025134495343)
      ·
        refine ⟨26825367100594537701743015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17883578067063025134495343 26825367100594537701743015)
        ·
          refine ⟨40238050650891806552614523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26825367100594537701743015 40238050650891806552614523)
          ·
            refine ⟨60357075976337709828921785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40238050650891806552614523 60357075976337709828921785)
            ·
              refine ⟨45267806982253282371691339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60357075976337709828921785 45267806982253282371691339)
              ·
                refine ⟨67901710473379923557537009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45267806982253282371691339 67901710473379923557537009)
                ·
                  refine ⟨50926282855034942668152757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67901710473379923557537009 50926282855034942668152757)
                  ·
                    refine ⟨4774339017659525875139321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50926282855034942668152757 4774339017659525875139321)
                    ·
                      refine ⟨3580754263244644406354491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4774339017659525875139321 3580754263244644406354491)
                      ·
                        rfl

theorem cell23_6973494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 1, 2, 5, 2].length) (baseStart_6973494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6973494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6973494 prefixEnd_6973494 := by exact prefixLift 6973494
  have htrace : WordTrace (prefixWord ++ tailWord_6973494) baseStart_6973494 baseEnd_6973494 := by
    simpa [prefixWord, tailWord_6973494, baseEnd_6973494] using wordTrace_append hprefix tailTrace_6973494
  have hstable : (prefixWord ++ tailWord_6973494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6973494).length < 2 ^ (prefixWord ++ tailWord_6973494).sum := by decide
  have hdescent : baseEnd_6973494 < baseStart_6973494 := by decide
  rcases family_descends (prefixWord ++ tailWord_6973494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6973497 : List Nat := [1, 2, 1, 5, 3, 1, 1, 1, 1, 2, 5]
def baseStart_6973497 : Nat := 118140960795 + 6973497 * 2 ^ 59
def prefixEnd_6973497 : Nat := 4983230072969 + 3 ^ 40 * 6973497 * 2
def baseEnd_6973497 : Nat := 3580755803686607894616977

theorem tailTrace_6973497 : CollatzResearch.WordTrace tailWord_6973497 prefixEnd_6973497 3580755803686607894616977 := by
  unfold tailWord_6973497
  simp only [CollatzResearch.WordTrace]
  refine ⟨254344330817218822314070745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169562887211479214876047163 254344330817218822314070745)
  ·
    refine ⟨190758248112914116735553059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254344330817218822314070745 190758248112914116735553059)
    ·
      refine ⟨286137372169371175103329589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190758248112914116735553059 286137372169371175103329589)
      ·
        refine ⟨26825378640878547665937149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 286137372169371175103329589 26825378640878547665937149)
        ·
          refine ⟨10059516990329455374726431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26825378640878547665937149 10059516990329455374726431)
          ·
            refine ⟨15089275485494183062089647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10059516990329455374726431 15089275485494183062089647)
            ·
              refine ⟨22633913228241274593134471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15089275485494183062089647 22633913228241274593134471)
              ·
                refine ⟨33950869842361911889701707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22633913228241274593134471 33950869842361911889701707)
                ·
                  refine ⟨50926304763542867834552561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33950869842361911889701707 50926304763542867834552561)
                  ·
                    refine ⟨38194728572657150875914421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50926304763542867834552561 38194728572657150875914421)
                    ·
                      refine ⟨3580755803686607894616977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38194728572657150875914421 3580755803686607894616977)
                      ·
                        rfl

theorem cell23_6973497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 1, 1, 2, 5].length) (baseStart_6973497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6973497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6973497 prefixEnd_6973497 := by exact prefixLift 6973497
  have htrace : WordTrace (prefixWord ++ tailWord_6973497) baseStart_6973497 baseEnd_6973497 := by
    simpa [prefixWord, tailWord_6973497, baseEnd_6973497] using wordTrace_append hprefix tailTrace_6973497
  have hstable : (prefixWord ++ tailWord_6973497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6973497).length < 2 ^ (prefixWord ++ tailWord_6973497).sum := by decide
  have hdescent : baseEnd_6973497 < baseStart_6973497 := by decide
  rcases family_descends (prefixWord ++ tailWord_6973497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6973502 : List Nat := [4, 2, 1, 3, 3, 1, 2, 1, 2, 2, 2]
def baseStart_6973502 : Nat := 118140960795 + 6973502 * 2 ^ 59
def prefixEnd_6973502 : Nat := 4983230072969 + 3 ^ 40 * 6973502 * 2
def baseEnd_6973502 : Nat := 3580758371089880375054455

theorem tailTrace_6973502 : CollatzResearch.WordTrace tailWord_6973502 prefixEnd_6973502 3580758371089880375054455 := by
  unfold tailWord_6973502
  simp only [CollatzResearch.WordTrace]
  refine ⟨31793064147775088521000345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 169563008788133805445335173 31793064147775088521000345)
  ·
    refine ⟨23844798110831316390750259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31793064147775088521000345 23844798110831316390750259)
    ·
      refine ⟨35767197166246974586125389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23844798110831316390750259 35767197166246974586125389)
      ·
        refine ⟨13412698937342615469797021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35767197166246974586125389 13412698937342615469797021)
        ·
          refine ⟨5029762101503480801173883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13412698937342615469797021 5029762101503480801173883)
          ·
            refine ⟨7544643152255221201760825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5029762101503480801173883 7544643152255221201760825)
            ·
              refine ⟨5658482364191415901320619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7544643152255221201760825 5658482364191415901320619)
              ·
                refine ⟨8487723546287123851980929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5658482364191415901320619 8487723546287123851980929)
                ·
                  refine ⟨6365792659715342888985697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8487723546287123851980929 6365792659715342888985697)
                  ·
                    refine ⟨4774344494786507166739273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6365792659715342888985697 4774344494786507166739273)
                    ·
                      refine ⟨3580758371089880375054455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4774344494786507166739273 3580758371089880375054455)
                      ·
                        rfl

theorem cell23_6973502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 2, 1, 2, 2, 2].length) (baseStart_6973502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6973502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6973502 prefixEnd_6973502 := by exact prefixLift 6973502
  have htrace : WordTrace (prefixWord ++ tailWord_6973502) baseStart_6973502 baseEnd_6973502 := by
    simpa [prefixWord, tailWord_6973502, baseEnd_6973502] using wordTrace_append hprefix tailTrace_6973502
  have hstable : (prefixWord ++ tailWord_6973502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6973502).length < 2 ^ (prefixWord ++ tailWord_6973502).sum := by decide
  have hdescent : baseEnd_6973502 < baseStart_6973502 := by decide
  rcases family_descends (prefixWord ++ tailWord_6973502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6973527 : List Nat := [1, 1, 3, 2, 2, 1, 3, 3, 2, 2, 3]
def baseStart_6973527 : Nat := 118140960795 + 6973527 * 2 ^ 59
def prefixEnd_6973527 : Nat := 4983230072969 + 3 ^ 40 * 6973527 * 2
def baseEnd_6973527 : Nat := 3580771208106242777241839

theorem tailTrace_6973527 : CollatzResearch.WordTrace tailWord_6973527 prefixEnd_6973527 3580771208106242777241839 := by
  unfold tailWord_6973527
  simp only [CollatzResearch.WordTrace]
  refine ⟨254345425007110137437662835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169563616671406758291775223 254345425007110137437662835)
  ·
    refine ⟨381518137510665206156494253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254345425007110137437662835 381518137510665206156494253)
    ·
      refine ⟨143069301566499452308685345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 381518137510665206156494253 143069301566499452308685345)
      ·
        refine ⟨107301976174874589231514009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143069301566499452308685345 107301976174874589231514009)
        ·
          refine ⟨80476482131155941923635507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107301976174874589231514009 80476482131155941923635507)
          ·
            refine ⟨120714723196733912885453261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80476482131155941923635507 120714723196733912885453261)
            ·
              refine ⟨45268021198775217332044973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 120714723196733912885453261 45268021198775217332044973)
              ·
                refine ⟨16975507949540706499516865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45268021198775217332044973 16975507949540706499516865)
                ·
                  refine ⟨12731630962155529874637649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16975507949540706499516865 12731630962155529874637649)
                  ·
                    refine ⟨9548723221616647405978237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12731630962155529874637649 9548723221616647405978237)
                    ·
                      refine ⟨3580771208106242777241839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9548723221616647405978237 3580771208106242777241839)
                      ·
                        rfl

theorem cell23_6973527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 3, 2, 2, 3].length) (baseStart_6973527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6973527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6973527 prefixEnd_6973527 := by exact prefixLift 6973527
  have htrace : WordTrace (prefixWord ++ tailWord_6973527) baseStart_6973527 baseEnd_6973527 := by
    simpa [prefixWord, tailWord_6973527, baseEnd_6973527] using wordTrace_append hprefix tailTrace_6973527
  have hstable : (prefixWord ++ tailWord_6973527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6973527).length < 2 ^ (prefixWord ++ tailWord_6973527).sum := by decide
  have hdescent : baseEnd_6973527 < baseStart_6973527 := by decide
  rcases family_descends (prefixWord ++ tailWord_6973527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6973551 : List Nat := [1, 1, 2, 1, 3, 4, 4, 2, 1, 4]
def baseStart_6973551 : Nat := 118140960795 + 6973551 * 2 ^ 59
def prefixEnd_6973551 : Nat := 4983230072969 + 3 ^ 40 * 6973551 * 2
def baseEnd_6973551 : Nat := 1193594510547316894447243

theorem tailTrace_6973551 : CollatzResearch.WordTrace tailWord_6973551 prefixEnd_6973551 1193594510547316894447243 := by
  unfold tailWord_6973551
  simp only [CollatzResearch.WordTrace]
  refine ⟨254346300359023189536536507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169564200239348793024357671 254346300359023189536536507)
  ·
    refine ⟨381519450538534784304804761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254346300359023189536536507 381519450538534784304804761)
    ·
      refine ⟨286139587903901088228603571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 381519450538534784304804761 286139587903901088228603571)
      ·
        refine ⟨429209381855851632342905357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286139587903901088228603571 429209381855851632342905357)
        ·
          refine ⟨160953518195944362128589509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 429209381855851632342905357 160953518195944362128589509)
          ·
            refine ⟨30178784661739567899110533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 160953518195944362128589509 30178784661739567899110533)
            ·
              refine ⟨5658522124076168981083225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30178784661739567899110533 5658522124076168981083225)
              ·
                refine ⟨4243891593057126735812419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5658522124076168981083225 4243891593057126735812419)
                ·
                  refine ⟨6365837389585690103718629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4243891593057126735812419 6365837389585690103718629)
                  ·
                    refine ⟨1193594510547316894447243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6365837389585690103718629 1193594510547316894447243)
                    ·
                      rfl

theorem cell23_6973551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 4, 2, 1, 4].length) (baseStart_6973551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6973551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6973551 prefixEnd_6973551 := by exact prefixLift 6973551
  have htrace : WordTrace (prefixWord ++ tailWord_6973551) baseStart_6973551 baseEnd_6973551 := by
    simpa [prefixWord, tailWord_6973551, baseEnd_6973551] using wordTrace_append hprefix tailTrace_6973551
  have hstable : (prefixWord ++ tailWord_6973551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6973551).length < 2 ^ (prefixWord ++ tailWord_6973551).sum := by decide
  have hdescent : baseEnd_6973551 < baseStart_6973551 := by decide
  rcases family_descends (prefixWord ++ tailWord_6973551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6973577 : List Nat := [1, 2, 1, 1, 4, 2, 2, 4, 1, 5]
def baseStart_6973577 : Nat := 118140960795 + 6973577 * 2 ^ 59
def prefixEnd_6973577 : Nat := 4983230072969 + 3 ^ 40 * 6973577 * 2
def baseEnd_6973577 : Nat := 1193598960712989193872203

theorem tailTrace_6973577 : CollatzResearch.WordTrace tailWord_6973577 prefixEnd_6973577 1193598960712989193872203 := by
  unfold tailWord_6973577
  simp only [CollatzResearch.WordTrace]
  refine ⟨254347248656928995976982985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169564832437952663984655323 254347248656928995976982985)
  ·
    refine ⟨190760436492696746982737239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254347248656928995976982985 190760436492696746982737239)
    ·
      refine ⟨286140654739045120474105859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190760436492696746982737239 286140654739045120474105859)
      ·
        refine ⟨429210982108567680711158789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286140654739045120474105859 429210982108567680711158789)
        ·
          refine ⟨80477059145356440133342273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 429210982108567680711158789 80477059145356440133342273)
          ·
            refine ⟨60357794359017330100006705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80477059145356440133342273 60357794359017330100006705)
            ·
              refine ⟨45268345769262997575005029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60357794359017330100006705 45268345769262997575005029)
              ·
                refine ⟨8487814831736812045313443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45268345769262997575005029 8487814831736812045313443)
                ·
                  refine ⟨12731722247605218067970165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8487814831736812045313443 12731722247605218067970165)
                  ·
                    refine ⟨1193598960712989193872203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12731722247605218067970165 1193598960712989193872203)
                    ·
                      rfl

theorem cell23_6973577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 4, 1, 5].length) (baseStart_6973577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6973577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6973577 prefixEnd_6973577 := by exact prefixLift 6973577
  have htrace : WordTrace (prefixWord ++ tailWord_6973577) baseStart_6973577 baseEnd_6973577 := by
    simpa [prefixWord, tailWord_6973577, baseEnd_6973577] using wordTrace_append hprefix tailTrace_6973577
  have hstable : (prefixWord ++ tailWord_6973577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6973577).length < 2 ^ (prefixWord ++ tailWord_6973577).sum := by decide
  have hdescent : baseEnd_6973577 < baseStart_6973577 := by decide
  rcases family_descends (prefixWord ++ tailWord_6973577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6973598 : List Nat := [4, 3, 1, 1, 4, 1, 1, 2, 6]
def baseStart_6973598 : Nat := 118140960795 + 6973598 * 2 ^ 59
def prefixEnd_6973598 : Nat := 4983230072969 + 3 ^ 40 * 6973598 * 2
def baseEnd_6973598 : Nat := 397867518359190222161557

theorem tailTrace_6973598 : CollatzResearch.WordTrace tailWord_6973598 prefixEnd_6973598 397867518359190222161557 := by
  unfold tailWord_6973598
  simp only [CollatzResearch.WordTrace]
  refine ⟨31793501823731614570437181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 169565343059901944375664965 31793501823731614570437181)
  ·
    refine ⟨11922563183899355463913943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31793501823731614570437181 11922563183899355463913943)
    ·
      refine ⟨17883844775849033195870915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11922563183899355463913943 17883844775849033195870915)
      ·
        refine ⟨26825767163773549793806373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17883844775849033195870915 26825767163773549793806373)
        ·
          refine ⟨5029831343207540586338695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26825767163773549793806373 5029831343207540586338695)
          ·
            refine ⟨7544747014811310879508043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5029831343207540586338695 7544747014811310879508043)
            ·
              refine ⟨11317120522216966319262065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7544747014811310879508043 11317120522216966319262065)
              ·
                refine ⟨8487840391662724739446549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11317120522216966319262065 8487840391662724739446549)
                ·
                  refine ⟨397867518359190222161557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8487840391662724739446549 397867518359190222161557)
                  ·
                    rfl

theorem cell23_6973598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 1, 2, 6].length) (baseStart_6973598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6973598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6973598 prefixEnd_6973598 := by exact prefixLift 6973598
  have htrace : WordTrace (prefixWord ++ tailWord_6973598) baseStart_6973598 baseEnd_6973598 := by
    simpa [prefixWord, tailWord_6973598, baseEnd_6973598] using wordTrace_append hprefix tailTrace_6973598
  have hstable : (prefixWord ++ tailWord_6973598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6973598).length < 2 ^ (prefixWord ++ tailWord_6973598).sum := by decide
  have hdescent : baseEnd_6973598 < baseStart_6973598 := by decide
  rcases family_descends (prefixWord ++ tailWord_6973598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6973637 : List Nat := [1, 3, 1, 1, 1, 1, 8, 7]
def baseStart_6973637 : Nat := 118140960795 + 6973637 * 2 ^ 59
def prefixEnd_6973637 : Nat := 4983230072969 + 3 ^ 40 * 6973637 * 2
def baseEnd_6973637 : Nat := 132623247814008790624679

theorem tailTrace_6973637 : CollatzResearch.WordTrace tailWord_6973637 prefixEnd_6973637 132623247814008790624679 := by
  unfold tailWord_6973637
  simp only [CollatzResearch.WordTrace]
  refine ⟨254349437036711626224167165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169566291357807750816111443 254349437036711626224167165)
  ·
    refine ⟨95381038888766859834062687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 254349437036711626224167165 95381038888766859834062687)
    ·
      refine ⟨143071558333150289751094031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95381038888766859834062687 143071558333150289751094031)
      ·
        refine ⟨214607337499725434626641047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143071558333150289751094031 214607337499725434626641047)
        ·
          refine ⟨321911006249588151939961571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214607337499725434626641047 321911006249588151939961571)
          ·
            refine ⟨482866509374382227909942357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 321911006249588151939961571 482866509374382227909942357)
            ·
              refine ⟨5658591906731041733319637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 482866509374382227909942357 5658591906731041733319637)
              ·
                refine ⟨132623247814008790624679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5658591906731041733319637 132623247814008790624679)
                ·
                  rfl

theorem cell23_6973637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 8, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 8, 7].length) (baseStart_6973637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6973637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6973637 prefixEnd_6973637 := by exact prefixLift 6973637
  have htrace : WordTrace (prefixWord ++ tailWord_6973637) baseStart_6973637 baseEnd_6973637 := by
    simpa [prefixWord, tailWord_6973637, baseEnd_6973637] using wordTrace_append hprefix tailTrace_6973637
  have hstable : (prefixWord ++ tailWord_6973637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6973637).length < 2 ^ (prefixWord ++ tailWord_6973637).sum := by decide
  have hdescent : baseEnd_6973637 < baseStart_6973637 := by decide
  rcases family_descends (prefixWord ++ tailWord_6973637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6973647 : List Nat := [1, 1, 2, 1, 1, 3, 4, 1, 3, 3, 3]
def baseStart_6973647 : Nat := 118140960795 + 6973647 * 2 ^ 59
def prefixEnd_6973647 : Nat := 4983230072969 + 3 ^ 40 * 6973647 * 2
def baseEnd_6973647 : Nat := 3580832825784782307741287

theorem tailTrace_6973647 : CollatzResearch.WordTrace tailWord_6973647 prefixEnd_6973647 3580832825784782307741287 := by
  unfold tailWord_6973647
  simp only [CollatzResearch.WordTrace]
  refine ⟨254349801766675397932031195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169566534511116931954687463 254349801766675397932031195)
  ·
    refine ⟨381524702650013096898046793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254349801766675397932031195 381524702650013096898046793)
    ·
      refine ⟨286143526987509822673535095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 381524702650013096898046793 286143526987509822673535095)
      ·
        refine ⟨429215290481264734010302643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286143526987509822673535095 429215290481264734010302643)
        ·
          refine ⟨643822935721897101015453965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 429215290481264734010302643 643822935721897101015453965)
          ·
            refine ⟨241433600895711412880795237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 643822935721897101015453965 241433600895711412880795237)
            ·
              refine ⟨45268800167945889915149107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 241433600895711412880795237 45268800167945889915149107)
              ·
                refine ⟨67903200251918834872723661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45268800167945889915149107 67903200251918834872723661)
                ·
                  refine ⟨25463700094469563077271373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67903200251918834872723661 25463700094469563077271373)
                  ·
                    refine ⟨9548887535426086153976765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25463700094469563077271373 9548887535426086153976765)
                    ·
                      refine ⟨3580832825784782307741287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9548887535426086153976765 3580832825784782307741287)
                      ·
                        rfl

theorem cell23_6973647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 1, 3, 3, 3].length) (baseStart_6973647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6973647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6973647 prefixEnd_6973647 := by exact prefixLift 6973647
  have htrace : WordTrace (prefixWord ++ tailWord_6973647) baseStart_6973647 baseEnd_6973647 := by
    simpa [prefixWord, tailWord_6973647, baseEnd_6973647] using wordTrace_append hprefix tailTrace_6973647
  have hstable : (prefixWord ++ tailWord_6973647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6973647).length < 2 ^ (prefixWord ++ tailWord_6973647).sum := by decide
  have hdescent : baseEnd_6973647 < baseStart_6973647 := by decide
  rcases family_descends (prefixWord ++ tailWord_6973647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6973654 : List Nat := [5, 2, 1, 2, 1, 1, 11]
def baseStart_6973654 : Nat := 118140960795 + 6973654 * 2 ^ 59
def prefixEnd_6973654 : Nat := 4983230072969 + 3 ^ 40 * 6973654 * 2
def baseEnd_6973654 : Nat := 44207857038881034325355

theorem tailTrace_6973654 : CollatzResearch.WordTrace tailWord_6973654 prefixEnd_6973654 44207857038881034325355 := by
  unfold tailWord_6973654
  simp only [CollatzResearch.WordTrace]
  refine ⟨15896878567353127382971001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 169566704718433358751690677 15896878567353127382971001)
  ·
    refine ⟨11922658925514845537228251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15896878567353127382971001 11922658925514845537228251)
    ·
      refine ⟨17883988388272268305842377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11922658925514845537228251 17883988388272268305842377)
      ·
        refine ⟨13412991291204201229381783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17883988388272268305842377 13412991291204201229381783)
        ·
          refine ⟨20119486936806301844072675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13412991291204201229381783 20119486936806301844072675)
          ·
            refine ⟨30179230405209452766109013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20119486936806301844072675 30179230405209452766109013)
            ·
              refine ⟨44207857038881034325355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 30179230405209452766109013 44207857038881034325355)
              ·
                rfl

theorem cell23_6973654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 11].length) (baseStart_6973654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6973654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6973654 prefixEnd_6973654 := by exact prefixLift 6973654
  have htrace : WordTrace (prefixWord ++ tailWord_6973654) baseStart_6973654 baseEnd_6973654 := by
    simpa [prefixWord, tailWord_6973654, baseEnd_6973654] using wordTrace_append hprefix tailTrace_6973654
  have hstable : (prefixWord ++ tailWord_6973654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6973654).length < 2 ^ (prefixWord ++ tailWord_6973654).sum := by decide
  have hdescent : baseEnd_6973654 < baseStart_6973654 := by decide
  rcases family_descends (prefixWord ++ tailWord_6973654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6973664 : List Nat := [2, 1, 1, 3, 1, 3, 1, 3, 4, 1, 3]
def baseStart_6973664 : Nat := 118140960795 + 6973664 * 2 ^ 59
def prefixEnd_6973664 : Nat := 4983230072969 + 3 ^ 40 * 6973664 * 2
def baseEnd_6973664 : Nat := 3580841554955908741228709

theorem tailTrace_6973664 : CollatzResearch.WordTrace tailWord_6973664 prefixEnd_6973664 3580841554955908741228709 := by
  unfold tailWord_6973664
  simp only [CollatzResearch.WordTrace]
  refine ⟨127175210903806904917700023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169566947871742539890266697 127175210903806904917700023)
  ·
    refine ⟨190762816355710357376550035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127175210903806904917700023 190762816355710357376550035)
    ·
      refine ⟨286144224533565536064825053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190762816355710357376550035 286144224533565536064825053)
      ·
        refine ⟨107304084200087076024309395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 286144224533565536064825053 107304084200087076024309395)
        ·
          refine ⟨160956126300130614036464093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107304084200087076024309395 160956126300130614036464093)
          ·
            refine ⟨60358547362548980263674035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 160956126300130614036464093 60358547362548980263674035)
            ·
              refine ⟨90537821043823470395511053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60358547362548980263674035 90537821043823470395511053)
              ·
                refine ⟨33951682891433801398316645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90537821043823470395511053 33951682891433801398316645)
                ·
                  refine ⟨6365940542143837762184371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33951682891433801398316645 6365940542143837762184371)
                  ·
                    refine ⟨9548910813215756643276557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6365940542143837762184371 9548910813215756643276557)
                    ·
                      refine ⟨3580841554955908741228709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9548910813215756643276557 3580841554955908741228709)
                      ·
                        rfl

theorem cell23_6973664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 3, 4, 1, 3].length) (baseStart_6973664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6973664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6973664 prefixEnd_6973664 := by exact prefixLift 6973664
  have htrace : WordTrace (prefixWord ++ tailWord_6973664) baseStart_6973664 baseEnd_6973664 := by
    simpa [prefixWord, tailWord_6973664, baseEnd_6973664] using wordTrace_append hprefix tailTrace_6973664
  have hstable : (prefixWord ++ tailWord_6973664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6973664).length < 2 ^ (prefixWord ++ tailWord_6973664).sum := by decide
  have hdescent : baseEnd_6973664 < baseStart_6973664 := by decide
  rcases family_descends (prefixWord ++ tailWord_6973664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6973665 : List Nat := [1, 2, 3, 1, 3, 1, 5, 2, 1, 2, 2]
def baseStart_6973665 : Nat := 118140960795 + 6973665 * 2 ^ 59
def prefixEnd_6973665 : Nat := 4983230072969 + 3 ^ 40 * 6973665 * 2
def baseEnd_6973665 : Nat := 3580842068436563237316205

theorem tailTrace_6973665 : CollatzResearch.WordTrace tailWord_6973665 prefixEnd_6973665 3580842068436563237316205 := by
  unfold tailWord_6973665
  simp only [CollatzResearch.WordTrace]
  refine ⟨254350458280610187006186449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169566972187073458004124299 254350458280610187006186449)
  ·
    refine ⟨190762843710457640254639837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254350458280610187006186449 190762843710457640254639837)
    ·
      refine ⟨71536066391421615095489939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 190762843710457640254639837 71536066391421615095489939)
      ·
        refine ⟨107304099587132422643234909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71536066391421615095489939 107304099587132422643234909)
        ·
          refine ⟨40239037345174658491213091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107304099587132422643234909 40239037345174658491213091)
          ·
            refine ⟨60358556017761987736819637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40239037345174658491213091 60358556017761987736819637)
            ·
              refine ⟨5658614626665186350326841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 60358556017761987736819637 5658614626665186350326841)
              ·
                refine ⟨4243960969998889762745131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5658614626665186350326841 4243960969998889762745131)
                ·
                  refine ⟨6365941454998334644117697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4243960969998889762745131 6365941454998334644117697)
                  ·
                    refine ⟨4774456091248750983088273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6365941454998334644117697 4774456091248750983088273)
                    ·
                      refine ⟨3580842068436563237316205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4774456091248750983088273 3580842068436563237316205)
                      ·
                        rfl

theorem cell23_6973665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 5, 2, 1, 2, 2].length) (baseStart_6973665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6973665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6973665 prefixEnd_6973665 := by exact prefixLift 6973665
  have htrace : WordTrace (prefixWord ++ tailWord_6973665) baseStart_6973665 baseEnd_6973665 := by
    simpa [prefixWord, tailWord_6973665, baseEnd_6973665] using wordTrace_append hprefix tailTrace_6973665
  have hstable : (prefixWord ++ tailWord_6973665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6973665).length < 2 ^ (prefixWord ++ tailWord_6973665).sum := by decide
  have hdescent : baseEnd_6973665 < baseStart_6973665 := by decide
  rcases family_descends (prefixWord ++ tailWord_6973665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6973707 : List Nat := [1, 1, 1, 1, 5, 2, 1, 3, 2, 1, 5]
def baseStart_6973707 : Nat := 118140960795 + 6973707 * 2 ^ 59
def prefixEnd_6973707 : Nat := 4983230072969 + 3 ^ 40 * 6973707 * 2
def baseEnd_6973707 : Nat := 3580863634624052072991011

theorem tailTrace_6973707 : CollatzResearch.WordTrace tailWord_6973707 prefixEnd_6973707 3580863634624052072991011 := by
  unfold tailWord_6973707
  simp only [CollatzResearch.WordTrace]
  refine ⟨254351990146458028179215375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169567993430972018786143583 254351990146458028179215375)
  ·
    refine ⟨381527985219687042268823063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254351990146458028179215375 381527985219687042268823063)
    ·
      refine ⟨572291977829530563403234595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 381527985219687042268823063 572291977829530563403234595)
      ·
        refine ⟨858437966744295845104851893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 572291977829530563403234595 858437966744295845104851893)
        ·
          refine ⟨80478559382277735478579865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 858437966744295845104851893 80478559382277735478579865)
          ·
            refine ⟨60358919536708301608934899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80478559382277735478579865 60358919536708301608934899)
            ·
              refine ⟨90538379305062452413402349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60358919536708301608934899 90538379305062452413402349)
              ·
                refine ⟨33951892239398419655025881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90538379305062452413402349 33951892239398419655025881)
                ·
                  refine ⟨25463919179548814741269411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33951892239398419655025881 25463919179548814741269411)
                  ·
                    refine ⟨38195878769323222111904117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25463919179548814741269411 38195878769323222111904117)
                    ·
                      refine ⟨3580863634624052072991011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38195878769323222111904117 3580863634624052072991011)
                      ·
                        rfl

theorem cell23_6973707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 3, 2, 1, 5].length) (baseStart_6973707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6973707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6973707 prefixEnd_6973707 := by exact prefixLift 6973707
  have htrace : WordTrace (prefixWord ++ tailWord_6973707) baseStart_6973707 baseEnd_6973707 := by
    simpa [prefixWord, tailWord_6973707, baseEnd_6973707] using wordTrace_append hprefix tailTrace_6973707
  have hstable : (prefixWord ++ tailWord_6973707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6973707).length < 2 ^ (prefixWord ++ tailWord_6973707).sum := by decide
  have hdescent : baseEnd_6973707 < baseStart_6973707 := by decide
  rcases family_descends (prefixWord ++ tailWord_6973707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6973708 : List Nat := [2, 2, 1, 2, 2, 2, 5, 1, 1, 3, 2]
def baseStart_6973708 : Nat := 118140960795 + 6973708 * 2 ^ 59
def prefixEnd_6973708 : Nat := 4983230072969 + 3 ^ 40 * 6973708 * 2
def baseEnd_6973708 : Nat := 3580864148104706569078507

theorem tailTrace_6973708 : CollatzResearch.WordTrace tailWord_6973708 prefixEnd_6973708 3580864148104706569078507 := by
  unfold tailWord_6973708
  simp only [CollatzResearch.WordTrace]
  refine ⟨127176013309727202675000889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169568017746302936900001185 127176013309727202675000889)
  ·
    refine ⟨95382009982295402006250667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127176013309727202675000889 95382009982295402006250667)
    ·
      refine ⟨143073014973443103009376001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95382009982295402006250667 143073014973443103009376001)
      ·
        refine ⟨107304761230082327257032001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143073014973443103009376001 107304761230082327257032001)
        ·
          refine ⟨80478570922561745442774001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107304761230082327257032001 80478570922561745442774001)
          ·
            refine ⟨60358928191921309082080501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80478570922561745442774001 60358928191921309082080501)
            ·
              refine ⟨5658649517992622726445047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 60358928191921309082080501 5658649517992622726445047)
              ·
                refine ⟨8487974276988934089667571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5658649517992622726445047 8487974276988934089667571)
                ·
                  refine ⟨12731961415483401134501357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8487974276988934089667571 12731961415483401134501357)
                  ·
                    refine ⟨4774485530806275425438009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12731961415483401134501357 4774485530806275425438009)
                    ·
                      refine ⟨3580864148104706569078507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4774485530806275425438009 3580864148104706569078507)
                      ·
                        rfl

theorem cell23_6973708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 5, 1, 1, 3, 2].length) (baseStart_6973708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6973708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6973708 prefixEnd_6973708 := by exact prefixLift 6973708
  have htrace : WordTrace (prefixWord ++ tailWord_6973708) baseStart_6973708 baseEnd_6973708 := by
    simpa [prefixWord, tailWord_6973708, baseEnd_6973708] using wordTrace_append hprefix tailTrace_6973708
  have hstable : (prefixWord ++ tailWord_6973708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6973708).length < 2 ^ (prefixWord ++ tailWord_6973708).sum := by decide
  have hdescent : baseEnd_6973708 < baseStart_6973708 := by decide
  rcases family_descends (prefixWord ++ tailWord_6973708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6973807 : List Nat := [1, 1, 2, 1, 3, 1, 2, 2, 1, 3, 6]
def baseStart_6973807 : Nat := 118140960795 + 6973807 * 2 ^ 59
def prefixEnd_6973807 : Nat := 4983230072969 + 3 ^ 40 * 6973807 * 2
def baseEnd_6973807 : Nat := 3580914982689501681740551

theorem tailTrace_6973807 : CollatzResearch.WordTrace tailWord_6973807 prefixEnd_6973807 3580914982689501681740551 := by
  unfold tailWord_6973807
  simp only [CollatzResearch.WordTrace]
  refine ⟨254355637446095745257855675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169570424964063830171903783 254355637446095745257855675)
  ·
    refine ⟨381533456169143617886783513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254355637446095745257855675 381533456169143617886783513)
    ·
      refine ⟨286150092126857713415087635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 381533456169143617886783513 286150092126857713415087635)
      ·
        refine ⟨429225138190286570122631453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286150092126857713415087635 429225138190286570122631453)
        ·
          refine ⟨160959426821357463795986795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 429225138190286570122631453 160959426821357463795986795)
          ·
            refine ⟨241439140232036195693980193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160959426821357463795986795 241439140232036195693980193)
            ·
              refine ⟨181079355174027146770485145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 241439140232036195693980193 181079355174027146770485145)
              ·
                refine ⟨135809516380520360077863859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 181079355174027146770485145 135809516380520360077863859)
                ·
                  refine ⟨203714274570780540116795789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 135809516380520360077863859 203714274570780540116795789)
                  ·
                    refine ⟨76392852964042702543798421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 203714274570780540116795789 76392852964042702543798421)
                    ·
                      refine ⟨3580914982689501681740551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76392852964042702543798421 3580914982689501681740551)
                      ·
                        rfl

theorem cell23_6973807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 2, 1, 3, 6].length) (baseStart_6973807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6973807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6973807 prefixEnd_6973807 := by exact prefixLift 6973807
  have htrace : WordTrace (prefixWord ++ tailWord_6973807) baseStart_6973807 baseEnd_6973807 := by
    simpa [prefixWord, tailWord_6973807, baseEnd_6973807] using wordTrace_append hprefix tailTrace_6973807
  have hstable : (prefixWord ++ tailWord_6973807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6973807).length < 2 ^ (prefixWord ++ tailWord_6973807).sum := by decide
  have hdescent : baseEnd_6973807 < baseStart_6973807 := by decide
  rcases family_descends (prefixWord ++ tailWord_6973807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6973831 : List Nat := [1, 1, 4, 2, 2, 1, 3, 2, 2, 2, 3]
def baseStart_6973831 : Nat := 118140960795 + 6973831 * 2 ^ 59
def prefixEnd_6973831 : Nat := 4983230072969 + 3 ^ 40 * 6973831 * 2
def baseEnd_6973831 : Nat := 3580927306225209587840441

theorem tailTrace_6973831 : CollatzResearch.WordTrace tailWord_6973831 prefixEnd_6973831 3580927306225209587840441 := by
  unfold tailWord_6973831
  simp only [CollatzResearch.WordTrace]
  refine ⟨254356512798008797356729347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169571008532005864904486231 254356512798008797356729347)
  ·
    refine ⟨381534769197013196035094021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254356512798008797356729347 381534769197013196035094021)
    ·
      refine ⟨71537769224439974256580129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 381534769197013196035094021 71537769224439974256580129)
      ·
        refine ⟨53653326918329980692435097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71537769224439974256580129 53653326918329980692435097)
        ·
          refine ⟨40239995188747485519326323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53653326918329980692435097 40239995188747485519326323)
          ·
            refine ⟨60359992783121228278989485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40239995188747485519326323 60359992783121228278989485)
            ·
              refine ⟨22634997293670460604621057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60359992783121228278989485 22634997293670460604621057)
              ·
                refine ⟨16976247970252845453465793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22634997293670460604621057 16976247970252845453465793)
                ·
                  refine ⟨12732185977689634090099345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16976247970252845453465793 12732185977689634090099345)
                  ·
                    refine ⟨9549139483267225567574509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12732185977689634090099345 9549139483267225567574509)
                    ·
                      refine ⟨3580927306225209587840441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9549139483267225567574509 3580927306225209587840441)
                      ·
                        rfl

theorem cell23_6973831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 2, 2, 2, 3].length) (baseStart_6973831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6973831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6973831 prefixEnd_6973831 := by exact prefixLift 6973831
  have htrace : WordTrace (prefixWord ++ tailWord_6973831) baseStart_6973831 baseEnd_6973831 := by
    simpa [prefixWord, tailWord_6973831, baseEnd_6973831] using wordTrace_append hprefix tailTrace_6973831
  have hstable : (prefixWord ++ tailWord_6973831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6973831).length < 2 ^ (prefixWord ++ tailWord_6973831).sum := by decide
  have hdescent : baseEnd_6973831 < baseStart_6973831 := by decide
  rcases family_descends (prefixWord ++ tailWord_6973831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6973838 : List Nat := [4, 1, 1, 4, 1, 1, 3, 1, 3, 4]
def baseStart_6973838 : Nat := 118140960795 + 6973838 * 2 ^ 59
def prefixEnd_6973838 : Nat := 4983230072969 + 3 ^ 40 * 6973838 * 2
def baseEnd_6973838 : Nat := 1193643633529930353484303

theorem tailTrace_6973838 : CollatzResearch.WordTrace tailWord_6973838 prefixEnd_6973838 1193643633529930353484303 := by
  unfold tailWord_6973838
  simp only [CollatzResearch.WordTrace]
  refine ⟨31794596013622929694029271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 169571178739322291701489445 31794596013622929694029271)
  ·
    refine ⟨47691894020434394541043907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31794596013622929694029271 47691894020434394541043907)
    ·
      refine ⟨71537841030651591811565861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47691894020434394541043907 71537841030651591811565861)
      ·
        refine ⟨13413345193247173464668599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71537841030651591811565861 13413345193247173464668599)
        ·
          refine ⟨20120017789870760197002899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13413345193247173464668599 20120017789870760197002899)
          ·
            refine ⟨30180026684806140295504349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20120017789870760197002899 30180026684806140295504349)
            ·
              refine ⟨11317510006802302610814131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30180026684806140295504349 11317510006802302610814131)
              ·
                refine ⟨16976265010203453916221197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11317510006802302610814131 16976265010203453916221197)
                ·
                  refine ⟨6366099378826295218582949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16976265010203453916221197 6366099378826295218582949)
                  ·
                    refine ⟨1193643633529930353484303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6366099378826295218582949 1193643633529930353484303)
                    ·
                      rfl

theorem cell23_6973838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 3, 1, 3, 4].length) (baseStart_6973838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6973838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6973838 prefixEnd_6973838 := by exact prefixLift 6973838
  have htrace : WordTrace (prefixWord ++ tailWord_6973838) baseStart_6973838 baseEnd_6973838 := by
    simpa [prefixWord, tailWord_6973838, baseEnd_6973838] using wordTrace_append hprefix tailTrace_6973838
  have hstable : (prefixWord ++ tailWord_6973838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6973838).length < 2 ^ (prefixWord ++ tailWord_6973838).sum := by decide
  have hdescent : baseEnd_6973838 < baseStart_6973838 := by decide
  rcases family_descends (prefixWord ++ tailWord_6973838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6973861 : List Nat := [1, 3, 1, 2, 1, 1, 4, 1, 5, 1, 3]
def baseStart_6973861 : Nat := 118140960795 + 6973861 * 2 ^ 59
def prefixEnd_6973861 : Nat := 4983230072969 + 3 ^ 40 * 6973861 * 2
def baseEnd_6973861 : Nat := 3580942710644844470465303

theorem tailTrace_6973861 : CollatzResearch.WordTrace tailWord_6973861 prefixEnd_6973861 3580942710644844470465303 := by
  unfold tailWord_6973861
  simp only [CollatzResearch.WordTrace]
  refine ⟨254357606987900112480321437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169571737991933408320214291 254357606987900112480321437)
  ·
    refine ⟨95384102620462542180120539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 254357606987900112480321437 95384102620462542180120539)
    ·
      refine ⟨143076153930693813270180809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95384102620462542180120539 143076153930693813270180809)
      ·
        refine ⟨107307115448020359952635607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143076153930693813270180809 107307115448020359952635607)
        ·
          refine ⟨160960673172030539928953411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107307115448020359952635607 160960673172030539928953411)
          ·
            refine ⟨241441009758045809893430117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160960673172030539928953411 241441009758045809893430117)
            ·
              refine ⟨45270189329633589355018147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 241441009758045809893430117 45270189329633589355018147)
              ·
                refine ⟨67905283994450384032527221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45270189329633589355018147 67905283994450384032527221)
                ·
                  refine ⟨6366120374479723503049427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 67905283994450384032527221 6366120374479723503049427)
                  ·
                    refine ⟨9549180561719585254574141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6366120374479723503049427 9549180561719585254574141)
                    ·
                      refine ⟨3580942710644844470465303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9549180561719585254574141 3580942710644844470465303)
                      ·
                        rfl

theorem cell23_6973861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 1, 5, 1, 3].length) (baseStart_6973861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6973861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6973861 prefixEnd_6973861 := by exact prefixLift 6973861
  have htrace : WordTrace (prefixWord ++ tailWord_6973861) baseStart_6973861 baseEnd_6973861 := by
    simpa [prefixWord, tailWord_6973861, baseEnd_6973861] using wordTrace_append hprefix tailTrace_6973861
  have hstable : (prefixWord ++ tailWord_6973861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6973861).length < 2 ^ (prefixWord ++ tailWord_6973861).sum := by decide
  have hdescent : baseEnd_6973861 < baseStart_6973861 := by decide
  rcases family_descends (prefixWord ++ tailWord_6973861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6973889 : List Nat := [1, 2, 7, 1, 1, 1, 1, 4, 1, 4]
def baseStart_6973889 : Nat := 118140960795 + 6973889 * 2 ^ 59
def prefixEnd_6973889 : Nat := 4983230072969 + 3 ^ 40 * 6973889 * 2
def baseEnd_6973889 : Nat := 1193652362701056786971725

theorem tailTrace_6973889 : CollatzResearch.WordTrace tailWord_6973889 prefixEnd_6973889 1193652362701056786971725 := by
  unfold tailWord_6973889
  simp only [CollatzResearch.WordTrace]
  refine ⟨254358628231798673262340721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169572418821199115508227147 254358628231798673262340721)
  ·
    refine ⟨190768971173849004946755541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254358628231798673262340721 190768971173849004946755541)
    ·
      refine ⟨4471147761887086053439583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 190768971173849004946755541 4471147761887086053439583)
      ·
        refine ⟨6706721642830629080159375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4471147761887086053439583 6706721642830629080159375)
        ·
          refine ⟨10060082464245943620239063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6706721642830629080159375 10060082464245943620239063)
          ·
            refine ⟨15090123696368915430358595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10060082464245943620239063 15090123696368915430358595)
            ·
              refine ⟨22635185544553373145537893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15090123696368915430358595 22635185544553373145537893)
              ·
                refine ⟨4244097289603757464788355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22635185544553373145537893 4244097289603757464788355)
                ·
                  refine ⟨6366145934405636197182533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4244097289603757464788355 6366145934405636197182533)
                  ·
                    refine ⟨1193652362701056786971725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6366145934405636197182533 1193652362701056786971725)
                    ·
                      rfl

theorem cell23_6973889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_6973889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6973889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6973889 prefixEnd_6973889 := by exact prefixLift 6973889
  have htrace : WordTrace (prefixWord ++ tailWord_6973889) baseStart_6973889 baseEnd_6973889 := by
    simpa [prefixWord, tailWord_6973889, baseEnd_6973889] using wordTrace_append hprefix tailTrace_6973889
  have hstable : (prefixWord ++ tailWord_6973889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6973889).length < 2 ^ (prefixWord ++ tailWord_6973889).sum := by decide
  have hdescent : baseEnd_6973889 < baseStart_6973889 := by decide
  rcases family_descends (prefixWord ++ tailWord_6973889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6973895 : List Nat := [1, 1, 4, 1, 1, 5, 1, 4, 1, 1, 3]
def baseStart_6973895 : Nat := 118140960795 + 6973895 * 2 ^ 59
def prefixEnd_6973895 : Nat := 4983230072969 + 3 ^ 40 * 6973895 * 2
def baseEnd_6973895 : Nat := 3580960168987097337440147

theorem tailTrace_6973895 : CollatzResearch.WordTrace tailWord_6973895 prefixEnd_6973895 3580960168987097337440147 := by
  unfold tailWord_6973895
  simp only [CollatzResearch.WordTrace]
  refine ⟨254358847069776936287059139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169572564713184624191372759 254358847069776936287059139)
  ·
    refine ⟨381538270604665404430588709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254358847069776936287059139 381538270604665404430588709)
    ·
      refine ⟨71538425738374763330735383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 381538270604665404430588709 71538425738374763330735383)
      ·
        refine ⟨107307638607562144996103075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71538425738374763330735383 107307638607562144996103075)
        ·
          refine ⟨160961457911343217494154613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107307638607562144996103075 160961457911343217494154613)
          ·
            refine ⟨15090136679188426640076995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 160961457911343217494154613 15090136679188426640076995)
            ·
              refine ⟨22635205018782639960115493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15090136679188426640076995 22635205018782639960115493)
              ·
                refine ⟨4244100941021744992521655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22635205018782639960115493 4244100941021744992521655)
                ·
                  refine ⟨6366151411532617488782483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4244100941021744992521655 6366151411532617488782483)
                  ·
                    refine ⟨9549227117298926233173725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6366151411532617488782483 9549227117298926233173725)
                    ·
                      refine ⟨3580960168987097337440147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9549227117298926233173725 3580960168987097337440147)
                      ·
                        rfl

theorem cell23_6973895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 4, 1, 1, 3].length) (baseStart_6973895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6973895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6973895 prefixEnd_6973895 := by exact prefixLift 6973895
  have htrace : WordTrace (prefixWord ++ tailWord_6973895) baseStart_6973895 baseEnd_6973895 := by
    simpa [prefixWord, tailWord_6973895, baseEnd_6973895] using wordTrace_append hprefix tailTrace_6973895
  have hstable : (prefixWord ++ tailWord_6973895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6973895).length < 2 ^ (prefixWord ++ tailWord_6973895).sum := by decide
  have hdescent : baseEnd_6973895 < baseStart_6973895 := by decide
  rcases family_descends (prefixWord ++ tailWord_6973895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6973904 : List Nat := [2, 1, 1, 1, 1, 2, 2, 1, 1, 8, 3]
def baseStart_6973904 : Nat := 118140960795 + 6973904 * 2 ^ 59
def prefixEnd_6973904 : Nat := 4983230072969 + 3 ^ 40 * 6973904 * 2
def baseEnd_6973904 : Nat := 3580964790312987802227605

theorem tailTrace_6973904 : CollatzResearch.WordTrace tailWord_6973904 prefixEnd_6973904 3580964790312987802227605 := by
  unfold tailWord_6973904
  simp only [CollatzResearch.WordTrace]
  refine ⟨127179587663372165412068383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169572783551162887216091177 127179587663372165412068383)
  ·
    refine ⟨190769381495058248118102575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127179587663372165412068383 190769381495058248118102575)
    ·
      refine ⟨286154072242587372177153863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190769381495058248118102575 286154072242587372177153863)
      ·
        refine ⟨429231108363881058265730795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286154072242587372177153863 429231108363881058265730795)
        ·
          refine ⟨643846662545821587398596193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 429231108363881058265730795 643846662545821587398596193)
          ·
            refine ⟨482884996909366190548947145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 643846662545821587398596193 482884996909366190548947145)
            ·
              refine ⟨362163747682024642911710359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 482884996909366190548947145 362163747682024642911710359)
              ·
                refine ⟨543245621523036964367565539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 362163747682024642911710359 543245621523036964367565539)
                ·
                  refine ⟨814868432284555446551348309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 543245621523036964367565539 814868432284555446551348309)
                  ·
                    refine ⟨9549239440834634139273613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 814868432284555446551348309 9549239440834634139273613)
                    ·
                      refine ⟨3580964790312987802227605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9549239440834634139273613 3580964790312987802227605)
                      ·
                        rfl

theorem cell23_6973904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 1, 8, 3].length) (baseStart_6973904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6973904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6973904 prefixEnd_6973904 := by exact prefixLift 6973904
  have htrace : WordTrace (prefixWord ++ tailWord_6973904) baseStart_6973904 baseEnd_6973904 := by
    simpa [prefixWord, tailWord_6973904, baseEnd_6973904] using wordTrace_append hprefix tailTrace_6973904
  have hstable : (prefixWord ++ tailWord_6973904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6973904).length < 2 ^ (prefixWord ++ tailWord_6973904).sum := by decide
  have hdescent : baseEnd_6973904 < baseStart_6973904 := by decide
  rcases family_descends (prefixWord ++ tailWord_6973904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6973921 : List Nat := [1, 2, 3, 1, 2, 2, 1, 3, 3, 2, 3]
def baseStart_6973921 : Nat := 118140960795 + 6973921 * 2 ^ 59
def prefixEnd_6973921 : Nat := 4983230072969 + 3 ^ 40 * 6973921 * 2
def baseEnd_6973921 : Nat := 3580973519484114235715027

theorem tailTrace_6973921 : CollatzResearch.WordTrace tailWord_6973921 prefixEnd_6973921 3580973519484114235715027 := by
  unfold tailWord_6973921
  simp only [CollatzResearch.WordTrace]
  refine ⟨254359795367682742727505617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169573196911788495151670411 254359795367682742727505617)
  ·
    refine ⟨190769846525762057045629213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254359795367682742727505617 190769846525762057045629213)
    ·
      refine ⟨71538692447160771392110955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 190769846525762057045629213 71538692447160771392110955)
      ·
        refine ⟨107308038670741157088166433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71538692447160771392110955 107308038670741157088166433)
        ·
          refine ⟨80481029003055867816124825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107308038670741157088166433 80481029003055867816124825)
          ·
            refine ⟨60360771752291900862093619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80481029003055867816124825 60360771752291900862093619)
            ·
              refine ⟨90541157628437851293140429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60360771752291900862093619 90541157628437851293140429)
              ·
                refine ⟨33952934110664194234927661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90541157628437851293140429 33952934110664194234927661)
                ·
                  refine ⟨12732350291499072838097873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33952934110664194234927661 12732350291499072838097873)
                  ·
                    refine ⟨9549262718624304628573405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12732350291499072838097873 9549262718624304628573405)
                    ·
                      refine ⟨3580973519484114235715027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9549262718624304628573405 3580973519484114235715027)
                      ·
                        rfl

theorem cell23_6973921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 3, 3, 2, 3].length) (baseStart_6973921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6973921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6973921 prefixEnd_6973921 := by exact prefixLift 6973921
  have htrace : WordTrace (prefixWord ++ tailWord_6973921) baseStart_6973921 baseEnd_6973921 := by
    simpa [prefixWord, tailWord_6973921, baseEnd_6973921] using wordTrace_append hprefix tailTrace_6973921
  have hstable : (prefixWord ++ tailWord_6973921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6973921).length < 2 ^ (prefixWord ++ tailWord_6973921).sum := by decide
  have hdescent : baseEnd_6973921 < baseStart_6973921 := by decide
  rcases family_descends (prefixWord ++ tailWord_6973921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6973922 : List Nat := [3, 3, 3, 2, 1, 1, 1, 1, 1, 5, 2]
def baseStart_6973922 : Nat := 118140960795 + 6973922 * 2 ^ 59
def prefixEnd_6973922 : Nat := 4983230072969 + 3 ^ 40 * 6973922 * 2
def baseEnd_6973922 : Nat := 3580974032964768731802523

theorem tailTrace_6973922 : CollatzResearch.WordTrace tailWord_6973922 prefixEnd_6973922 3580974032964768731802523 := by
  unfold tailWord_6973922
  simp only [CollatzResearch.WordTrace]
  refine ⟨63589957960169779974573005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169573221227119413265528013 63589957960169779974573005)
  ·
    refine ⟨23846234235063667490464877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63589957960169779974573005 23846234235063667490464877)
    ·
      refine ⟨8942337838148875308924329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23846234235063667490464877 8942337838148875308924329)
      ·
        refine ⟨6706753378611656481693247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8942337838148875308924329 6706753378611656481693247)
        ·
          refine ⟨10060130067917484722539871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6706753378611656481693247 10060130067917484722539871)
          ·
            refine ⟨15090195101876227083809807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10060130067917484722539871 15090195101876227083809807)
            ·
              refine ⟨22635292652814340625714711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15090195101876227083809807 22635292652814340625714711)
              ·
                refine ⟨33952938979221510938572067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22635292652814340625714711 33952938979221510938572067)
                ·
                  refine ⟨50929408468832266407858101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33952938979221510938572067 50929408468832266407858101)
                  ·
                    refine ⟨4774632043953024975736697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50929408468832266407858101 4774632043953024975736697)
                    ·
                      refine ⟨3580974032964768731802523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4774632043953024975736697 3580974032964768731802523)
                      ·
                        rfl

theorem cell23_6973922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_6973922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6973922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6973922 prefixEnd_6973922 := by exact prefixLift 6973922
  have htrace : WordTrace (prefixWord ++ tailWord_6973922) baseStart_6973922 baseEnd_6973922 := by
    simpa [prefixWord, tailWord_6973922, baseEnd_6973922] using wordTrace_append hprefix tailTrace_6973922
  have hstable : (prefixWord ++ tailWord_6973922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6973922).length < 2 ^ (prefixWord ++ tailWord_6973922).sum := by decide
  have hdescent : baseEnd_6973922 < baseStart_6973922 := by decide
  rcases family_descends (prefixWord ++ tailWord_6973922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6973961 : List Nat := [1, 2, 1, 1, 3, 1, 2, 1, 2, 7, 2]
def baseStart_6973961 : Nat := 118140960795 + 6973961 * 2 ^ 59
def prefixEnd_6973961 : Nat := 4983230072969 + 3 ^ 40 * 6973961 * 2
def baseEnd_6973961 : Nat := 3580994058710294079214843

theorem tailTrace_6973961 : CollatzResearch.WordTrace tailWord_6973961 prefixEnd_6973961 3580994058710294079214843 := by
  unfold tailWord_6973961
  simp only [CollatzResearch.WordTrace]
  refine ⟨254361254287537829558961737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169574169525025219705974491 254361254287537829558961737)
  ·
    refine ⟨190770940715653372169221303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254361254287537829558961737 190770940715653372169221303)
    ·
      refine ⟨286156411073480058253831955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190770940715653372169221303 286156411073480058253831955)
      ·
        refine ⟨429234616610220087380747933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286156411073480058253831955 429234616610220087380747933)
        ·
          refine ⟨160962981228832532767780475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 429234616610220087380747933 160962981228832532767780475)
          ·
            refine ⟨241444471843248799151670713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160962981228832532767780475 241444471843248799151670713)
            ·
              refine ⟨181083353882436599363753035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 241444471843248799151670713 181083353882436599363753035)
              ·
                refine ⟨271625030823654899045629553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 181083353882436599363753035 271625030823654899045629553)
                ·
                  refine ⟨203718773117741174284222165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 271625030823654899045629553 203718773117741174284222165)
                  ·
                    refine ⟨4774658744947058772286457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 203718773117741174284222165 4774658744947058772286457)
                    ·
                      refine ⟨3580994058710294079214843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4774658744947058772286457 3580994058710294079214843)
                      ·
                        rfl

theorem cell23_6973961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 7, 2].length) (baseStart_6973961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6973961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6973961 prefixEnd_6973961 := by exact prefixLift 6973961
  have htrace : WordTrace (prefixWord ++ tailWord_6973961) baseStart_6973961 baseEnd_6973961 := by
    simpa [prefixWord, tailWord_6973961, baseEnd_6973961] using wordTrace_append hprefix tailTrace_6973961
  have hstable : (prefixWord ++ tailWord_6973961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6973961).length < 2 ^ (prefixWord ++ tailWord_6973961).sum := by decide
  have hdescent : baseEnd_6973961 < baseStart_6973961 := by decide
  rcases family_descends (prefixWord ++ tailWord_6973961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6973965 : List Nat := [1, 7, 1, 1, 1, 2, 1, 1, 1, 1, 6]
def baseStart_6973965 : Nat := 118140960795 + 6973965 * 2 ^ 59
def prefixEnd_6973965 : Nat := 4983230072969 + 3 ^ 40 * 6973965 * 2
def baseEnd_6973965 : Nat := 3580996112632912063564825

theorem tailTrace_6973965 : CollatzResearch.WordTrace tailWord_6973965 prefixEnd_6973965 3580996112632912063564825 := by
  unfold tailWord_6973965
  simp only [CollatzResearch.WordTrace]
  refine ⟨254361400179523338242107349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169574266786348892161404899 254361400179523338242107349)
  ·
    refine ⟨5961595316707578240049391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 254361400179523338242107349 5961595316707578240049391)
    ·
      refine ⟨8942392975061367360074087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5961595316707578240049391 8942392975061367360074087)
      ·
        refine ⟨13413589462592051040111131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8942392975061367360074087 13413589462592051040111131)
        ·
          refine ⟨20120384193888076560166697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13413589462592051040111131 20120384193888076560166697)
          ·
            refine ⟨15090288145416057420125023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20120384193888076560166697 15090288145416057420125023)
            ·
              refine ⟨22635432218124086130187535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15090288145416057420125023 22635432218124086130187535)
              ·
                refine ⟨33953148327186129195281303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22635432218124086130187535 33953148327186129195281303)
                ·
                  refine ⟨50929722490779193792921955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33953148327186129195281303 50929722490779193792921955)
                  ·
                    refine ⟨76394583736168790689382933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50929722490779193792921955 76394583736168790689382933)
                    ·
                      refine ⟨3580996112632912063564825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76394583736168790689382933 3580996112632912063564825)
                      ·
                        rfl

theorem cell23_6973965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_6973965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6973965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6973965 prefixEnd_6973965 := by exact prefixLift 6973965
  have htrace : WordTrace (prefixWord ++ tailWord_6973965) baseStart_6973965 baseEnd_6973965 := by
    simpa [prefixWord, tailWord_6973965, baseEnd_6973965] using wordTrace_append hprefix tailTrace_6973965
  have hstable : (prefixWord ++ tailWord_6973965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6973965).length < 2 ^ (prefixWord ++ tailWord_6973965).sum := by decide
  have hdescent : baseEnd_6973965 < baseStart_6973965 := by decide
  rcases family_descends (prefixWord ++ tailWord_6973965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6973972 : List Nat := [2, 4, 3, 1, 1, 2, 2, 2, 1, 2, 3]
def baseStart_6973972 : Nat := 118140960795 + 6973972 * 2 ^ 59
def prefixEnd_6973972 : Nat := 4983230072969 + 3 ^ 40 * 6973972 * 2
def baseEnd_6973972 : Nat := 3580999706997493536177293

theorem tailTrace_6973972 : CollatzResearch.WordTrace tailWord_6973972 prefixEnd_6973972 3580999706997493536177293 := by
  unfold tailWord_6973972
  simp only [CollatzResearch.WordTrace]
  refine ⟨127180827745248989218806085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169574436993665318958408113 127180827745248989218806085)
  ·
    refine ⟨23846405202234185478526141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 127180827745248989218806085 23846405202234185478526141)
    ·
      refine ⟨8942401950837819554447303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23846405202234185478526141 8942401950837819554447303)
      ·
        refine ⟨13413602926256729331670955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8942401950837819554447303 13413602926256729331670955)
        ·
          refine ⟨20120404389385093997506433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13413602926256729331670955 20120404389385093997506433)
          ·
            refine ⟨15090303292038820498129825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20120404389385093997506433 15090303292038820498129825)
            ·
              refine ⟨11317727469029115373597369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15090303292038820498129825 11317727469029115373597369)
              ·
                refine ⟨8488295601771836530198027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11317727469029115373597369 8488295601771836530198027)
                ·
                  refine ⟨12732443402657754795297041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8488295601771836530198027 12732443402657754795297041)
                  ·
                    refine ⟨9549332551993316096472781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12732443402657754795297041 9549332551993316096472781)
                    ·
                      refine ⟨3580999706997493536177293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9549332551993316096472781 3580999706997493536177293)
                      ·
                        rfl

theorem cell23_6973972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_6973972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6973972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6973972 prefixEnd_6973972 := by exact prefixLift 6973972
  have htrace : WordTrace (prefixWord ++ tailWord_6973972) baseStart_6973972 baseEnd_6973972 := by
    simpa [prefixWord, tailWord_6973972, baseEnd_6973972] using wordTrace_append hprefix tailTrace_6973972
  have hstable : (prefixWord ++ tailWord_6973972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6973972).length < 2 ^ (prefixWord ++ tailWord_6973972).sum := by decide
  have hdescent : baseEnd_6973972 < baseStart_6973972 := by decide
  rcases family_descends (prefixWord ++ tailWord_6973972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6973975 : List Nat := [1, 1, 3, 6, 1, 2, 2, 7]
def baseStart_6973975 : Nat := 118140960795 + 6973975 * 2 ^ 59
def prefixEnd_6973975 : Nat := 4983230072969 + 3 ^ 40 * 6973975 * 2
def baseEnd_6973975 : Nat := 132629675831091000905177

theorem tailTrace_6973975 : CollatzResearch.WordTrace tailWord_6973975 prefixEnd_6973975 132629675831091000905177 := by
  unfold tailWord_6973975
  simp only [CollatzResearch.WordTrace]
  refine ⟨254361764909487109949971379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169574509939658073299980919 254361764909487109949971379)
  ·
    refine ⟨381542647364230664924957069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254361764909487109949971379 381542647364230664924957069)
    ·
      refine ⟨143078492761586499346858901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 381542647364230664924957069 143078492761586499346858901)
      ·
        refine ⟨6706804348199367156884011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 143078492761586499346858901 6706804348199367156884011)
        ·
          refine ⟨10060206522299050735326017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6706804348199367156884011 10060206522299050735326017)
          ·
            refine ⟨7545154891724288051494513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10060206522299050735326017 7545154891724288051494513)
            ·
              refine ⟨5658866168793216038620885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7545154891724288051494513 5658866168793216038620885)
              ·
                refine ⟨132629675831091000905177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5658866168793216038620885 132629675831091000905177)
                ·
                  rfl

theorem cell23_6973975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 2, 7].length) (baseStart_6973975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6973975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6973975 prefixEnd_6973975 := by exact prefixLift 6973975
  have htrace : WordTrace (prefixWord ++ tailWord_6973975) baseStart_6973975 baseEnd_6973975 := by
    simpa [prefixWord, tailWord_6973975, baseEnd_6973975] using wordTrace_append hprefix tailTrace_6973975
  have hstable : (prefixWord ++ tailWord_6973975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6973975).length < 2 ^ (prefixWord ++ tailWord_6973975).sum := by decide
  have hdescent : baseEnd_6973975 < baseStart_6973975 := by decide
  rcases family_descends (prefixWord ++ tailWord_6973975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6973978 : List Nat := [3, 1, 1, 3, 1, 1, 2, 3, 3, 3, 2]
def baseStart_6973978 : Nat := 118140960795 + 6973978 * 2 ^ 59
def prefixEnd_6973978 : Nat := 4983230072969 + 3 ^ 40 * 6973978 * 2
def baseEnd_6973978 : Nat := 3581002787881420512702265

theorem tailTrace_6973978 : CollatzResearch.WordTrace tailWord_6973978 prefixEnd_6973978 3581002787881420512702265 := by
  unfold tailWord_6973978
  simp only [CollatzResearch.WordTrace]
  refine ⟨63590468582119060365582647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169574582885650827641553725 63590468582119060365582647)
  ·
    refine ⟨95385702873178590548373971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63590468582119060365582647 95385702873178590548373971)
    ·
      refine ⟨143078554309767885822560957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95385702873178590548373971 143078554309767885822560957)
      ·
        refine ⟨53654457866162957183460359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143078554309767885822560957 53654457866162957183460359)
        ·
          refine ⟨80481686799244435775190539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53654457866162957183460359 80481686799244435775190539)
          ·
            refine ⟨120722530198866653662785809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80481686799244435775190539 120722530198866653662785809)
            ·
              refine ⟨90541897649149990247089357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120722530198866653662785809 90541897649149990247089357)
              ·
                refine ⟨33953211618431246342658509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90541897649149990247089357 33953211618431246342658509)
                ·
                  refine ⟨12732454356911717378496941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33953211618431246342658509 12732454356911717378496941)
                  ·
                    refine ⟨4774670383841894016936353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12732454356911717378496941 4774670383841894016936353)
                    ·
                      refine ⟨3581002787881420512702265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4774670383841894016936353 3581002787881420512702265)
                      ·
                        rfl

theorem cell23_6973978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 3, 3, 3, 2].length) (baseStart_6973978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6973978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6973978 prefixEnd_6973978 := by exact prefixLift 6973978
  have htrace : WordTrace (prefixWord ++ tailWord_6973978) baseStart_6973978 baseEnd_6973978 := by
    simpa [prefixWord, tailWord_6973978, baseEnd_6973978] using wordTrace_append hprefix tailTrace_6973978
  have hstable : (prefixWord ++ tailWord_6973978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6973978).length < 2 ^ (prefixWord ++ tailWord_6973978).sum := by decide
  have hdescent : baseEnd_6973978 < baseStart_6973978 := by decide
  rcases family_descends (prefixWord ++ tailWord_6973978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6973981 : List Nat := [1, 4, 2, 2, 1, 2, 1, 1, 2, 2, 5]
def baseStart_6973981 : Nat := 118140960795 + 6973981 * 2 ^ 59
def prefixEnd_6973981 : Nat := 4983230072969 + 3 ^ 40 * 6973981 * 2
def baseEnd_6973981 : Nat := 3581004328323384000964751

theorem tailTrace_6973981 : CollatzResearch.WordTrace tailWord_6973981 prefixEnd_6973981 3581004328323384000964751 := by
  unfold tailWord_6973981
  simp only [CollatzResearch.WordTrace]
  refine ⟨254361983747465372974689797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169574655831643581983126531 254361983747465372974689797)
  ·
    refine ⟨47692871952649757432754337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 254361983747465372974689797 47692871952649757432754337)
    ·
      refine ⟨35769653964487318074565753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47692871952649757432754337 35769653964487318074565753)
      ·
        refine ⟨26827240473365488555924315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35769653964487318074565753 26827240473365488555924315)
        ·
          refine ⟨40240860710048232833886473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26827240473365488555924315 40240860710048232833886473)
          ·
            refine ⟨30180645532536174625414855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40240860710048232833886473 30180645532536174625414855)
            ·
              refine ⟨45270968298804261938122283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30180645532536174625414855 45270968298804261938122283)
              ·
                refine ⟨67906452448206392907183425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45270968298804261938122283 67906452448206392907183425)
                ·
                  refine ⟨50929839336154794680387569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67906452448206392907183425 50929839336154794680387569)
                  ·
                    refine ⟨38197379502116096010290677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50929839336154794680387569 38197379502116096010290677)
                    ·
                      refine ⟨3581004328323384000964751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38197379502116096010290677 3581004328323384000964751)
                      ·
                        rfl

theorem cell23_6973981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_6973981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6973981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6973981 prefixEnd_6973981 := by exact prefixLift 6973981
  have htrace : WordTrace (prefixWord ++ tailWord_6973981) baseStart_6973981 baseEnd_6973981 := by
    simpa [prefixWord, tailWord_6973981, baseEnd_6973981] using wordTrace_append hprefix tailTrace_6973981
  have hstable : (prefixWord ++ tailWord_6973981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6973981).length < 2 ^ (prefixWord ++ tailWord_6973981).sum := by decide
  have hdescent : baseEnd_6973981 < baseStart_6973981 := by decide
  rcases family_descends (prefixWord ++ tailWord_6973981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6974029 : List Nat := [1, 6, 1, 1, 2, 3, 1, 2, 1, 3, 2]
def baseStart_6974029 : Nat := 118140960795 + 6974029 * 2 ^ 59
def prefixEnd_6974029 : Nat := 4983230072969 + 3 ^ 40 * 6974029 * 2
def baseEnd_6974029 : Nat := 3581028975394799813164531

theorem tailTrace_6974029 : CollatzResearch.WordTrace tailWord_6974029 prefixEnd_6974029 3581028975394799813164531 := by
  unfold tailWord_6974029
  simp only [CollatzResearch.WordTrace]
  refine ⟨254363734451291477172437141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169575822967527651448291427 254363734451291477172437141)
  ·
    refine ⟨11923300052404287992457991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 254363734451291477172437141 11923300052404287992457991)
    ·
      refine ⟨17884950078606431988686987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11923300052404287992457991 17884950078606431988686987)
      ·
        refine ⟨26827425117909647983030481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17884950078606431988686987 26827425117909647983030481)
        ·
          refine ⟨20120568838432235987272861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26827425117909647983030481 20120568838432235987272861)
          ·
            refine ⟨7545213314412088495227323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20120568838432235987272861 7545213314412088495227323)
            ·
              refine ⟨11317819971618132742840985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7545213314412088495227323 11317819971618132742840985)
              ·
                refine ⟨8488364978713599557130739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11317819971618132742840985 8488364978713599557130739)
                ·
                  refine ⟨12732547468070399335696109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8488364978713599557130739 12732547468070399335696109)
                  ·
                    refine ⟨4774705300526399750886041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12732547468070399335696109 4774705300526399750886041)
                    ·
                      refine ⟨3581028975394799813164531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4774705300526399750886041 3581028975394799813164531)
                      ·
                        rfl

theorem cell23_6974029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 1, 2, 1, 3, 2].length) (baseStart_6974029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6974029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6974029 prefixEnd_6974029 := by exact prefixLift 6974029
  have htrace : WordTrace (prefixWord ++ tailWord_6974029) baseStart_6974029 baseEnd_6974029 := by
    simpa [prefixWord, tailWord_6974029, baseEnd_6974029] using wordTrace_append hprefix tailTrace_6974029
  have hstable : (prefixWord ++ tailWord_6974029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6974029).length < 2 ^ (prefixWord ++ tailWord_6974029).sum := by decide
  have hdescent : baseEnd_6974029 < baseStart_6974029 := by decide
  rcases family_descends (prefixWord ++ tailWord_6974029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6974041 : List Nat := [1, 2, 1, 2, 2, 1, 1, 1, 6, 3, 3]
def baseStart_6974041 : Nat := 118140960795 + 6974041 * 2 ^ 59
def prefixEnd_6974041 : Nat := 4983230072969 + 3 ^ 40 * 6974041 * 2
def baseEnd_6974041 : Nat := 3581035137162653766214475

theorem tailTrace_6974041 : CollatzResearch.WordTrace tailWord_6974041 prefixEnd_6974041 3581035137162653766214475 := by
  unfold tailWord_6974041
  simp only [CollatzResearch.WordTrace]
  refine ⟨254364172127248003221873977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169576114751498668814582651 254364172127248003221873977)
  ·
    refine ⟨190773129095436002416405483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254364172127248003221873977 190773129095436002416405483)
    ·
      refine ⟨286159693643154003624608225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190773129095436002416405483 286159693643154003624608225)
      ·
        refine ⟨214619770232365502718456169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 286159693643154003624608225 214619770232365502718456169)
        ·
          refine ⟨160964827674274127038842127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 214619770232365502718456169 160964827674274127038842127)
          ·
            refine ⟨241447241511411190558263191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160964827674274127038842127 241447241511411190558263191)
            ·
              refine ⟨362170862267116785837394787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 241447241511411190558263191 362170862267116785837394787)
              ·
                refine ⟨543256293400675178756092181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 362170862267116785837394787 543256293400675178756092181)
                ·
                  refine ⟨25465138753156649004191821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 543256293400675178756092181 25465138753156649004191821)
                  ·
                    refine ⟨9549427032433743376571933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25465138753156649004191821 9549427032433743376571933)
                    ·
                      refine ⟨3581035137162653766214475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9549427032433743376571933 3581035137162653766214475)
                      ·
                        rfl

theorem cell23_6974041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 6, 3, 3].length) (baseStart_6974041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6974041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6974041 prefixEnd_6974041 := by exact prefixLift 6974041
  have htrace : WordTrace (prefixWord ++ tailWord_6974041) baseStart_6974041 baseEnd_6974041 := by
    simpa [prefixWord, tailWord_6974041, baseEnd_6974041] using wordTrace_append hprefix tailTrace_6974041
  have hstable : (prefixWord ++ tailWord_6974041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6974041).length < 2 ^ (prefixWord ++ tailWord_6974041).sum := by decide
  have hdescent : baseEnd_6974041 < baseStart_6974041 := by decide
  rcases family_descends (prefixWord ++ tailWord_6974041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6974058 : List Nat := [3, 1, 3, 2, 1, 1, 2, 2, 2, 3, 3]
def baseStart_6974058 : Nat := 118140960795 + 6974058 * 2 ^ 59
def prefixEnd_6974058 : Nat := 4983230072969 + 3 ^ 40 * 6974058 * 2
def baseEnd_6974058 : Nat := 3581043866333780199701897

theorem tailTrace_6974058 : CollatzResearch.WordTrace tailWord_6974058 prefixEnd_6974058 3581043866333780199701897 := by
  unfold tailWord_6974058
  simp only [CollatzResearch.WordTrace]
  refine ⟨63591198042046603781310707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169576528112124276750161885 63591198042046603781310707)
  ·
    refine ⟨95386797063069905671966061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63591198042046603781310707 95386797063069905671966061)
    ·
      refine ⟨35770048898651214626987273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95386797063069905671966061 35770048898651214626987273)
      ·
        refine ⟨26827536673988410970240455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35770048898651214626987273 26827536673988410970240455)
        ·
          refine ⟨40241305010982616455360683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26827536673988410970240455 40241305010982616455360683)
          ·
            refine ⟨60361957516473924683041025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40241305010982616455360683 60361957516473924683041025)
            ·
              refine ⟨45271468137355443512280769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60361957516473924683041025 45271468137355443512280769)
              ·
                refine ⟨33953601103016582634210577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45271468137355443512280769 33953601103016582634210577)
                ·
                  refine ⟨25465200827262436975657933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33953601103016582634210577 25465200827262436975657933)
                  ·
                    refine ⟨9549450310223413865871725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25465200827262436975657933 9549450310223413865871725)
                    ·
                      refine ⟨3581043866333780199701897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9549450310223413865871725 3581043866333780199701897)
                      ·
                        rfl

theorem cell23_6974058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 2, 2, 3, 3].length) (baseStart_6974058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6974058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6974058 prefixEnd_6974058 := by exact prefixLift 6974058
  have htrace : WordTrace (prefixWord ++ tailWord_6974058) baseStart_6974058 baseEnd_6974058 := by
    simpa [prefixWord, tailWord_6974058, baseEnd_6974058] using wordTrace_append hprefix tailTrace_6974058
  have hstable : (prefixWord ++ tailWord_6974058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6974058).length < 2 ^ (prefixWord ++ tailWord_6974058).sum := by decide
  have hdescent : baseEnd_6974058 < baseStart_6974058 := by decide
  rcases family_descends (prefixWord ++ tailWord_6974058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6974071 : List Nat := [1, 1, 3, 1, 1, 3, 4, 1, 1, 2, 5]
def baseStart_6974071 : Nat := 118140960795 + 6974071 * 2 ^ 59
def prefixEnd_6974071 : Nat := 4983230072969 + 3 ^ 40 * 6974071 * 2
def baseEnd_6974071 : Nat := 3581050541582288648839337

theorem tailTrace_6974071 : CollatzResearch.WordTrace tailWord_6974071 prefixEnd_6974071 3581050541582288648839337 := by
  unfold tailWord_6974071
  simp only [CollatzResearch.WordTrace]
  refine ⟨254365266317139318345466067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169576844211426212230310711 254365266317139318345466067)
  ·
    refine ⟨381547899475708977518199101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254365266317139318345466067 381547899475708977518199101)
    ·
      refine ⟨143080462303390866569324663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 381547899475708977518199101 143080462303390866569324663)
      ·
        refine ⟨214620693455086299853986995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143080462303390866569324663 214620693455086299853986995)
        ·
          refine ⟨321931040182629449780980493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214620693455086299853986995 321931040182629449780980493)
          ·
            refine ⟨120724140068486043667867685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 321931040182629449780980493 120724140068486043667867685)
            ·
              refine ⟨22635776262841133187725191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 120724140068486043667867685 22635776262841133187725191)
              ·
                refine ⟨33953664394261699781587787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22635776262841133187725191 33953664394261699781587787)
                ·
                  refine ⟨50930496591392549672381681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33953664394261699781587787 50930496591392549672381681)
                  ·
                    refine ⟨38197872443544412254286261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50930496591392549672381681 38197872443544412254286261)
                    ·
                      refine ⟨3581050541582288648839337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38197872443544412254286261 3581050541582288648839337)
                      ·
                        rfl

theorem cell23_6974071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 1, 1, 2, 5].length) (baseStart_6974071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6974071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6974071 prefixEnd_6974071 := by exact prefixLift 6974071
  have htrace : WordTrace (prefixWord ++ tailWord_6974071) baseStart_6974071 baseEnd_6974071 := by
    simpa [prefixWord, tailWord_6974071, baseEnd_6974071] using wordTrace_append hprefix tailTrace_6974071
  have hstable : (prefixWord ++ tailWord_6974071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6974071).length < 2 ^ (prefixWord ++ tailWord_6974071).sum := by decide
  have hdescent : baseEnd_6974071 < baseStart_6974071 := by decide
  rcases family_descends (prefixWord ++ tailWord_6974071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6974125 : List Nat := [1, 5, 2, 1, 1, 2, 1, 3, 3, 4]
def baseStart_6974125 : Nat := 118140960795 + 6974125 * 2 ^ 59
def prefixEnd_6974125 : Nat := 4983230072969 + 3 ^ 40 * 6974125 * 2
def baseEnd_6974125 : Nat := 1193692756512543812521363

theorem tailTrace_6974125 : CollatzResearch.WordTrace tailWord_6974125 prefixEnd_6974125 1193692756512543812521363 := by
  unfold tailWord_6974125
  simp only [CollatzResearch.WordTrace]
  refine ⟨254367235858943685567931829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169578157239295790378621219 254367235858943685567931829)
  ·
    refine ⟨23846928361775970521993609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 254367235858943685567931829 23846928361775970521993609)
    ·
      refine ⟨17885196271331977891495207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23846928361775970521993609 17885196271331977891495207)
      ·
        refine ⟨26827794406997966837242811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17885196271331977891495207 26827794406997966837242811)
        ·
          refine ⟨40241691610496950255864217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26827794406997966837242811 40241691610496950255864217)
          ·
            refine ⟨30181268707872712691898163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40241691610496950255864217 30181268707872712691898163)
            ·
              refine ⟨45271903061809069037847245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30181268707872712691898163 45271903061809069037847245)
              ·
                refine ⟨16976963648178400889192717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45271903061809069037847245 16976963648178400889192717)
                ·
                  refine ⟨6366361368066900333447269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16976963648178400889192717 6366361368066900333447269)
                  ·
                    refine ⟨1193692756512543812521363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6366361368066900333447269 1193692756512543812521363)
                    ·
                      rfl

theorem cell23_6974125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 3, 3, 4].length) (baseStart_6974125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6974125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6974125 prefixEnd_6974125 := by exact prefixLift 6974125
  have htrace : WordTrace (prefixWord ++ tailWord_6974125) baseStart_6974125 baseEnd_6974125 := by
    simpa [prefixWord, tailWord_6974125, baseEnd_6974125] using wordTrace_append hprefix tailTrace_6974125
  have hstable : (prefixWord ++ tailWord_6974125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6974125).length < 2 ^ (prefixWord ++ tailWord_6974125).sum := by decide
  have hdescent : baseEnd_6974125 < baseStart_6974125 := by decide
  rcases family_descends (prefixWord ++ tailWord_6974125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6974175 : List Nat := [1, 1, 2, 3, 2, 3, 1, 1, 4, 3, 2]
def baseStart_6974175 : Nat := 118140960795 + 6974175 * 2 ^ 59
def prefixEnd_6974175 : Nat := 4983230072969 + 3 ^ 40 * 6974175 * 2
def baseEnd_6974175 : Nat := 3581103943570356241938859

theorem tailTrace_6974175 : CollatzResearch.WordTrace tailWord_6974175 prefixEnd_6974175 3581103943570356241938859 := by
  unfold tailWord_6974175
  simp only [CollatzResearch.WordTrace]
  refine ⟨254369059508762544107251979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169579373005841696071501319 254369059508762544107251979)
  ·
    refine ⟨381553589263143816160877969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254369059508762544107251979 381553589263143816160877969)
    ·
      refine ⟨286165191947357862120658477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 381553589263143816160877969 286165191947357862120658477)
      ·
        refine ⟨107311946980259198295246929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 286165191947357862120658477 107311946980259198295246929)
        ·
          refine ⟨80483960235194398721435197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107311946980259198295246929 80483960235194398721435197)
          ·
            refine ⟨30181485088197899520538199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80483960235194398721435197 30181485088197899520538199)
            ·
              refine ⟨45272227632296849280807299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30181485088197899520538199 45272227632296849280807299)
              ·
                refine ⟨67908341448445273921210949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45272227632296849280807299 67908341448445273921210949)
                ·
                  refine ⟨12732814021583488860227053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67908341448445273921210949 12732814021583488860227053)
                  ·
                    refine ⟨4774805258093808322585145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12732814021583488860227053 4774805258093808322585145)
                    ·
                      refine ⟨3581103943570356241938859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4774805258093808322585145 3581103943570356241938859)
                      ·
                        rfl

theorem cell23_6974175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 1, 4, 3, 2].length) (baseStart_6974175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6974175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6974175 prefixEnd_6974175 := by exact prefixLift 6974175
  have htrace : WordTrace (prefixWord ++ tailWord_6974175) baseStart_6974175 baseEnd_6974175 := by
    simpa [prefixWord, tailWord_6974175, baseEnd_6974175] using wordTrace_append hprefix tailTrace_6974175
  have hstable : (prefixWord ++ tailWord_6974175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6974175).length < 2 ^ (prefixWord ++ tailWord_6974175).sum := by decide
  have hdescent : baseEnd_6974175 < baseStart_6974175 := by decide
  rcases family_descends (prefixWord ++ tailWord_6974175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6974188 : List Nat := [2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 4]
def baseStart_6974188 : Nat := 118140960795 + 6974188 * 2 ^ 59
def prefixEnd_6974188 : Nat := 4983230072969 + 3 ^ 40 * 6974188 * 2
def baseEnd_6974188 : Nat := 3581110618818864691076299

theorem tailTrace_6974188 : CollatzResearch.WordTrace tailWord_6974188 prefixEnd_6974188 3581110618818864691076299 := by
  unfold tailWord_6974188
  simp only [CollatzResearch.WordTrace]
  refine ⟨127184766828857723663737609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169579689105143631551650145 127184766828857723663737609)
  ·
    refine ⟨95388575121643292747803207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127184766828857723663737609 95388575121643292747803207)
    ·
      refine ⟨143082862682464939121704811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95388575121643292747803207 143082862682464939121704811)
      ·
        refine ⟨214624294023697408682557217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143082862682464939121704811 214624294023697408682557217)
        ·
          refine ⟨160968220517773056511917913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 214624294023697408682557217 160968220517773056511917913)
          ·
            refine ⟨120726165388329792383938435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160968220517773056511917913 120726165388329792383938435)
            ·
              refine ⟨181089248082494688575907653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120726165388329792383938435 181089248082494688575907653)
              ·
                refine ⟨33954234015467754107982685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 181089248082494688575907653 33954234015467754107982685)
                ·
                  refine ⟨12732837755800407790493507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33954234015467754107982685 12732837755800407790493507)
                  ·
                    refine ⟨19099256633700611685740261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12732837755800407790493507 19099256633700611685740261)
                    ·
                      refine ⟨3581110618818864691076299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19099256633700611685740261 3581110618818864691076299)
                      ·
                        rfl

theorem cell23_6974188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 4].length) (baseStart_6974188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6974188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6974188 prefixEnd_6974188 := by exact prefixLift 6974188
  have htrace : WordTrace (prefixWord ++ tailWord_6974188) baseStart_6974188 baseEnd_6974188 := by
    simpa [prefixWord, tailWord_6974188, baseEnd_6974188] using wordTrace_append hprefix tailTrace_6974188
  have hstable : (prefixWord ++ tailWord_6974188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6974188).length < 2 ^ (prefixWord ++ tailWord_6974188).sum := by decide
  have hdescent : baseEnd_6974188 < baseStart_6974188 := by decide
  rcases family_descends (prefixWord ++ tailWord_6974188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6974215 : List Nat := [1, 1, 4, 4, 1, 2, 1, 2, 1, 6]
def baseStart_6974215 : Nat := 118140960795 + 6974215 * 2 ^ 59
def prefixEnd_6974215 : Nat := 4983230072969 + 3 ^ 40 * 6974215 * 2
def baseEnd_6974215 : Nat := 1193708160932178695146225

theorem tailTrace_6974215 : CollatzResearch.WordTrace tailWord_6974215 prefixEnd_6974215 1193708160932178695146225 := by
  unfold tailWord_6974215
  simp only [CollatzResearch.WordTrace]
  refine ⟨254370518428617630938708099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169580345619078420625805399 254370518428617630938708099)
  ·
    refine ⟨381555777642926446408062149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254370518428617630938708099 381555777642926446408062149)
    ·
      refine ⟨71541708308048708701511653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 381555777642926446408062149 71541708308048708701511653)
      ·
        refine ⟨13414070307759132881533435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71541708308048708701511653 13414070307759132881533435)
        ·
          refine ⟨20121105461638699322300153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13414070307759132881533435 20121105461638699322300153)
          ·
            refine ⟨15090829096229024491725115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20121105461638699322300153 15090829096229024491725115)
            ·
              refine ⟨22636243644343536737587673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15090829096229024491725115 22636243644343536737587673)
              ·
                refine ⟨16977182733257652553190755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22636243644343536737587673 16977182733257652553190755)
                ·
                  refine ⟨25465774099886478829786133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16977182733257652553190755 25465774099886478829786133)
                  ·
                    refine ⟨1193708160932178695146225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25465774099886478829786133 1193708160932178695146225)
                    ·
                      rfl

theorem cell23_6974215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 2, 1, 6].length) (baseStart_6974215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6974215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6974215 prefixEnd_6974215 := by exact prefixLift 6974215
  have htrace : WordTrace (prefixWord ++ tailWord_6974215) baseStart_6974215 baseEnd_6974215 := by
    simpa [prefixWord, tailWord_6974215, baseEnd_6974215] using wordTrace_append hprefix tailTrace_6974215
  have hstable : (prefixWord ++ tailWord_6974215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6974215).length < 2 ^ (prefixWord ++ tailWord_6974215).sum := by decide
  have hdescent : baseEnd_6974215 < baseStart_6974215 := by decide
  rcases family_descends (prefixWord ++ tailWord_6974215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6974225 : List Nat := [1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 3]
def baseStart_6974225 : Nat := 118140960795 + 6974225 * 2 ^ 59
def prefixEnd_6974225 : Nat := 4983230072969 + 3 ^ 40 * 6974225 * 2
def baseEnd_6974225 : Nat := 3581129617603081046313629

theorem tailTrace_6974225 : CollatzResearch.WordTrace tailWord_6974225 prefixEnd_6974225 3581129617603081046313629 := by
  unfold tailWord_6974225
  simp only [CollatzResearch.WordTrace]
  refine ⟨254370883158581402646572129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169580588772387601764381419 254370883158581402646572129)
  ·
    refine ⟨190778162368936051984929097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254370883158581402646572129 190778162368936051984929097)
    ·
      refine ⟨143083621776702038988696823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190778162368936051984929097 143083621776702038988696823)
      ·
        refine ⟨214625432665053058483045235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143083621776702038988696823 214625432665053058483045235)
        ·
          refine ⟨321938148997579587724567853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214625432665053058483045235 321938148997579587724567853)
          ·
            refine ⟨120726805874092345396712945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 321938148997579587724567853 120726805874092345396712945)
            ·
              refine ⟨90545104405569259047534709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120726805874092345396712945 90545104405569259047534709)
              ·
                refine ⟨8488603538022118035706379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 90545104405569259047534709 8488603538022118035706379)
                ·
                  refine ⟨12732905307033177053559569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8488603538022118035706379 12732905307033177053559569)
                  ·
                    refine ⟨9549678980274882790169677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12732905307033177053559569 9549678980274882790169677)
                    ·
                      refine ⟨3581129617603081046313629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9549678980274882790169677 3581129617603081046313629)
                      ·
                        rfl

theorem cell23_6974225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 3].length) (baseStart_6974225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6974225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6974225 prefixEnd_6974225 := by exact prefixLift 6974225
  have htrace : WordTrace (prefixWord ++ tailWord_6974225) baseStart_6974225 baseEnd_6974225 := by
    simpa [prefixWord, tailWord_6974225, baseEnd_6974225] using wordTrace_append hprefix tailTrace_6974225
  have hstable : (prefixWord ++ tailWord_6974225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6974225).length < 2 ^ (prefixWord ++ tailWord_6974225).sum := by decide
  have hdescent : baseEnd_6974225 < baseStart_6974225 := by decide
  rcases family_descends (prefixWord ++ tailWord_6974225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6974258 : List Nat := [3, 2, 1, 1, 3, 1, 1, 2, 2, 7]
def baseStart_6974258 : Nat := 118140960795 + 6974258 * 2 ^ 59
def prefixEnd_6974258 : Nat := 4983230072969 + 3 ^ 40 * 6974258 * 2
def baseEnd_6974258 : Nat := 1193715520821559805733659

theorem tailTrace_6974258 : CollatzResearch.WordTrace tailWord_6974258 prefixEnd_6974258 1193715520821559805733659 := by
  unfold tailWord_6974258
  simp only [CollatzResearch.WordTrace]
  refine ⟨63593021691865462320630857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169581391178307899521682285 63593021691865462320630857)
  ·
    refine ⟨47694766268899096740473143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63593021691865462320630857 47694766268899096740473143)
    ·
      refine ⟨71542149403348645110709715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47694766268899096740473143 71542149403348645110709715)
      ·
        refine ⟨107313224105022967666064573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71542149403348645110709715 107313224105022967666064573)
        ·
          refine ⟨40242459039383612874774215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107313224105022967666064573 40242459039383612874774215)
          ·
            refine ⟨60363688559075419312161323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40242459039383612874774215 60363688559075419312161323)
            ·
              refine ⟨90545532838613128968241985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60363688559075419312161323 90545532838613128968241985)
              ·
                refine ⟨67909149628959846726181489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90545532838613128968241985 67909149628959846726181489)
                ·
                  refine ⟨50931862221719885044636117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67909149628959846726181489 50931862221719885044636117)
                  ·
                    refine ⟨1193715520821559805733659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50931862221719885044636117 1193715520821559805733659)
                    ·
                      rfl

theorem cell23_6974258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 2, 2, 7].length) (baseStart_6974258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6974258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6974258 prefixEnd_6974258 := by exact prefixLift 6974258
  have htrace : WordTrace (prefixWord ++ tailWord_6974258) baseStart_6974258 baseEnd_6974258 := by
    simpa [prefixWord, tailWord_6974258, baseEnd_6974258] using wordTrace_append hprefix tailTrace_6974258
  have hstable : (prefixWord ++ tailWord_6974258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6974258).length < 2 ^ (prefixWord ++ tailWord_6974258).sum := by decide
  have hdescent : baseEnd_6974258 < baseStart_6974258 := by decide
  rcases family_descends (prefixWord ++ tailWord_6974258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6974268 : List Nat := [2, 2, 2, 2, 1, 1, 1, 3, 2, 2, 5]
def baseStart_6974268 : Nat := 118140960795 + 6974268 * 2 ^ 59
def prefixEnd_6974268 : Nat := 4983230072969 + 3 ^ 40 * 6974268 * 2
def baseEnd_6974268 : Nat := 3581151697271224378075931

theorem tailTrace_6974268 : CollatzResearch.WordTrace tailWord_6974268 prefixEnd_6974268 3581151697271224378075931 := by
  unfold tailWord_6974268
  simp only [CollatzResearch.WordTrace]
  refine ⟨127186225748712810495193729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169581634331617080660258305 127186225748712810495193729)
  ·
    refine ⟨95389669311534607871395297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127186225748712810495193729 95389669311534607871395297)
    ·
      refine ⟨71542251983650955903546473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95389669311534607871395297 71542251983650955903546473)
      ·
        refine ⟨53656688987738216927659855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71542251983650955903546473 53656688987738216927659855)
        ·
          refine ⟨80485033481607325391489783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53656688987738216927659855 80485033481607325391489783)
          ·
            refine ⟨120727550222410988087234675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80485033481607325391489783 120727550222410988087234675)
            ·
              refine ⟨181091325333616482130852013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120727550222410988087234675 181091325333616482130852013)
              ·
                refine ⟨67909247000106180799069505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 181091325333616482130852013 67909247000106180799069505)
                ·
                  refine ⟨50931935250079635599302129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67909247000106180799069505 50931935250079635599302129)
                  ·
                    refine ⟨38198951437559726699476597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50931935250079635599302129 38198951437559726699476597)
                    ·
                      refine ⟨3581151697271224378075931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38198951437559726699476597 3581151697271224378075931)
                      ·
                        rfl

theorem cell23_6974268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 3, 2, 2, 5].length) (baseStart_6974268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6974268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6974268 prefixEnd_6974268 := by exact prefixLift 6974268
  have htrace : WordTrace (prefixWord ++ tailWord_6974268) baseStart_6974268 baseEnd_6974268 := by
    simpa [prefixWord, tailWord_6974268, baseEnd_6974268] using wordTrace_append hprefix tailTrace_6974268
  have hstable : (prefixWord ++ tailWord_6974268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6974268).length < 2 ^ (prefixWord ++ tailWord_6974268).sum := by decide
  have hdescent : baseEnd_6974268 < baseStart_6974268 := by decide
  rcases family_descends (prefixWord ++ tailWord_6974268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6974273 : List Nat := [1, 2, 5, 3, 2, 1, 2, 1, 1, 1, 4]
def baseStart_6974273 : Nat := 118140960795 + 6974273 * 2 ^ 59
def prefixEnd_6974273 : Nat := 4983230072969 + 3 ^ 40 * 6974273 * 2
def baseEnd_6974273 : Nat := 3581154264674496858513409

theorem tailTrace_6974273 : CollatzResearch.WordTrace tailWord_6974273 prefixEnd_6974273 3581154264674496858513409 := by
  unfold tailWord_6974273
  simp only [CollatzResearch.WordTrace]
  refine ⟨254372633862407506844319473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169581755908271671229546315 254372633862407506844319473)
  ·
    refine ⟨190779475396805630133239605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254372633862407506844319473 190779475396805630133239605)
    ·
      refine ⟨17885575818450527824991213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 190779475396805630133239605 17885575818450527824991213)
      ·
        refine ⟨6707090931918947934371705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17885575818450527824991213 6707090931918947934371705)
        ·
          refine ⟨5030318198939210950778779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6707090931918947934371705 5030318198939210950778779)
          ·
            refine ⟨7545477298408816426168169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5030318198939210950778779 7545477298408816426168169)
            ·
              refine ⟨5659107973806612319626127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7545477298408816426168169 5659107973806612319626127)
              ·
                refine ⟨8488661960709918479439191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5659107973806612319626127 8488661960709918479439191)
                ·
                  refine ⟨12732992941064877719158787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8488661960709918479439191 12732992941064877719158787)
                  ·
                    refine ⟨19099489411597316578738181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12732992941064877719158787 19099489411597316578738181)
                    ·
                      refine ⟨3581154264674496858513409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19099489411597316578738181 3581154264674496858513409)
                      ·
                        rfl

theorem cell23_6974273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_6974273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6974273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6974273 prefixEnd_6974273 := by exact prefixLift 6974273
  have htrace : WordTrace (prefixWord ++ tailWord_6974273) baseStart_6974273 baseEnd_6974273 := by
    simpa [prefixWord, tailWord_6974273, baseEnd_6974273] using wordTrace_append hprefix tailTrace_6974273
  have hstable : (prefixWord ++ tailWord_6974273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6974273).length < 2 ^ (prefixWord ++ tailWord_6974273).sum := by decide
  have hdescent : baseEnd_6974273 < baseStart_6974273 := by decide
  rcases family_descends (prefixWord ++ tailWord_6974273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6974276 : List Nat := [2, 3, 4, 2, 1, 1, 1, 3, 1, 2, 3]
def baseStart_6974276 : Nat := 118140960795 + 6974276 * 2 ^ 59
def prefixEnd_6974276 : Nat := 4983230072969 + 3 ^ 40 * 6974276 * 2
def baseEnd_6974276 : Nat := 3581155805116460346775895

theorem tailTrace_6974276 : CollatzResearch.WordTrace tailWord_6974276 prefixEnd_6974276 3581155805116460346775895 := by
  unfold tailWord_6974276
  simp only [CollatzResearch.WordTrace]
  refine ⟨127186371640698319178339341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169581828854264425571119121 127186371640698319178339341)
  ·
    refine ⟨47694889365261869691877253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127186371640698319178339341 47694889365261869691877253)
    ·
      refine ⟨8942791755986600567226985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47694889365261869691877253 8942791755986600567226985)
      ·
        refine ⟨6707093816989950425420239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8942791755986600567226985 6707093816989950425420239)
        ·
          refine ⟨10060640725484925638130359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6707093816989950425420239 10060640725484925638130359)
          ·
            refine ⟨15090961088227388457195539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10060640725484925638130359 15090961088227388457195539)
            ·
              refine ⟨22636441632341082685793309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15090961088227388457195539 22636441632341082685793309)
              ·
                refine ⟨8488665612127906007172491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22636441632341082685793309 8488665612127906007172491)
                ·
                  refine ⟨12732998418191859010758737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8488665612127906007172491 12732998418191859010758737)
                  ·
                    refine ⟨9549748813643894258069053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12732998418191859010758737 9549748813643894258069053)
                    ·
                      refine ⟨3581155805116460346775895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9549748813643894258069053 3581155805116460346775895)
                      ·
                        rfl

theorem cell23_6974276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_6974276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6974276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6974276 prefixEnd_6974276 := by exact prefixLift 6974276
  have htrace : WordTrace (prefixWord ++ tailWord_6974276) baseStart_6974276 baseEnd_6974276 := by
    simpa [prefixWord, tailWord_6974276, baseEnd_6974276] using wordTrace_append hprefix tailTrace_6974276
  have hstable : (prefixWord ++ tailWord_6974276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6974276).length < 2 ^ (prefixWord ++ tailWord_6974276).sum := by decide
  have hdescent : baseEnd_6974276 < baseStart_6974276 := by decide
  rcases family_descends (prefixWord ++ tailWord_6974276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6974288 : List Nat := [2, 1, 1, 1, 1, 4, 3, 2, 2, 6]
def baseStart_6974288 : Nat := 118140960795 + 6974288 * 2 ^ 59
def prefixEnd_6974288 : Nat := 4983230072969 + 3 ^ 40 * 6974288 * 2
def baseEnd_6974288 : Nat := 1193720655628104766608613

theorem tailTrace_6974288 : CollatzResearch.WordTrace tailWord_6974288 prefixEnd_6974288 1193720655628104766608613 := by
  unfold tailWord_6974288
  simp only [CollatzResearch.WordTrace]
  refine ⟨127186590478676582203057759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169582120638235442937410345 127186590478676582203057759)
  ·
    refine ⟨190779885718014873304586639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127186590478676582203057759 190779885718014873304586639)
    ·
      refine ⟨286169828577022309956879959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190779885718014873304586639 286169828577022309956879959)
      ·
        refine ⟨429254742865533464935319939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286169828577022309956879959 429254742865533464935319939)
        ·
          refine ⟨643882114298300197402979909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 429254742865533464935319939 643882114298300197402979909)
          ·
            refine ⟨120727896430931287013058733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 643882114298300197402979909 120727896430931287013058733)
            ·
              refine ⟨45272961161599232629897025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 120727896430931287013058733 45272961161599232629897025)
              ·
                refine ⟨33954720871199424472422769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45272961161599232629897025 33954720871199424472422769)
                ·
                  refine ⟨25466040653399568354317077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33954720871199424472422769 25466040653399568354317077)
                  ·
                    refine ⟨1193720655628104766608613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25466040653399568354317077 1193720655628104766608613)
                    ·
                      rfl

theorem cell23_6974288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 2, 2, 6].length) (baseStart_6974288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6974288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6974288 prefixEnd_6974288 := by exact prefixLift 6974288
  have htrace : WordTrace (prefixWord ++ tailWord_6974288) baseStart_6974288 baseEnd_6974288 := by
    simpa [prefixWord, tailWord_6974288, baseEnd_6974288] using wordTrace_append hprefix tailTrace_6974288
  have hstable : (prefixWord ++ tailWord_6974288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6974288).length < 2 ^ (prefixWord ++ tailWord_6974288).sum := by decide
  have hdescent : baseEnd_6974288 < baseStart_6974288 := by decide
  rcases family_descends (prefixWord ++ tailWord_6974288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6974306 : List Nat := [3, 3, 2, 1, 4, 1, 1, 1, 1, 3, 3]
def baseStart_6974306 : Nat := 118140960795 + 6974306 * 2 ^ 59
def prefixEnd_6974306 : Nat := 4983230072969 + 3 ^ 40 * 6974306 * 2
def baseEnd_6974306 : Nat := 3581171209536095229400757

theorem tailTrace_6974306 : CollatzResearch.WordTrace tailWord_6974306 prefixEnd_6974306 3581171209536095229400757 := by
  unfold tailWord_6974306
  simp only [CollatzResearch.WordTrace]
  refine ⟨63593459367821988370067693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169582558314191968986847181 63593459367821988370067693)
  ·
    refine ⟨23847547262933245638775385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63593459367821988370067693 23847547262933245638775385)
    ·
      refine ⟨17885660447199934229081539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23847547262933245638775385 17885660447199934229081539)
      ·
        refine ⟨26828490670799901343622309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17885660447199934229081539 26828490670799901343622309)
        ·
          refine ⟨5030342000774981501929183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26828490670799901343622309 5030342000774981501929183)
          ·
            refine ⟨7545513001162472252893775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5030342000774981501929183 7545513001162472252893775)
            ·
              refine ⟨11318269501743708379340663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7545513001162472252893775 11318269501743708379340663)
              ·
                refine ⟨16977404252615562569010995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11318269501743708379340663 16977404252615562569010995)
                ·
                  refine ⟨25466106378923343853516493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16977404252615562569010995 25466106378923343853516493)
                  ·
                    refine ⟨9549789892096253945068685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25466106378923343853516493 9549789892096253945068685)
                    ·
                      refine ⟨3581171209536095229400757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9549789892096253945068685 3581171209536095229400757)
                      ·
                        rfl

theorem cell23_6974306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 1, 1, 1, 3, 3].length) (baseStart_6974306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6974306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6974306 prefixEnd_6974306 := by exact prefixLift 6974306
  have htrace : WordTrace (prefixWord ++ tailWord_6974306) baseStart_6974306 baseEnd_6974306 := by
    simpa [prefixWord, tailWord_6974306, baseEnd_6974306] using wordTrace_append hprefix tailTrace_6974306
  have hstable : (prefixWord ++ tailWord_6974306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6974306).length < 2 ^ (prefixWord ++ tailWord_6974306).sum := by decide
  have hdescent : baseEnd_6974306 < baseStart_6974306 := by decide
  rcases family_descends (prefixWord ++ tailWord_6974306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6974365 : List Nat := [1, 4, 2, 1, 2, 1, 1, 2, 4, 5]
def baseStart_6974365 : Nat := 118140960795 + 6974365 * 2 ^ 59
def prefixEnd_6974365 : Nat := 4983230072969 + 3 ^ 40 * 6974365 * 2
def baseEnd_6974365 : Nat := 1193733834964903499520995

theorem tailTrace_6974365 : CollatzResearch.WordTrace tailWord_6974365 prefixEnd_6974365 1193733834964903499520995 := by
  unfold tailWord_6974365
  simp only [CollatzResearch.WordTrace]
  refine ⟨254375989378074206556668549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169583992918716137704445699 254375989378074206556668549)
  ·
    refine ⟨47695498008388913729375353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 254375989378074206556668549 47695498008388913729375353)
    ·
      refine ⟨35771623506291685297031515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47695498008388913729375353 35771623506291685297031515)
      ·
        refine ⟨53657435259437527945547273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35771623506291685297031515 53657435259437527945547273)
        ·
          refine ⟨40243076444578145959160455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53657435259437527945547273 40243076444578145959160455)
          ·
            refine ⟨60364614666867218938740683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40243076444578145959160455 60364614666867218938740683)
            ·
              refine ⟨90546922000300828408111025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60364614666867218938740683 90546922000300828408111025)
              ·
                refine ⟨67910191500225621306083269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90546922000300828408111025 67910191500225621306083269)
                ·
                  refine ⟨12733160906292303994890613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67910191500225621306083269 12733160906292303994890613)
                  ·
                    refine ⟨1193733834964903499520995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12733160906292303994890613 1193733834964903499520995)
                    ·
                      rfl

theorem cell23_6974365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 2, 4, 5].length) (baseStart_6974365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6974365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6974365 prefixEnd_6974365 := by exact prefixLift 6974365
  have htrace : WordTrace (prefixWord ++ tailWord_6974365) baseStart_6974365 baseEnd_6974365 := by
    simpa [prefixWord, tailWord_6974365, baseEnd_6974365] using wordTrace_append hprefix tailTrace_6974365
  have hstable : (prefixWord ++ tailWord_6974365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6974365).length < 2 ^ (prefixWord ++ tailWord_6974365).sum := by decide
  have hdescent : baseEnd_6974365 < baseStart_6974365 := by decide
  rcases family_descends (prefixWord ++ tailWord_6974365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6974412 : List Nat := [2, 2, 1, 4, 1, 1, 2, 3, 3, 4]
def baseStart_6974412 : Nat := 118140960795 + 6974412 * 2 ^ 59
def prefixEnd_6974412 : Nat := 4983230072969 + 3 ^ 40 * 6974412 * 2
def baseEnd_6974412 : Nat := 1193741879495157271558423

theorem tailTrace_6974412 : CollatzResearch.WordTrace tailWord_6974412 prefixEnd_6974412 1193741879495157271558423 := by
  unfold tailWord_6974412
  simp only [CollatzResearch.WordTrace]
  refine ⟨127188851804451966791814745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169585135739269289055752993 127188851804451966791814745)
  ·
    refine ⟨95391638853338975093861059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127188851804451966791814745 95391638853338975093861059)
    ·
      refine ⟨143087458280008462640791589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95391638853338975093861059 143087458280008462640791589)
      ·
        refine ⟨26828898427501586745148423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 143087458280008462640791589 26828898427501586745148423)
        ·
          refine ⟨40243347641252380117722635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26828898427501586745148423 40243347641252380117722635)
          ·
            refine ⟨60365021461878570176583953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40243347641252380117722635 60365021461878570176583953)
            ·
              refine ⟨45273766096408927632437965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60365021461878570176583953 45273766096408927632437965)
              ·
                refine ⟨16977662286153347862164237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45273766096408927632437965 16977662286153347862164237)
                ·
                  refine ⟨6366623357307505448311589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16977662286153347862164237 6366623357307505448311589)
                  ·
                    refine ⟨1193741879495157271558423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6366623357307505448311589 1193741879495157271558423)
                    ·
                      rfl

theorem cell23_6974412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 3, 3, 4].length) (baseStart_6974412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6974412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6974412 prefixEnd_6974412 := by exact prefixLift 6974412
  have htrace : WordTrace (prefixWord ++ tailWord_6974412) baseStart_6974412 baseEnd_6974412 := by
    simpa [prefixWord, tailWord_6974412, baseEnd_6974412] using wordTrace_append hprefix tailTrace_6974412
  have hstable : (prefixWord ++ tailWord_6974412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6974412).length < 2 ^ (prefixWord ++ tailWord_6974412).sum := by decide
  have hdescent : baseEnd_6974412 < baseStart_6974412 := by decide
  rcases family_descends (prefixWord ++ tailWord_6974412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6974413 : List Nat := [1, 6, 3, 1, 1, 1, 1, 1, 2, 3, 3]
def baseStart_6974413 : Nat := 118140960795 + 6974413 * 2 ^ 59
def prefixEnd_6974413 : Nat := 4983230072969 + 3 ^ 40 * 6974413 * 2
def baseEnd_6974413 : Nat := 3581226151966126310762765

theorem tailTrace_6974413 : CollatzResearch.WordTrace tailWord_6974413 prefixEnd_6974413 3581226151966126310762765 := by
  unfold tailWord_6974413
  simp only [CollatzResearch.WordTrace]
  refine ⟨254377740081900310754415893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169585160054600207169610595 254377740081900310754415893)
  ·
    refine ⟨11923956566339077066613245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 254377740081900310754415893 11923956566339077066613245)
    ·
      refine ⟨4471483712377153899979967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11923956566339077066613245 4471483712377153899979967)
      ·
        refine ⟨6707225568565730849969951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4471483712377153899979967 6707225568565730849969951)
        ·
          refine ⟨10060838352848596274954927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6707225568565730849969951 10060838352848596274954927)
          ·
            refine ⟨15091257529272894412432391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10060838352848596274954927 15091257529272894412432391)
            ·
              refine ⟨22636886293909341618648587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15091257529272894412432391 22636886293909341618648587)
              ·
                refine ⟨33955329440864012427972881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22636886293909341618648587 33955329440864012427972881)
                ·
                  refine ⟨25466497080648009320979661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33955329440864012427972881 25466497080648009320979661)
                  ·
                    refine ⟨9549936405243003495367373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25466497080648009320979661 9549936405243003495367373)
                    ·
                      refine ⟨3581226151966126310762765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9549936405243003495367373 3581226151966126310762765)
                      ·
                        rfl

theorem cell23_6974413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_6974413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6974413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6974413 prefixEnd_6974413 := by exact prefixLift 6974413
  have htrace : WordTrace (prefixWord ++ tailWord_6974413) baseStart_6974413 baseEnd_6974413 := by
    simpa [prefixWord, tailWord_6974413, baseEnd_6974413] using wordTrace_append hprefix tailTrace_6974413
  have hstable : (prefixWord ++ tailWord_6974413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6974413).length < 2 ^ (prefixWord ++ tailWord_6974413).sum := by decide
  have hdescent : baseEnd_6974413 < baseStart_6974413 := by decide
  rcases family_descends (prefixWord ++ tailWord_6974413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6974429 : List Nat := [1, 4, 3, 1, 2, 2, 1, 2, 3, 4]
def baseStart_6974429 : Nat := 118140960795 + 6974429 * 2 ^ 59
def prefixEnd_6974429 : Nat := 4983230072969 + 3 ^ 40 * 6974429 * 2
def baseEnd_6974429 : Nat := 1193744789218866082720897

theorem tailTrace_6974429 : CollatzResearch.WordTrace tailWord_6974429 prefixEnd_6974429 1193744789218866082720897 := by
  unfold tailWord_6974429
  simp only [CollatzResearch.WordTrace]
  refine ⟨254378323649842345486998341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169585549099894896991332227 254378323649842345486998341)
  ·
    refine ⟨47695935684345439778812189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 254378323649842345486998341 47695935684345439778812189)
    ·
      refine ⟨17885975881629539917054571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47695935684345439778812189 17885975881629539917054571)
      ·
        refine ⟨26828963822444309875581857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17885975881629539917054571 26828963822444309875581857)
        ·
          refine ⟨20121722866833232406686393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26828963822444309875581857 20121722866833232406686393)
          ·
            refine ⟨15091292150124924305014795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20121722866833232406686393 15091292150124924305014795)
            ·
              refine ⟨22636938225187386457522193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15091292150124924305014795 22636938225187386457522193)
              ·
                refine ⟨16977703668890539843141645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22636938225187386457522193 16977703668890539843141645)
                ·
                  refine ⟨6366638875833952441178117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16977703668890539843141645 6366638875833952441178117)
                  ·
                    refine ⟨1193744789218866082720897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6366638875833952441178117 1193744789218866082720897)
                    ·
                      rfl

theorem cell23_6974429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 2, 3, 4].length) (baseStart_6974429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6974429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6974429 prefixEnd_6974429 := by exact prefixLift 6974429
  have htrace : WordTrace (prefixWord ++ tailWord_6974429) baseStart_6974429 baseEnd_6974429 := by
    simpa [prefixWord, tailWord_6974429, baseEnd_6974429] using wordTrace_append hprefix tailTrace_6974429
  have hstable : (prefixWord ++ tailWord_6974429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6974429).length < 2 ^ (prefixWord ++ tailWord_6974429).sum := by decide
  have hdescent : baseEnd_6974429 < baseStart_6974429 := by decide
  rcases family_descends (prefixWord ++ tailWord_6974429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6974439 : List Nat := [1, 1, 5, 2, 2, 1, 3, 1, 2, 2, 3]
def baseStart_6974439 : Nat := 118140960795 + 6974439 * 2 ^ 59
def prefixEnd_6974439 : Nat := 4983230072969 + 3 ^ 40 * 6974439 * 2
def baseEnd_6974439 : Nat := 3581239502463143209037645

theorem tailTrace_6974439 : CollatzResearch.WordTrace tailWord_6974439 prefixEnd_6974439 3581239502463143209037645 := by
  unfold tailWord_6974439
  simp only [CollatzResearch.WordTrace]
  refine ⟨254378688379806117194862371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169585792253204078129908247 254378688379806117194862371)
  ·
    refine ⟨381568032569709175792293557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254378688379806117194862371 381568032569709175792293557)
    ·
      refine ⟨35772003053410235230527521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 381568032569709175792293557 35772003053410235230527521)
      ·
        refine ⟨26829002290057676422895641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35772003053410235230527521 26829002290057676422895641)
        ·
          refine ⟨20121751717543257317171731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26829002290057676422895641 20121751717543257317171731)
          ·
            refine ⟨30182627576314885975757597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20121751717543257317171731 30182627576314885975757597)
            ·
              refine ⟨11318485341118082240909099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30182627576314885975757597 11318485341118082240909099)
              ·
                refine ⟨16977728011677123361363649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11318485341118082240909099 16977728011677123361363649)
                ·
                  refine ⟨12733296008757842521022737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16977728011677123361363649 12733296008757842521022737)
                  ·
                    refine ⟨9549972006568381890767053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12733296008757842521022737 9549972006568381890767053)
                    ·
                      refine ⟨3581239502463143209037645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9549972006568381890767053 3581239502463143209037645)
                      ·
                        rfl

theorem cell23_6974439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 3, 1, 2, 2, 3].length) (baseStart_6974439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6974439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6974439 prefixEnd_6974439 := by exact prefixLift 6974439
  have htrace : WordTrace (prefixWord ++ tailWord_6974439) baseStart_6974439 baseEnd_6974439 := by
    simpa [prefixWord, tailWord_6974439, baseEnd_6974439] using wordTrace_append hprefix tailTrace_6974439
  have hstable : (prefixWord ++ tailWord_6974439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6974439).length < 2 ^ (prefixWord ++ tailWord_6974439).sum := by decide
  have hdescent : baseEnd_6974439 < baseStart_6974439 := by decide
  rcases family_descends (prefixWord ++ tailWord_6974439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6974469 : List Nat := [1, 3, 1, 1, 2, 3, 4, 1, 3, 1, 3]
def baseStart_6974469 : Nat := 118140960795 + 6974469 * 2 ^ 59
def prefixEnd_6974469 : Nat := 4983230072969 + 3 ^ 40 * 6974469 * 2
def baseEnd_6974469 : Nat := 3581254906882778091662507

theorem tailTrace_6974469 : CollatzResearch.WordTrace tailWord_6974469 prefixEnd_6974469 3581254906882778091662507 := by
  unfold tailWord_6974469
  simp only [CollatzResearch.WordTrace]
  refine ⟨254379782569697432318454461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169586521713131621545636307 254379782569697432318454461)
  ·
    refine ⟨95392418463636537119420423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 254379782569697432318454461 95392418463636537119420423)
    ·
      refine ⟨143088627695454805679130635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95392418463636537119420423 143088627695454805679130635)
      ·
        refine ⟨214632941543182208518695953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143088627695454805679130635 214632941543182208518695953)
        ·
          refine ⟨160974706157386656389021965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 214632941543182208518695953 160974706157386656389021965)
          ·
            refine ⟨60365514809019996145883237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 160974706157386656389021965 60365514809019996145883237)
            ·
              refine ⟨11318534026691249277353107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60365514809019996145883237 11318534026691249277353107)
              ·
                refine ⟨16977801040036873916029661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11318534026691249277353107 16977801040036873916029661)
                ·
                  refine ⟨6366675390013827718511123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16977801040036873916029661 6366675390013827718511123)
                  ·
                    refine ⟨9550013085020741577766685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6366675390013827718511123 9550013085020741577766685)
                    ·
                      refine ⟨3581254906882778091662507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9550013085020741577766685 3581254906882778091662507)
                      ·
                        rfl

theorem cell23_6974469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 4, 1, 3, 1, 3].length) (baseStart_6974469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6974469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6974469 prefixEnd_6974469 := by exact prefixLift 6974469
  have htrace : WordTrace (prefixWord ++ tailWord_6974469) baseStart_6974469 baseEnd_6974469 := by
    simpa [prefixWord, tailWord_6974469, baseEnd_6974469] using wordTrace_append hprefix tailTrace_6974469
  have hstable : (prefixWord ++ tailWord_6974469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6974469).length < 2 ^ (prefixWord ++ tailWord_6974469).sum := by decide
  have hdescent : baseEnd_6974469 < baseStart_6974469 := by decide
  rcases family_descends (prefixWord ++ tailWord_6974469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6974512 : List Nat := [2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 5]
def baseStart_6974512 : Nat := 118140960795 + 6974512 * 2 ^ 59
def prefixEnd_6974512 : Nat := 4983230072969 + 3 ^ 40 * 6974512 * 2
def baseEnd_6974512 : Nat := 3581276986550921423424809

theorem tailTrace_6974512 : CollatzResearch.WordTrace tailWord_6974512 prefixEnd_6974512 3581276986550921423424809 := by
  unfold tailWord_6974512
  simp only [CollatzResearch.WordTrace]
  refine ⟨127190675454270825331134895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169587567272361100441513193 127190675454270825331134895)
  ·
    refine ⟨190786013181406237996702343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127190675454270825331134895 190786013181406237996702343)
    ·
      refine ⟨286179019772109356995053515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190786013181406237996702343 286179019772109356995053515)
      ·
        refine ⟨429268529658164035492580273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286179019772109356995053515 429268529658164035492580273)
        ·
          refine ⟨321951397243623026619435205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 429268529658164035492580273 321951397243623026619435205)
          ·
            refine ⟨60365886983179317491144101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 321951397243623026619435205 60365886983179317491144101)
            ·
              refine ⟨11318603809346122029589519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60365886983179317491144101 11318603809346122029589519)
              ·
                refine ⟨16977905714019183044384279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11318603809346122029589519 16977905714019183044384279)
                ·
                  refine ⟨25466858571028774566576419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16977905714019183044384279 25466858571028774566576419)
                  ·
                    refine ⟨38200287856543161849864629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25466858571028774566576419 38200287856543161849864629)
                    ·
                      refine ⟨3581276986550921423424809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38200287856543161849864629 3581276986550921423424809)
                      ·
                        rfl

theorem cell23_6974512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 5].length) (baseStart_6974512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6974512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6974512 prefixEnd_6974512 := by exact prefixLift 6974512
  have htrace : WordTrace (prefixWord ++ tailWord_6974512) baseStart_6974512 baseEnd_6974512 := by
    simpa [prefixWord, tailWord_6974512, baseEnd_6974512] using wordTrace_append hprefix tailTrace_6974512
  have hstable : (prefixWord ++ tailWord_6974512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6974512).length < 2 ^ (prefixWord ++ tailWord_6974512).sum := by decide
  have hdescent : baseEnd_6974512 < baseStart_6974512 := by decide
  rcases family_descends (prefixWord ++ tailWord_6974512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6974546 : List Nat := [3, 2, 2, 1, 3, 1, 3, 2, 1, 2, 3]
def baseStart_6974546 : Nat := 118140960795 + 6974546 * 2 ^ 59
def prefixEnd_6974546 : Nat := 4983230072969 + 3 ^ 40 * 6974546 * 2
def baseEnd_6974546 : Nat := 3581294444893174290399653

theorem tailTrace_6974546 : CollatzResearch.WordTrace tailWord_6974546 prefixEnd_6974546 3581294444893174290399653 := by
  unfold tailWord_6974546
  simp only [CollatzResearch.WordTrace]
  refine ⟨63595647747604618617251873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169588393993612316312671661 63595647747604618617251873)
  ·
    refine ⟨47696735810703463962938905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63595647747604618617251873 47696735810703463962938905)
    ·
      refine ⟨35772551858027597972204179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47696735810703463962938905 35772551858027597972204179)
      ·
        refine ⟨53658827787041396958306269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35772551858027597972204179 53658827787041396958306269)
        ·
          refine ⟨20122060420140523859364851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53658827787041396958306269 20122060420140523859364851)
          ·
            refine ⟨30183090630210785789047277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20122060420140523859364851 30183090630210785789047277)
            ·
              refine ⟨11318658986329044670892729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30183090630210785789047277 11318658986329044670892729)
              ·
                refine ⟨8488994239746783503169547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11318658986329044670892729 8488994239746783503169547)
                ·
                  refine ⟨12733491359620175254754321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8488994239746783503169547 12733491359620175254754321)
                  ·
                    refine ⟨9550118519715131441065741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12733491359620175254754321 9550118519715131441065741)
                    ·
                      refine ⟨3581294444893174290399653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9550118519715131441065741 3581294444893174290399653)
                      ·
                        rfl

theorem cell23_6974546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 3, 2, 1, 2, 3].length) (baseStart_6974546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6974546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6974546 prefixEnd_6974546 := by exact prefixLift 6974546
  have htrace : WordTrace (prefixWord ++ tailWord_6974546) baseStart_6974546 baseEnd_6974546 := by
    simpa [prefixWord, tailWord_6974546, baseEnd_6974546] using wordTrace_append hprefix tailTrace_6974546
  have hstable : (prefixWord ++ tailWord_6974546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6974546).length < 2 ^ (prefixWord ++ tailWord_6974546).sum := by decide
  have hdescent : baseEnd_6974546 < baseStart_6974546 := by decide
  rcases family_descends (prefixWord ++ tailWord_6974546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6974576 : List Nat := [2, 1, 1, 1, 5, 1, 4, 2, 2, 1, 3]
def baseStart_6974576 : Nat := 118140960795 + 6974576 * 2 ^ 59
def prefixEnd_6974576 : Nat := 4983230072969 + 3 ^ 40 * 6974576 * 2
def baseEnd_6974576 : Nat := 3581309849312809173024515

theorem tailTrace_6974576 : CollatzResearch.WordTrace tailWord_6974576 prefixEnd_6974576 3581309849312809173024515 := by
  unfold tailWord_6974576
  simp only [CollatzResearch.WordTrace]
  refine ⟨127191842590154894796299791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169589123453539859728399721 127191842590154894796299791)
  ·
    refine ⟨190787763885232342194449687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127191842590154894796299791 190787763885232342194449687)
    ·
      refine ⟨286181645827848513291674531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190787763885232342194449687 286181645827848513291674531)
      ·
        refine ⟨429272468741772769937511797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286181645827848513291674531 429272468741772769937511797)
        ·
          refine ⟨40244293944541197181641731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 429272468741772769937511797 40244293944541197181641731)
          ·
            refine ⟨60366440916811795772462597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40244293944541197181641731 60366440916811795772462597)
            ·
              refine ⟨11318707671902211707336737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60366440916811795772462597 11318707671902211707336737)
              ·
                refine ⟨8489030753926658780502553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11318707671902211707336737 8489030753926658780502553)
                ·
                  refine ⟨6366773065444994085376915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8489030753926658780502553 6366773065444994085376915)
                  ·
                    refine ⟨9550159598167491128065373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6366773065444994085376915 9550159598167491128065373)
                    ·
                      refine ⟨3581309849312809173024515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9550159598167491128065373 3581309849312809173024515)
                      ·
                        rfl

theorem cell23_6974576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 4, 2, 2, 1, 3].length) (baseStart_6974576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6974576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6974576 prefixEnd_6974576 := by exact prefixLift 6974576
  have htrace : WordTrace (prefixWord ++ tailWord_6974576) baseStart_6974576 baseEnd_6974576 := by
    simpa [prefixWord, tailWord_6974576, baseEnd_6974576] using wordTrace_append hprefix tailTrace_6974576
  have hstable : (prefixWord ++ tailWord_6974576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6974576).length < 2 ^ (prefixWord ++ tailWord_6974576).sum := by decide
  have hdescent : baseEnd_6974576 < baseStart_6974576 := by decide
  rcases family_descends (prefixWord ++ tailWord_6974576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6974590 : List Nat := [4, 2, 4, 1, 1, 1, 2, 1, 1, 2, 4]
def baseStart_6974590 : Nat := 118140960795 + 6974590 * 2 ^ 59
def prefixEnd_6974590 : Nat := 4983230072969 + 3 ^ 40 * 6974590 * 2
def baseEnd_6974590 : Nat := 3581317038041972118249451

theorem tailTrace_6974590 : CollatzResearch.WordTrace tailWord_6974590 prefixEnd_6974590 3581317038041972118249451 := by
  unfold tailWord_6974590
  simp only [CollatzResearch.WordTrace]
  refine ⟨31798024475282383747951153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 169589463868172713322406149 31798024475282383747951153)
  ·
    refine ⟨23848518356461787810963365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31798024475282383747951153 23848518356461787810963365)
    ·
      refine ⟨4471597191836585214555631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23848518356461787810963365 4471597191836585214555631)
      ·
        refine ⟨6707395787754877821833447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4471597191836585214555631 6707395787754877821833447)
        ·
          refine ⟨10061093681632316732750171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6707395787754877821833447 10061093681632316732750171)
          ·
            refine ⟨15091640522448475099125257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10061093681632316732750171 15091640522448475099125257)
            ·
              refine ⟨11318730391836356324343943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15091640522448475099125257 11318730391836356324343943)
              ·
                refine ⟨16978095587754534486515915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11318730391836356324343943 16978095587754534486515915)
                ·
                  refine ⟨25467143381631801729773873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16978095587754534486515915 25467143381631801729773873)
                  ·
                    refine ⟨19100357536223851297330405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25467143381631801729773873 19100357536223851297330405)
                    ·
                      refine ⟨3581317038041972118249451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19100357536223851297330405 3581317038041972118249451)
                      ·
                        rfl

theorem cell23_6974590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_6974590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6974590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6974590 prefixEnd_6974590 := by exact prefixLift 6974590
  have htrace : WordTrace (prefixWord ++ tailWord_6974590) baseStart_6974590 baseEnd_6974590 := by
    simpa [prefixWord, tailWord_6974590, baseEnd_6974590] using wordTrace_append hprefix tailTrace_6974590
  have hstable : (prefixWord ++ tailWord_6974590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6974590).length < 2 ^ (prefixWord ++ tailWord_6974590).sum := by decide
  have hdescent : baseEnd_6974590 < baseStart_6974590 := by decide
  rcases family_descends (prefixWord ++ tailWord_6974590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6974616 : List Nat := [2, 1, 2, 4, 2, 1, 2, 2, 1, 4, 2]
def baseStart_6974616 : Nat := 118140960795 + 6974616 * 2 ^ 59
def prefixEnd_6974616 : Nat := 4983230072969 + 3 ^ 40 * 6974616 * 2
def baseEnd_6974616 : Nat := 3581330388538989016524331

theorem tailTrace_6974616 : CollatzResearch.WordTrace tailWord_6974616 prefixEnd_6974616 3581330388538989016524331 := by
  unfold tailWord_6974616
  simp only [CollatzResearch.WordTrace]
  refine ⟨127192572050082438212027851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169590096066776584282703801 127192572050082438212027851)
  ·
    refine ⟨190788858075123657318041777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127192572050082438212027851 190788858075123657318041777)
    ·
      refine ⟨143091643556342742988531333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190788858075123657318041777 143091643556342742988531333)
      ·
        refine ⟨26829683166814264310349625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 143091643556342742988531333 26829683166814264310349625)
        ·
          refine ⟨20122262375110698232762219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26829683166814264310349625 20122262375110698232762219)
          ·
            refine ⟨30183393562666047349143329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20122262375110698232762219 30183393562666047349143329)
            ·
              refine ⟨22637545171999535511857497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30183393562666047349143329 22637545171999535511857497)
              ·
                refine ⟨16978158878999651633893123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22637545171999535511857497 16978158878999651633893123)
                ·
                  refine ⟨25467238318499477450839685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16978158878999651633893123 25467238318499477450839685)
                  ·
                    refine ⟨4775107184718652022032441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25467238318499477450839685 4775107184718652022032441)
                    ·
                      refine ⟨3581330388538989016524331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4775107184718652022032441 3581330388538989016524331)
                      ·
                        rfl

theorem cell23_6974616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 2, 1, 4, 2].length) (baseStart_6974616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6974616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6974616 prefixEnd_6974616 := by exact prefixLift 6974616
  have htrace : WordTrace (prefixWord ++ tailWord_6974616) baseStart_6974616 baseEnd_6974616 := by
    simpa [prefixWord, tailWord_6974616, baseEnd_6974616] using wordTrace_append hprefix tailTrace_6974616
  have hstable : (prefixWord ++ tailWord_6974616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6974616).length < 2 ^ (prefixWord ++ tailWord_6974616).sum := by decide
  have hdescent : baseEnd_6974616 < baseStart_6974616 := by decide
  rcases family_descends (prefixWord ++ tailWord_6974616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6974620 : List Nat := [2, 2, 3, 2, 1, 4, 2, 1, 1, 3, 2]
def baseStart_6974620 : Nat := 118140960795 + 6974620 * 2 ^ 59
def prefixEnd_6974620 : Nat := 4983230072969 + 3 ^ 40 * 6974620 * 2
def baseEnd_6974620 : Nat := 3581332442461607000874313

theorem tailTrace_6974620 : CollatzResearch.WordTrace tailWord_6974620 prefixEnd_6974620 3581332442461607000874313 := by
  unfold tailWord_6974620
  simp only [CollatzResearch.WordTrace]
  refine ⟨127192644996075192553600657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169590193328100256738134209 127192644996075192553600657)
  ·
    refine ⟨95394483747056394415200493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127192644996075192553600657 95394483747056394415200493)
    ·
      refine ⟨35772931405146147905700185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95394483747056394415200493 35772931405146147905700185)
      ·
        refine ⟨26829698553859610929275139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35772931405146147905700185 26829698553859610929275139)
        ·
          refine ⟨40244547830789416393912709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26829698553859610929275139 40244547830789416393912709)
          ·
            refine ⟨7545852718273015573858633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40244547830789416393912709 7545852718273015573858633)
            ·
              refine ⟨5659389538704761680393975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7545852718273015573858633 5659389538704761680393975)
              ·
                refine ⟨8489084308057142520590963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5659389538704761680393975 8489084308057142520590963)
                ·
                  refine ⟨12733626462085713780886445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8489084308057142520590963 12733626462085713780886445)
                  ·
                    refine ⟨4775109923282142667832417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12733626462085713780886445 4775109923282142667832417)
                    ·
                      refine ⟨3581332442461607000874313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4775109923282142667832417 3581332442461607000874313)
                      ·
                        rfl

theorem cell23_6974620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 2, 1, 1, 3, 2].length) (baseStart_6974620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6974620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6974620 prefixEnd_6974620 := by exact prefixLift 6974620
  have htrace : WordTrace (prefixWord ++ tailWord_6974620) baseStart_6974620 baseEnd_6974620 := by
    simpa [prefixWord, tailWord_6974620, baseEnd_6974620] using wordTrace_append hprefix tailTrace_6974620
  have hstable : (prefixWord ++ tailWord_6974620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6974620).length < 2 ^ (prefixWord ++ tailWord_6974620).sum := by decide
  have hdescent : baseEnd_6974620 < baseStart_6974620 := by decide
  rcases family_descends (prefixWord ++ tailWord_6974620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6974639 : List Nat := [1, 1, 2, 1, 2, 3, 4, 4, 5]
def baseStart_6974639 : Nat := 118140960795 + 6974639 * 2 ^ 59
def prefixEnd_6974639 : Nat := 4983230072969 + 3 ^ 40 * 6974639 * 2
def baseEnd_6974639 : Nat := 397926910954893602948525

theorem tailTrace_6974639 : CollatzResearch.WordTrace tailWord_6974639 prefixEnd_6974639 397926910954893602948525 := by
  unfold tailWord_6974639
  simp only [CollatzResearch.WordTrace]
  refine ⟨254385982979081551352142971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169590655319387700901428647 254385982979081551352142971)
  ·
    refine ⟨381578974468622327028214457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254385982979081551352142971 381578974468622327028214457)
    ·
      refine ⟨286184230851466745271160843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 381578974468622327028214457 286184230851466745271160843)
      ·
        refine ⟨429276346277200117906741265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286184230851466745271160843 429276346277200117906741265)
        ·
          refine ⟨321957259707900088430055949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 429276346277200117906741265 321957259707900088430055949)
          ·
            refine ⟨120733972390462533161270981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 321957259707900088430055949 120733972390462533161270981)
            ·
              refine ⟨22637619823211724967738309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 120733972390462533161270981 22637619823211724967738309)
              ·
                refine ⟨4244553716852198431450933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22637619823211724967738309 4244553716852198431450933)
                ·
                  refine ⟨397926910954893602948525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4244553716852198431450933 397926910954893602948525)
                  ·
                    rfl

theorem cell23_6974639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 4, 5].length) (baseStart_6974639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6974639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6974639 prefixEnd_6974639 := by exact prefixLift 6974639
  have htrace : WordTrace (prefixWord ++ tailWord_6974639) baseStart_6974639 baseEnd_6974639 := by
    simpa [prefixWord, tailWord_6974639, baseEnd_6974639] using wordTrace_append hprefix tailTrace_6974639
  have hstable : (prefixWord ++ tailWord_6974639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6974639).length < 2 ^ (prefixWord ++ tailWord_6974639).sum := by decide
  have hdescent : baseEnd_6974639 < baseStart_6974639 := by decide
  rcases family_descends (prefixWord ++ tailWord_6974639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6974649 : List Nat := [1, 2, 1, 4, 1, 3, 2, 1, 2, 3, 3]
def baseStart_6974649 : Nat := 118140960795 + 6974649 * 2 ^ 59
def prefixEnd_6974649 : Nat := 4983230072969 + 3 ^ 40 * 6974649 * 2
def baseEnd_6974649 : Nat := 3581347333400587387411679

theorem tailTrace_6974649 : CollatzResearch.WordTrace tailWord_6974649 prefixEnd_6974649 3581347333400587387411679 := by
  unfold tailWord_6974649
  simp only [CollatzResearch.WordTrace]
  refine ⟨254386347709045323060007001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169590898472696882040004667 254386347709045323060007001)
  ·
    refine ⟨190789760781783992295005251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254386347709045323060007001 190789760781783992295005251)
    ·
      refine ⟨286184641172675988442507877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190789760781783992295005251 286184641172675988442507877)
      ·
        refine ⟨53659620219876747832970227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 286184641172675988442507877 53659620219876747832970227)
        ·
          refine ⟨80489430329815121749455341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53659620219876747832970227 80489430329815121749455341)
          ·
            refine ⟨30183536373680670656045753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80489430329815121749455341 30183536373680670656045753)
            ·
              refine ⟨22637652280260502992034315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30183536373680670656045753 22637652280260502992034315)
              ·
                refine ⟨33956478420390754488051473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22637652280260502992034315 33956478420390754488051473)
                ·
                  refine ⟨25467358815293065866038605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33956478420390754488051473 25467358815293065866038605)
                  ·
                    refine ⟨9550259555734899699764477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25467358815293065866038605 9550259555734899699764477)
                    ·
                      refine ⟨3581347333400587387411679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9550259555734899699764477 3581347333400587387411679)
                      ·
                        rfl

theorem cell23_6974649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 1, 2, 3, 3].length) (baseStart_6974649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6974649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6974649 prefixEnd_6974649 := by exact prefixLift 6974649
  have htrace : WordTrace (prefixWord ++ tailWord_6974649) baseStart_6974649 baseEnd_6974649 := by
    simpa [prefixWord, tailWord_6974649, baseEnd_6974649] using wordTrace_append hprefix tailTrace_6974649
  have hstable : (prefixWord ++ tailWord_6974649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6974649).length < 2 ^ (prefixWord ++ tailWord_6974649).sum := by decide
  have hdescent : baseEnd_6974649 < baseStart_6974649 := by decide
  rcases family_descends (prefixWord ++ tailWord_6974649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6974689 : List Nat := [1, 2, 3, 1, 3, 2, 1, 1, 4, 1, 4]
def baseStart_6974689 : Nat := 118140960795 + 6974689 * 2 ^ 59
def prefixEnd_6974689 : Nat := 4983230072969 + 3 ^ 40 * 6974689 * 2
def baseEnd_6974689 : Nat := 3581367872626767230911495

theorem tailTrace_6974689 : CollatzResearch.WordTrace tailWord_6974689 prefixEnd_6974689 3581367872626767230911495 := by
  unfold tailWord_6974689
  simp only [CollatzResearch.WordTrace]
  refine ⟨254387806628900409891463121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169591871085933606594308747 254387806628900409891463121)
  ·
    refine ⟨190790854971675307418597341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254387806628900409891463121 190790854971675307418597341)
    ·
      refine ⟨71546570614378240281974003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 190790854971675307418597341 71546570614378240281974003)
      ·
        refine ⟨107319855921567360422961005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71546570614378240281974003 107319855921567360422961005)
        ·
          refine ⟨40244945970587760158610377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107319855921567360422961005 40244945970587760158610377)
          ·
            refine ⟨30183709477940820118957783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40244945970587760158610377 30183709477940820118957783)
            ·
              refine ⟨45275564216911230178436675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30183709477940820118957783 45275564216911230178436675)
              ·
                refine ⟨67913346325366845267655013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45275564216911230178436675 67913346325366845267655013)
                ·
                  refine ⟨12733752436006283487685315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67913346325366845267655013 12733752436006283487685315)
                  ·
                    refine ⟨19100628654009425231527973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12733752436006283487685315 19100628654009425231527973)
                    ·
                      refine ⟨3581367872626767230911495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19100628654009425231527973 3581367872626767230911495)
                      ·
                        rfl

theorem cell23_6974689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 1, 4, 1, 4].length) (baseStart_6974689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6974689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6974689 prefixEnd_6974689 := by exact prefixLift 6974689
  have htrace : WordTrace (prefixWord ++ tailWord_6974689) baseStart_6974689 baseEnd_6974689 := by
    simpa [prefixWord, tailWord_6974689, baseEnd_6974689] using wordTrace_append hprefix tailTrace_6974689
  have hstable : (prefixWord ++ tailWord_6974689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6974689).length < 2 ^ (prefixWord ++ tailWord_6974689).sum := by decide
  have hdescent : baseEnd_6974689 < baseStart_6974689 := by decide
  rcases family_descends (prefixWord ++ tailWord_6974689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6974746 : List Nat := [3, 1, 1, 3, 3, 2, 2, 2, 6]
def baseStart_6974746 : Nat := 118140960795 + 6974746 * 2 ^ 59
def prefixEnd_6974746 : Nat := 4983230072969 + 3 ^ 40 * 6974746 * 2
def baseEnd_6974746 : Nat := 397933015669341500877637

theorem tailTrace_6974746 : CollatzResearch.WordTrace tailWord_6974746 prefixEnd_6974746 397933015669341500877637 := by
  unfold tailWord_6974746
  simp only [CollatzResearch.WordTrace]
  refine ⟨63597471397423477156572023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169593257059795939084192061 63597471397423477156572023)
  ·
    refine ⟨95396207096135215734858035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63597471397423477156572023 95396207096135215734858035)
    ·
      refine ⟨143094310644202823602287053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95396207096135215734858035 143094310644202823602287053)
      ·
        refine ⟨53660366491576058850857645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143094310644202823602287053 53660366491576058850857645)
        ·
          refine ⟨20122637434341022069071617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53660366491576058850857645 20122637434341022069071617)
          ·
            refine ⟨15091978075755766551803713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20122637434341022069071617 15091978075755766551803713)
            ·
              refine ⟨11318983556816824913852785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15091978075755766551803713 11318983556816824913852785)
              ·
                refine ⟨8489237667612618685389589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11318983556816824913852785 8489237667612618685389589)
                ·
                  refine ⟨397933015669341500877637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8489237667612618685389589 397933015669341500877637)
                  ·
                    rfl

theorem cell23_6974746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 2, 2, 6].length) (baseStart_6974746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6974746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6974746 prefixEnd_6974746 := by exact prefixLift 6974746
  have htrace : WordTrace (prefixWord ++ tailWord_6974746) baseStart_6974746 baseEnd_6974746 := by
    simpa [prefixWord, tailWord_6974746, baseEnd_6974746] using wordTrace_append hprefix tailTrace_6974746
  have hstable : (prefixWord ++ tailWord_6974746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6974746).length < 2 ^ (prefixWord ++ tailWord_6974746).sum := by decide
  have hdescent : baseEnd_6974746 < baseStart_6974746 := by decide
  rcases family_descends (prefixWord ++ tailWord_6974746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6974773 : List Nat := [1, 3, 3, 1, 2, 3, 1, 2, 3, 1, 3]
def baseStart_6974773 : Nat := 118140960795 + 6974773 * 2 ^ 59
def prefixEnd_6974773 : Nat := 4983230072969 + 3 ^ 40 * 6974773 * 2
def baseEnd_6974773 : Nat := 3581411005001744902261109

theorem tailTrace_6974773 : CollatzResearch.WordTrace tailWord_6974773 prefixEnd_6974773 3581411005001744902261109 := by
  unfold tailWord_6974773
  simp only [CollatzResearch.WordTrace]
  refine ⟨254390870360596092237520973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169593913573730728158347315 254390870360596092237520973)
  ·
    refine ⟨95396576385223534589070365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 254390870360596092237520973 95396576385223534589070365)
    ·
      refine ⟨35773716144458825470901387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95396576385223534589070365 35773716144458825470901387)
      ·
        refine ⟨53660574216688238206352081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35773716144458825470901387 53660574216688238206352081)
        ·
          refine ⟨40245430662516178654764061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53660574216688238206352081 40245430662516178654764061)
          ·
            refine ⟨15092036498443566995536523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40245430662516178654764061 15092036498443566995536523)
            ·
              refine ⟨22638054747665350493304785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15092036498443566995536523 22638054747665350493304785)
              ·
                refine ⟨16978541060749012869978589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22638054747665350493304785 16978541060749012869978589)
                ·
                  refine ⟨6366952897780879826241971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16978541060749012869978589 6366952897780879826241971)
                  ·
                    refine ⟨9550429346671319739362957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6366952897780879826241971 9550429346671319739362957)
                    ·
                      refine ⟨3581411005001744902261109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9550429346671319739362957 3581411005001744902261109)
                      ·
                        rfl

theorem cell23_6974773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 2, 3, 1, 3].length) (baseStart_6974773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6974773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6974773 prefixEnd_6974773 := by exact prefixLift 6974773
  have htrace : WordTrace (prefixWord ++ tailWord_6974773) baseStart_6974773 baseEnd_6974773 := by
    simpa [prefixWord, tailWord_6974773, baseEnd_6974773] using wordTrace_append hprefix tailTrace_6974773
  have hstable : (prefixWord ++ tailWord_6974773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6974773).length < 2 ^ (prefixWord ++ tailWord_6974773).sum := by decide
  have hdescent : baseEnd_6974773 < baseStart_6974773 := by decide
  rcases family_descends (prefixWord ++ tailWord_6974773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6974783 : List Nat := [1, 1, 2, 2, 4, 2, 3, 1, 2, 3, 2]
def baseStart_6974783 : Nat := 118140960795 + 6974783 * 2 ^ 59
def prefixEnd_6974783 : Nat := 4983230072969 + 3 ^ 40 * 6974783 * 2
def baseEnd_6974783 : Nat := 3581416139808289863136063

theorem tailTrace_6974783 : CollatzResearch.WordTrace tailWord_6974783 prefixEnd_6974783 3581416139808289863136063 := by
  unfold tailWord_6974783
  simp only [CollatzResearch.WordTrace]
  refine ⟨254391235090559863945385003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169594156727039909296923335 254391235090559863945385003)
  ·
    refine ⟨381586852635839795918077505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254391235090559863945385003 381586852635839795918077505)
    ·
      refine ⟨286190139476879846938558129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 381586852635839795918077505 286190139476879846938558129)
      ·
        refine ⟨214642604607659885203918597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 286190139476879846938558129 214642604607659885203918597)
        ·
          refine ⟨40245488363936228475734737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 214642604607659885203918597 40245488363936228475734737)
          ·
            refine ⟨30184116272952171356801053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40245488363936228475734737 30184116272952171356801053)
            ·
              refine ⟨11319043602357064258800395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30184116272952171356801053 11319043602357064258800395)
              ·
                refine ⟨16978565403535596388200593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11319043602357064258800395 16978565403535596388200593)
                ·
                  refine ⟨12733924052651697291150445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16978565403535596388200593 12733924052651697291150445)
                  ·
                    refine ⟨4775221519744386484181417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12733924052651697291150445 4775221519744386484181417)
                    ·
                      refine ⟨3581416139808289863136063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4775221519744386484181417 3581416139808289863136063)
                      ·
                        rfl

theorem cell23_6974783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 3, 1, 2, 3, 2].length) (baseStart_6974783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6974783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6974783 prefixEnd_6974783 := by exact prefixLift 6974783
  have htrace : WordTrace (prefixWord ++ tailWord_6974783) baseStart_6974783 baseEnd_6974783 := by
    simpa [prefixWord, tailWord_6974783, baseEnd_6974783] using wordTrace_append hprefix tailTrace_6974783
  have hstable : (prefixWord ++ tailWord_6974783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6974783).length < 2 ^ (prefixWord ++ tailWord_6974783).sum := by decide
  have hdescent : baseEnd_6974783 < baseStart_6974783 := by decide
  rcases family_descends (prefixWord ++ tailWord_6974783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6974797 : List Nat := [1, 6, 1, 3, 2, 1, 1, 2, 6]
def baseStart_6974797 : Nat := 118140960795 + 6974797 * 2 ^ 59
def prefixEnd_6974797 : Nat := 4983230072969 + 3 ^ 40 * 6974797 * 2
def baseEnd_6974797 : Nat := 397935925393050312040111

theorem tailTrace_6974797 : CollatzResearch.WordTrace tailWord_6974797 prefixEnd_6974797 397935925393050312040111 := by
  unfold tailWord_6974797
  simp only [CollatzResearch.WordTrace]
  refine ⟨254391745712509144336394645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169594497141672762890929763 254391745712509144336394645)
  ·
    refine ⟨11924613080273866140768499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 254391745712509144336394645 11924613080273866140768499)
    ·
      refine ⟨17886919620410799211152749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11924613080273866140768499 17886919620410799211152749)
      ·
        refine ⟨6707594857654049704182281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17886919620410799211152749 6707594857654049704182281)
        ·
          refine ⟨5030696143240537278136711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6707594857654049704182281 5030696143240537278136711)
          ·
            refine ⟨7546044214860805917205067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5030696143240537278136711 7546044214860805917205067)
            ·
              refine ⟨11319066322291208875807601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7546044214860805917205067 11319066322291208875807601)
              ·
                refine ⟨8489299741718406656855701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11319066322291208875807601 8489299741718406656855701)
                ·
                  refine ⟨397935925393050312040111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8489299741718406656855701 397935925393050312040111)
                  ·
                    rfl

theorem cell23_6974797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 1, 2, 6].length) (baseStart_6974797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6974797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6974797 prefixEnd_6974797 := by exact prefixLift 6974797
  have htrace : WordTrace (prefixWord ++ tailWord_6974797) baseStart_6974797 baseEnd_6974797 := by
    simpa [prefixWord, tailWord_6974797, baseEnd_6974797] using wordTrace_append hprefix tailTrace_6974797
  have hstable : (prefixWord ++ tailWord_6974797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6974797).length < 2 ^ (prefixWord ++ tailWord_6974797).sum := by decide
  have hdescent : baseEnd_6974797 < baseStart_6974797 := by decide
  rcases family_descends (prefixWord ++ tailWord_6974797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6974809 : List Nat := [1, 2, 1, 2, 2, 2, 2, 2, 3, 2, 4]
def baseStart_6974809 : Nat := 118140960795 + 6974809 * 2 ^ 59
def prefixEnd_6974809 : Nat := 4983230072969 + 3 ^ 40 * 6974809 * 2
def baseEnd_6974809 : Nat := 3581429490305306761410943

theorem tailTrace_6974809 : CollatzResearch.WordTrace tailWord_6974809 prefixEnd_6974809 3581429490305306761410943 := by
  unfold tailWord_6974809
  simp only [CollatzResearch.WordTrace]
  refine ⟨254392183388465670385831481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169594788925643780257220987 254392183388465670385831481)
  ·
    refine ⟨190794137541349252789373611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254392183388465670385831481 190794137541349252789373611)
    ·
      refine ⟨286191206312023879184060417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190794137541349252789373611 286191206312023879184060417)
      ·
        refine ⟨214643404734017909388045313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 286191206312023879184060417 214643404734017909388045313)
        ·
          refine ⟨160982553550513432041033985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 214643404734017909388045313 160982553550513432041033985)
          ·
            refine ⟨120736915162885074030775489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160982553550513432041033985 120736915162885074030775489)
            ·
              refine ⟨90552686372163805523081617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120736915162885074030775489 90552686372163805523081617)
              ·
                refine ⟨67914514779122854142311213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90552686372163805523081617 67914514779122854142311213)
                ·
                  refine ⟨25467943042171070303366705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67914514779122854142311213 25467943042171070303366705)
                  ·
                    refine ⟨19100957281628302727525029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25467943042171070303366705 19100957281628302727525029)
                    ·
                      refine ⟨3581429490305306761410943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19100957281628302727525029 3581429490305306761410943)
                      ·
                        rfl

theorem cell23_6974809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 2, 3, 2, 4].length) (baseStart_6974809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6974809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6974809 prefixEnd_6974809 := by exact prefixLift 6974809
  have htrace : WordTrace (prefixWord ++ tailWord_6974809) baseStart_6974809 baseEnd_6974809 := by
    simpa [prefixWord, tailWord_6974809, baseEnd_6974809] using wordTrace_append hprefix tailTrace_6974809
  have hstable : (prefixWord ++ tailWord_6974809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6974809).length < 2 ^ (prefixWord ++ tailWord_6974809).sum := by decide
  have hdescent : baseEnd_6974809 < baseStart_6974809 := by decide
  rcases family_descends (prefixWord ++ tailWord_6974809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6974816 : List Nat := [2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 5]
def baseStart_6974816 : Nat := 118140960795 + 6974816 * 2 ^ 59
def prefixEnd_6974816 : Nat := 4983230072969 + 3 ^ 40 * 6974816 * 2
def baseEnd_6974816 : Nat := 3581433084669888234023411

theorem tailTrace_6974816 : CollatzResearch.WordTrace tailWord_6974816 prefixEnd_6974816 3581433084669888234023411 := by
  unfold tailWord_6974816
  simp only [CollatzResearch.WordTrace]
  refine ⟨127196219349720155290668151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169594959132960207054224201 127196219349720155290668151)
  ·
    refine ⟨190794329024580232936002227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127196219349720155290668151 190794329024580232936002227)
    ·
      refine ⟨286191493536870349404003341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190794329024580232936002227 286191493536870349404003341)
      ·
        refine ⟨107321810076326381026501253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 286191493536870349404003341 107321810076326381026501253)
        ·
          refine ⟨20122839389311196442468985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 107321810076326381026501253 20122839389311196442468985)
          ·
            refine ⟨15092129541983397331851739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20122839389311196442468985 15092129541983397331851739)
            ·
              refine ⟨22638194312975095997777609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15092129541983397331851739 22638194312975095997777609)
              ·
                refine ⟨16978645734731321998333207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22638194312975095997777609 16978645734731321998333207)
                ·
                  refine ⟨25467968602096982997499811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16978645734731321998333207 25467968602096982997499811)
                  ·
                    refine ⟨38201952903145474496249717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25467968602096982997499811 38201952903145474496249717)
                    ·
                      refine ⟨3581433084669888234023411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38201952903145474496249717 3581433084669888234023411)
                      ·
                        rfl

theorem cell23_6974816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 5].length) (baseStart_6974816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6974816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6974816 prefixEnd_6974816 := by exact prefixLift 6974816
  have htrace : WordTrace (prefixWord ++ tailWord_6974816) baseStart_6974816 baseEnd_6974816 := by
    simpa [prefixWord, tailWord_6974816, baseEnd_6974816] using wordTrace_append hprefix tailTrace_6974816
  have hstable : (prefixWord ++ tailWord_6974816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6974816).length < 2 ^ (prefixWord ++ tailWord_6974816).sum := by decide
  have hdescent : baseEnd_6974816 < baseStart_6974816 := by decide
  rcases family_descends (prefixWord ++ tailWord_6974816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6974823 : List Nat := [1, 1, 5, 1, 4, 2, 1, 1, 1, 6]
def baseStart_6974823 : Nat := 118140960795 + 6974823 * 2 ^ 59
def prefixEnd_6974823 : Nat := 4983230072969 + 3 ^ 40 * 6974823 * 2
def baseEnd_6974823 : Nat := 1193812226344823235545293

theorem tailTrace_6974823 : CollatzResearch.WordTrace tailWord_6974823 prefixEnd_6974823 1193812226344823235545293 := by
  unfold tailWord_6974823
  simp only [CollatzResearch.WordTrace]
  refine ⟨254392694010414950776841123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169595129340276633851227415 254392694010414950776841123)
  ·
    refine ⟨381589041015622426165261685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254392694010414950776841123 381589041015622426165261685)
    ·
      refine ⟨35773972595214602452993283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 381589041015622426165261685 35773972595214602452993283)
      ·
        refine ⟨53660958892821903679489925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35773972595214602452993283 53660958892821903679489925)
        ·
          refine ⟨10061429792404106939904361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53660958892821903679489925 10061429792404106939904361)
          ·
            refine ⟨7546072344303080204928271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10061429792404106939904361 7546072344303080204928271)
            ·
              refine ⟨11319108516454620307392407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7546072344303080204928271 11319108516454620307392407)
              ·
                refine ⟨16978662774681930461088611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11319108516454620307392407 16978662774681930461088611)
                ·
                  refine ⟨25467994162022895691632917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16978662774681930461088611 25467994162022895691632917)
                  ·
                    refine ⟨1193812226344823235545293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25467994162022895691632917 1193812226344823235545293)
                    ·
                      rfl

theorem cell23_6974823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 1, 1, 1, 6].length) (baseStart_6974823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6974823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6974823 prefixEnd_6974823 := by exact prefixLift 6974823
  have htrace : WordTrace (prefixWord ++ tailWord_6974823) baseStart_6974823 baseEnd_6974823 := by
    simpa [prefixWord, tailWord_6974823, baseEnd_6974823] using wordTrace_append hprefix tailTrace_6974823
  have hstable : (prefixWord ++ tailWord_6974823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6974823).length < 2 ^ (prefixWord ++ tailWord_6974823).sum := by decide
  have hdescent : baseEnd_6974823 < baseStart_6974823 := by decide
  rcases family_descends (prefixWord ++ tailWord_6974823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6974850 : List Nat := [3, 4, 2, 1, 1, 2, 2, 1, 1, 1, 5]
def baseStart_6974850 : Nat := 118140960795 + 6974850 * 2 ^ 59
def prefixEnd_6974850 : Nat := 4983230072969 + 3 ^ 40 * 6974850 * 2
def baseEnd_6974850 : Nat := 3581450543012141100998255

theorem tailTrace_6974850 : CollatzResearch.WordTrace tailWord_6974850 prefixEnd_6974850 3581450543012141100998255 := by
  unfold tailWord_6974850
  simp only [CollatzResearch.WordTrace]
  refine ⟨63598419695329283597018501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169595785854211422925382669 63598419695329283597018501)
  ·
    refine ⟨11924703692874240674440969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63598419695329283597018501 11924703692874240674440969)
    ·
      refine ⟨8943527769655680505830727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11924703692874240674440969 8943527769655680505830727)
      ·
        refine ⟨13415291654483520758746091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8943527769655680505830727 13415291654483520758746091)
        ·
          refine ⟨20122937481725281138119137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13415291654483520758746091 20122937481725281138119137)
          ·
            refine ⟨15092203111293960853589353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20122937481725281138119137 15092203111293960853589353)
            ·
              refine ⟨11319152333470470640192015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15092203111293960853589353 11319152333470470640192015)
              ·
                refine ⟨16978728500205705960288023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11319152333470470640192015 16978728500205705960288023)
                ·
                  refine ⟨25468092750308558940432035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16978728500205705960288023 25468092750308558940432035)
                  ·
                    refine ⟨38202139125462838410648053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25468092750308558940432035 38202139125462838410648053)
                    ·
                      refine ⟨3581450543012141100998255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38202139125462838410648053 3581450543012141100998255)
                      ·
                        rfl

theorem cell23_6974850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_6974850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6974850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6974850 prefixEnd_6974850 := by exact prefixLift 6974850
  have htrace : WordTrace (prefixWord ++ tailWord_6974850) baseStart_6974850 baseEnd_6974850 := by
    simpa [prefixWord, tailWord_6974850, baseEnd_6974850] using wordTrace_append hprefix tailTrace_6974850
  have hstable : (prefixWord ++ tailWord_6974850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6974850).length < 2 ^ (prefixWord ++ tailWord_6974850).sum := by decide
  have hdescent : baseEnd_6974850 < baseStart_6974850 := by decide
  rcases family_descends (prefixWord ++ tailWord_6974850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6974859 : List Nat := [1, 1, 1, 1, 4, 3, 1, 2, 2, 2, 5]
def baseStart_6974859 : Nat := 118140960795 + 6974859 * 2 ^ 59
def prefixEnd_6974859 : Nat := 4983230072969 + 3 ^ 40 * 6974859 * 2
def baseEnd_6974859 : Nat := 3581455164338031565785713

theorem tailTrace_6974859 : CollatzResearch.WordTrace tailWord_6974859 prefixEnd_6974859 3581455164338031565785713 := by
  unfold tailWord_6974859
  simp only [CollatzResearch.WordTrace]
  refine ⟨254394007038284528925151631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169596004692189685950101087 254394007038284528925151631)
  ·
    refine ⟨381591010557426793387727447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254394007038284528925151631 381591010557426793387727447)
    ·
      refine ⟨572386515836140190081591171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 381591010557426793387727447 572386515836140190081591171)
      ·
        refine ⟨858579773754210285122386757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 572386515836140190081591171 858579773754210285122386757)
        ·
          refine ⟨160983707578914428460447517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 858579773754210285122386757 160983707578914428460447517)
          ·
            refine ⟨60368890342092910672667819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 160983707578914428460447517 60368890342092910672667819)
            ·
              refine ⟨90553335513139366009001729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60368890342092910672667819 90553335513139366009001729)
              ·
                refine ⟨67915001634854524506751297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90553335513139366009001729 67915001634854524506751297)
                ·
                  refine ⟨50936251226140893380063473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67915001634854524506751297 50936251226140893380063473)
                  ·
                    refine ⟨38202188419605670035047605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50936251226140893380063473 38202188419605670035047605)
                    ·
                      refine ⟨3581455164338031565785713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38202188419605670035047605 3581455164338031565785713)
                      ·
                        rfl

theorem cell23_6974859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 2, 2, 2, 5].length) (baseStart_6974859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6974859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6974859 prefixEnd_6974859 := by exact prefixLift 6974859
  have htrace : WordTrace (prefixWord ++ tailWord_6974859) baseStart_6974859 baseEnd_6974859 := by
    simpa [prefixWord, tailWord_6974859, baseEnd_6974859] using wordTrace_append hprefix tailTrace_6974859
  have hstable : (prefixWord ++ tailWord_6974859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6974859).length < 2 ^ (prefixWord ++ tailWord_6974859).sum := by decide
  have hdescent : baseEnd_6974859 < baseStart_6974859 := by decide
  rcases family_descends (prefixWord ++ tailWord_6974859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6974903 : List Nat := [1, 1, 3, 1, 3, 2, 3, 2, 1, 4, 2]
def baseStart_6974903 : Nat := 118140960795 + 6974903 * 2 ^ 59
def prefixEnd_6974903 : Nat := 4983230072969 + 3 ^ 40 * 6974903 * 2
def baseEnd_6974903 : Nat := 3581477757486829393635511

theorem tailTrace_6974903 : CollatzResearch.WordTrace tailWord_6974903 prefixEnd_6974903 3581477757486829393635511 := by
  unfold tailWord_6974903
  simp only [CollatzResearch.WordTrace]
  refine ⟨254395611850125124439753363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169597074566750082959835575 254395611850125124439753363)
  ·
    refine ⟨381593417775187686659630045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254395611850125124439753363 381593417775187686659630045)
    ·
      refine ⟨143097531665695382497361267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 381593417775187686659630045 143097531665695382497361267)
      ·
        refine ⟨214646297498543073746041901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143097531665695382497361267 214646297498543073746041901)
        ·
          refine ⟨80492361561953652654765713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 214646297498543073746041901 80492361561953652654765713)
          ·
            refine ⟨60369271171465239491074285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80492361561953652654765713 60369271171465239491074285)
            ·
              refine ⟨22638476689299464809152857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60369271171465239491074285 22638476689299464809152857)
              ·
                refine ⟨16978857516974598606864643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22638476689299464809152857 16978857516974598606864643)
                ·
                  refine ⟨25468286275461897910296965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16978857516974598606864643 25468286275461897910296965)
                  ·
                    refine ⟨4775303676649105858180681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25468286275461897910296965 4775303676649105858180681)
                    ·
                      refine ⟨3581477757486829393635511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4775303676649105858180681 3581477757486829393635511)
                      ·
                        rfl

theorem cell23_6974903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 4, 2].length) (baseStart_6974903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6974903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6974903 prefixEnd_6974903 := by exact prefixLift 6974903
  have htrace : WordTrace (prefixWord ++ tailWord_6974903) baseStart_6974903 baseEnd_6974903 := by
    simpa [prefixWord, tailWord_6974903, baseEnd_6974903] using wordTrace_append hprefix tailTrace_6974903
  have hstable : (prefixWord ++ tailWord_6974903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6974903).length < 2 ^ (prefixWord ++ tailWord_6974903).sum := by decide
  have hdescent : baseEnd_6974903 < baseStart_6974903 := by decide
  rcases family_descends (prefixWord ++ tailWord_6974903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6974929 : List Nat := [1, 2, 2, 1, 2, 1, 1, 1, 1, 3, 8]
def baseStart_6974929 : Nat := 118140960795 + 6974929 * 2 ^ 59
def prefixEnd_6974929 : Nat := 4983230072969 + 3 ^ 40 * 6974929 * 2
def baseEnd_6974929 : Nat := 3581491107983846291910391

theorem tailTrace_6974929 : CollatzResearch.WordTrace tailWord_6974929 prefixEnd_6974929 3581491107983846291910391 := by
  unfold tailWord_6974929
  simp only [CollatzResearch.WordTrace]
  refine ⟨254396560148030930880199841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169597706765353953920133227 254396560148030930880199841)
  ·
    refine ⟨190797420111023198160149881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254396560148030930880199841 190797420111023198160149881)
    ·
      refine ⟨143098065083267398620112411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190797420111023198160149881 143098065083267398620112411)
      ·
        refine ⟨214647097624901097930168617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143098065083267398620112411 214647097624901097930168617)
        ·
          refine ⟨160985323218675823447626463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 214647097624901097930168617 160985323218675823447626463)
          ·
            refine ⟨241477984828013735171439695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160985323218675823447626463 241477984828013735171439695)
            ·
              refine ⟨362216977242020602757159543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 241477984828013735171439695 362216977242020602757159543)
              ·
                refine ⟨543325465863030904135739315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 362216977242020602757159543 543325465863030904135739315)
                ·
                  refine ⟨814988198794546356203608973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 543325465863030904135739315 814988198794546356203608973)
                  ·
                    refine ⟨305620574547954883576353365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 814988198794546356203608973 305620574547954883576353365)
                    ·
                      refine ⟨3581491107983846291910391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 305620574547954883576353365 3581491107983846291910391)
                      ·
                        rfl

theorem cell23_6974929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 3, 8].length) (baseStart_6974929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6974929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6974929 prefixEnd_6974929 := by exact prefixLift 6974929
  have htrace : WordTrace (prefixWord ++ tailWord_6974929) baseStart_6974929 baseEnd_6974929 := by
    simpa [prefixWord, tailWord_6974929, baseEnd_6974929] using wordTrace_append hprefix tailTrace_6974929
  have hstable : (prefixWord ++ tailWord_6974929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6974929).length < 2 ^ (prefixWord ++ tailWord_6974929).sum := by decide
  have hdescent : baseEnd_6974929 < baseStart_6974929 := by decide
  rcases family_descends (prefixWord ++ tailWord_6974929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6974936 : List Nat := [2, 1, 2, 2, 2, 1, 3, 1, 1, 5, 3]
def baseStart_6974936 : Nat := 118140960795 + 6974936 * 2 ^ 59
def prefixEnd_6974936 : Nat := 4983230072969 + 3 ^ 40 * 6974936 * 2
def baseEnd_6974936 : Nat := 3581494702348427764522859

theorem tailTrace_6974936 : CollatzResearch.WordTrace tailWord_6974936 prefixEnd_6974936 3581494702348427764522859 := by
  unfold tailWord_6974936
  simp only [CollatzResearch.WordTrace]
  refine ⟨127198407729502785537852331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169597876972670380717136441 127198407729502785537852331)
  ·
    refine ⟨190797611594254178306778497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127198407729502785537852331 190797611594254178306778497)
    ·
      refine ⟨143098208695690633730083873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190797611594254178306778497 143098208695690633730083873)
      ·
        refine ⟨107323656521767975297562905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143098208695690633730083873 107323656521767975297562905)
        ·
          refine ⟨80492742391325981473172179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107323656521767975297562905 80492742391325981473172179)
          ·
            refine ⟨120739113586988972209758269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80492742391325981473172179 120739113586988972209758269)
            ·
              refine ⟨45277167595120864578659351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 120739113586988972209758269 45277167595120864578659351)
              ·
                refine ⟨67915751392681296867989027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45277167595120864578659351 67915751392681296867989027)
                ·
                  refine ⟨101873627089021945301983541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67915751392681296867989027 101873627089021945301983541)
                  ·
                    refine ⟨9550652539595807372060957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 101873627089021945301983541 9550652539595807372060957)
                    ·
                      refine ⟨3581494702348427764522859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9550652539595807372060957 3581494702348427764522859)
                      ·
                        rfl

theorem cell23_6974936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 1, 1, 5, 3].length) (baseStart_6974936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6974936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6974936 prefixEnd_6974936 := by exact prefixLift 6974936
  have htrace : WordTrace (prefixWord ++ tailWord_6974936) baseStart_6974936 baseEnd_6974936 := by
    simpa [prefixWord, tailWord_6974936, baseEnd_6974936] using wordTrace_append hprefix tailTrace_6974936
  have hstable : (prefixWord ++ tailWord_6974936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6974936).length < 2 ^ (prefixWord ++ tailWord_6974936).sum := by decide
  have hdescent : baseEnd_6974936 < baseStart_6974936 := by decide
  rcases family_descends (prefixWord ++ tailWord_6974936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6974939 : List Nat := [1, 1, 1, 1, 1, 1, 1, 2, 7, 7]
def baseStart_6974939 : Nat := 118140960795 + 6974939 * 2 ^ 59
def prefixEnd_6974939 : Nat := 4983230072969 + 3 ^ 40 * 6974939 * 2
def baseEnd_6974939 : Nat := 1193832080930130417595115

theorem tailTrace_6974939 : CollatzResearch.WordTrace tailWord_6974939 prefixEnd_6974939 1193832080930130417595115 := by
  unfold tailWord_6974939
  simp only [CollatzResearch.WordTrace]
  refine ⟨254396924877994702588063871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169597949918663135058709247 254396924877994702588063871)
  ·
    refine ⟨381595387316992053882095807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254396924877994702588063871 381595387316992053882095807)
    ·
      refine ⟨572393080975488080823143711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 381595387316992053882095807 572393080975488080823143711)
      ·
        refine ⟨858589621463232121234715567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 572393080975488080823143711 858589621463232121234715567)
        ·
          refine ⟨1287884432194848181852073351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 858589621463232121234715567 1287884432194848181852073351)
          ·
            refine ⟨1931826648292272272778110027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1287884432194848181852073351 1931826648292272272778110027)
            ·
              refine ⟨2897739972438408409167165041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1931826648292272272778110027 2897739972438408409167165041)
              ·
                refine ⟨2173304979328806306875373781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2897739972438408409167165041 2173304979328806306875373781)
                ·
                  refine ⟨50936835453018897817391573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2173304979328806306875373781 50936835453018897817391573)
                  ·
                    refine ⟨1193832080930130417595115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50936835453018897817391573 1193832080930130417595115)
                    ·
                      rfl

theorem cell23_6974939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 7, 7].length) (baseStart_6974939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6974939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6974939 prefixEnd_6974939 := by exact prefixLift 6974939
  have htrace : WordTrace (prefixWord ++ tailWord_6974939) baseStart_6974939 baseEnd_6974939 := by
    simpa [prefixWord, tailWord_6974939, baseEnd_6974939] using wordTrace_append hprefix tailTrace_6974939
  have hstable : (prefixWord ++ tailWord_6974939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6974939).length < 2 ^ (prefixWord ++ tailWord_6974939).sum := by decide
  have hdescent : baseEnd_6974939 < baseStart_6974939 := by decide
  rcases family_descends (prefixWord ++ tailWord_6974939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6974956 : List Nat := [2, 2, 1, 1, 2, 1, 2, 5, 2, 5]
def baseStart_6974956 : Nat := 118140960795 + 6974956 * 2 ^ 59
def prefixEnd_6974956 : Nat := 4983230072969 + 3 ^ 40 * 6974956 * 2
def baseEnd_6974956 : Nat := 1193834990653839228757589

theorem tailTrace_6974956 : CollatzResearch.WordTrace tailWord_6974956 prefixEnd_6974956 1193834990653839228757589 := by
  unfold tailWord_6974956
  simp only [CollatzResearch.WordTrace]
  refine ⟨127198772459466557245716361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169598363279288742994288481 127198772459466557245716361)
  ·
    refine ⟨95399079344599917934287271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127198772459466557245716361 95399079344599917934287271)
    ·
      refine ⟨143098619016899876901430907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95399079344599917934287271 143098619016899876901430907)
      ·
        refine ⟨214647928525349815352146361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143098619016899876901430907 214647928525349815352146361)
        ·
          refine ⟨160985946394012361514109771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 214647928525349815352146361 160985946394012361514109771)
          ·
            refine ⟨241478919591018542271164657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160985946394012361514109771 241478919591018542271164657)
            ·
              refine ⟨181109189693263906703373493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 241478919591018542271164657 181109189693263906703373493)
              ·
                refine ⟨16978986533743491253441265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 181109189693263906703373493 16978986533743491253441265)
                ·
                  refine ⟨12734239900307618440080949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16978986533743491253441265 12734239900307618440080949)
                  ·
                    refine ⟨1193834990653839228757589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12734239900307618440080949 1193834990653839228757589)
                    ·
                      rfl

theorem cell23_6974956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 5].length) (baseStart_6974956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6974956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6974956 prefixEnd_6974956 := by exact prefixLift 6974956
  have htrace : WordTrace (prefixWord ++ tailWord_6974956) baseStart_6974956 baseEnd_6974956 := by
    simpa [prefixWord, tailWord_6974956, baseEnd_6974956] using wordTrace_append hprefix tailTrace_6974956
  have hstable : (prefixWord ++ tailWord_6974956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6974956).length < 2 ^ (prefixWord ++ tailWord_6974956).sum := by decide
  have hdescent : baseEnd_6974956 < baseStart_6974956 := by decide
  rcases family_descends (prefixWord ++ tailWord_6974956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6974993 : List Nat := [1, 2, 2, 1, 1, 2, 3, 3, 2, 4, 2]
def baseStart_6974993 : Nat := 118140960795 + 6974993 * 2 ^ 59
def prefixEnd_6974993 : Nat := 4983230072969 + 3 ^ 40 * 6974993 * 2
def baseEnd_6974993 : Nat := 3581523970745734041510097

theorem tailTrace_6974993 : CollatzResearch.WordTrace tailWord_6974993 prefixEnd_6974993 3581523970745734041510097 := by
  unfold tailWord_6974993
  simp only [CollatzResearch.WordTrace]
  refine ⟨254398894419799069810529633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169599262946532713207019755 254398894419799069810529633)
  ·
    refine ⟨190799170814849302357897225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254398894419799069810529633 190799170814849302357897225)
    ·
      refine ⟨143099378111136976768422919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190799170814849302357897225 143099378111136976768422919)
      ·
        refine ⟨214649067166705465152634379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143099378111136976768422919 214649067166705465152634379)
        ·
          refine ⟨321973600750058197728951569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214649067166705465152634379 321973600750058197728951569)
          ·
            refine ⟨241480200562543648296713677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 321973600750058197728951569 241480200562543648296713677)
            ·
              refine ⟨90555075210953868111267629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 241480200562543648296713677 90555075210953868111267629)
              ·
                refine ⟨33958153204107700541725361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90555075210953868111267629 33958153204107700541725361)
                ·
                  refine ⟨25468614903080775406294021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33958153204107700541725361 25468614903080775406294021)
                  ·
                    refine ⟨4775365294327645388680129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25468614903080775406294021 4775365294327645388680129)
                    ·
                      refine ⟨3581523970745734041510097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4775365294327645388680129 3581523970745734041510097)
                      ·
                        rfl

theorem cell23_6974993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 4, 2].length) (baseStart_6974993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6974993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6974993 prefixEnd_6974993 := by exact prefixLift 6974993
  have htrace : WordTrace (prefixWord ++ tailWord_6974993) baseStart_6974993 baseEnd_6974993 := by
    simpa [prefixWord, tailWord_6974993, baseEnd_6974993] using wordTrace_append hprefix tailTrace_6974993
  have hstable : (prefixWord ++ tailWord_6974993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6974993).length < 2 ^ (prefixWord ++ tailWord_6974993).sum := by decide
  have hdescent : baseEnd_6974993 < baseStart_6974993 := by decide
  rcases family_descends (prefixWord ++ tailWord_6974993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6975013 : List Nat := [1, 3, 1, 2, 2, 1, 1, 5, 2, 2, 3]
def baseStart_6975013 : Nat := 118140960795 + 6975013 * 2 ^ 59
def prefixEnd_6975013 : Nat := 4983230072969 + 3 ^ 40 * 6975013 * 2
def baseEnd_6975013 : Nat := 3581534240358823963260005

theorem tailTrace_6975013 : CollatzResearch.WordTrace tailWord_6975013 prefixEnd_6975013 3581534240358823963260005 := by
  unfold tailWord_6975013
  simp only [CollatzResearch.WordTrace]
  refine ⟨254399623879726613226257693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169599749253151075484171795 254399623879726613226257693)
  ·
    refine ⟨95399858954897479959846635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 254399623879726613226257693 95399858954897479959846635)
    ·
      refine ⟨143099788432346219939769953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95399858954897479959846635 143099788432346219939769953)
      ·
        refine ⟨107324841324259664954827465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143099788432346219939769953 107324841324259664954827465)
        ·
          refine ⟨80493630993194748716120599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107324841324259664954827465 80493630993194748716120599)
          ·
            refine ⟨120740446489792123074180899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80493630993194748716120599 120740446489792123074180899)
            ·
              refine ⟨181110669734688184611271349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120740446489792123074180899 181110669734688184611271349)
              ·
                refine ⟨16979125287627017307306689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 181110669734688184611271349 16979125287627017307306689)
                ·
                  refine ⟨12734343965720262980480017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16979125287627017307306689 12734343965720262980480017)
                  ·
                    refine ⟨9550757974290197235360013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12734343965720262980480017 9550757974290197235360013)
                    ·
                      refine ⟨3581534240358823963260005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9550757974290197235360013 3581534240358823963260005)
                      ·
                        rfl

theorem cell23_6975013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 5, 2, 2, 3].length) (baseStart_6975013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6975013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6975013 prefixEnd_6975013 := by exact prefixLift 6975013
  have htrace : WordTrace (prefixWord ++ tailWord_6975013) baseStart_6975013 baseEnd_6975013 := by
    simpa [prefixWord, tailWord_6975013, baseEnd_6975013] using wordTrace_append hprefix tailTrace_6975013
  have hstable : (prefixWord ++ tailWord_6975013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6975013).length < 2 ^ (prefixWord ++ tailWord_6975013).sum := by decide
  have hdescent : baseEnd_6975013 < baseStart_6975013 := by decide
  rcases family_descends (prefixWord ++ tailWord_6975013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6975037 : List Nat := [1, 4, 1, 3, 3, 2, 1, 1, 3, 4]
def baseStart_6975037 : Nat := 118140960795 + 6975037 * 2 ^ 59
def prefixEnd_6975037 : Nat := 4983230072969 + 3 ^ 40 * 6975037 * 2
def baseEnd_6975037 : Nat := 1193848854631510623119965

theorem tailTrace_6975037 : CollatzResearch.WordTrace tailWord_6975037 prefixEnd_6975037 1193848854631510623119965 := by
  unfold tailWord_6975037
  simp only [CollatzResearch.WordTrace]
  refine ⟨254400499231639665325131365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169600332821093110216754243 254400499231639665325131365)
  ·
    refine ⟨47700093605932437248462131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 254400499231639665325131365 47700093605932437248462131)
    ·
      refine ⟨71550140408898655872693197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47700093605932437248462131 71550140408898655872693197)
      ·
        refine ⟨26831302653336995952259949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71550140408898655872693197 26831302653336995952259949)
        ·
          refine ⟨10061738495001373482097481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26831302653336995952259949 10061738495001373482097481)
          ·
            refine ⟨7546303871251030111573111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10061738495001373482097481 7546303871251030111573111)
            ·
              refine ⟨11319455806876545167359667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7546303871251030111573111 11319455806876545167359667)
              ·
                refine ⟨16979183710314817751039501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11319455806876545167359667 16979183710314817751039501)
                ·
                  refine ⟨6367193891368056656639813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16979183710314817751039501 6367193891368056656639813)
                  ·
                    refine ⟨1193848854631510623119965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6367193891368056656639813 1193848854631510623119965)
                    ·
                      rfl

theorem cell23_6975037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 1, 1, 3, 4].length) (baseStart_6975037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6975037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6975037 prefixEnd_6975037 := by exact prefixLift 6975037
  have htrace : WordTrace (prefixWord ++ tailWord_6975037) baseStart_6975037 baseEnd_6975037 := by
    simpa [prefixWord, tailWord_6975037, baseEnd_6975037] using wordTrace_append hprefix tailTrace_6975037
  have hstable : (prefixWord ++ tailWord_6975037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6975037).length < 2 ^ (prefixWord ++ tailWord_6975037).sum := by decide
  have hdescent : baseEnd_6975037 < baseStart_6975037 := by decide
  rcases family_descends (prefixWord ++ tailWord_6975037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6975060 : List Nat := [2, 4, 1, 1, 1, 2, 2, 1, 5, 1, 3]
def baseStart_6975060 : Nat := 118140960795 + 6975060 * 2 ^ 59
def prefixEnd_6975060 : Nat := 4983230072969 + 3 ^ 40 * 6975060 * 2
def baseEnd_6975060 : Nat := 3581558373949585279372289

theorem tailTrace_6975060 : CollatzResearch.WordTrace tailWord_6975060 prefixEnd_6975060 3581558373949585279372289 := by
  unfold tailWord_6975060
  simp only [CollatzResearch.WordTrace]
  refine ⟨127200669055278170126609317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169600892073704226835479089 127200669055278170126609317)
  ·
    refine ⟨23850125447864656898739247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 127200669055278170126609317 23850125447864656898739247)
    ·
      refine ⟨35775188171796985348108871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23850125447864656898739247 35775188171796985348108871)
      ·
        refine ⟨53662782257695478022163307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35775188171796985348108871 53662782257695478022163307)
        ·
          refine ⟨80494173386543217033244961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53662782257695478022163307 80494173386543217033244961)
          ·
            refine ⟨60370630039907412774933721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80494173386543217033244961 60370630039907412774933721)
            ·
              refine ⟨45277972529930559581200291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60370630039907412774933721 45277972529930559581200291)
              ·
                refine ⟨67916958794895839371800437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45277972529930559581200291 67916958794895839371800437)
                ·
                  refine ⟨6367214887021484941106291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 67916958794895839371800437 6367214887021484941106291)
                  ·
                    refine ⟨9550822330532227411659437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6367214887021484941106291 9550822330532227411659437)
                    ·
                      refine ⟨3581558373949585279372289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9550822330532227411659437 3581558373949585279372289)
                      ·
                        rfl

theorem cell23_6975060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 1, 5, 1, 3].length) (baseStart_6975060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6975060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6975060 prefixEnd_6975060 := by exact prefixLift 6975060
  have htrace : WordTrace (prefixWord ++ tailWord_6975060) baseStart_6975060 baseEnd_6975060 := by
    simpa [prefixWord, tailWord_6975060, baseEnd_6975060] using wordTrace_append hprefix tailTrace_6975060
  have hstable : (prefixWord ++ tailWord_6975060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6975060).length < 2 ^ (prefixWord ++ tailWord_6975060).sum := by decide
  have hdescent : baseEnd_6975060 < baseStart_6975060 := by decide
  rcases family_descends (prefixWord ++ tailWord_6975060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6975063 : List Nat := [1, 1, 3, 2, 2, 4, 1, 1, 3, 5]
def baseStart_6975063 : Nat := 118140960795 + 6975063 * 2 ^ 59
def prefixEnd_6975063 : Nat := 4983230072969 + 3 ^ 40 * 6975063 * 2
def baseEnd_6975063 : Nat := 1193853304797182922544925

theorem tailTrace_6975063 : CollatzResearch.WordTrace tailWord_6975063 prefixEnd_6975063 1193853304797182922544925 := by
  unfold tailWord_6975063
  simp only [CollatzResearch.WordTrace]
  refine ⟨254401447529545471765577843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169600965019696981177051895 254401447529545471765577843)
  ·
    refine ⟨381602171294318207648366765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254401447529545471765577843 381602171294318207648366765)
    ·
      refine ⟨143100814235369327868137537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 381602171294318207648366765 143100814235369327868137537)
      ·
        refine ⟨107325610676526995901103153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143100814235369327868137537 107325610676526995901103153)
        ·
          refine ⟨80494208007395246925827365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107325610676526995901103153 80494208007395246925827365)
          ·
            refine ⟨15092664001386608798592631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80494208007395246925827365 15092664001386608798592631)
            ·
              refine ⟨22638996002079913197888947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15092664001386608798592631 22638996002079913197888947)
              ·
                refine ⟨33958494003119869796833421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22638996002079913197888947 33958494003119869796833421)
                ·
                  refine ⟨12734435251169951173812533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33958494003119869796833421 12734435251169951173812533)
                  ·
                    refine ⟨1193853304797182922544925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12734435251169951173812533 1193853304797182922544925)
                    ·
                      rfl

theorem cell23_6975063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 1, 3, 5].length) (baseStart_6975063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6975063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6975063 prefixEnd_6975063 := by exact prefixLift 6975063
  have htrace : WordTrace (prefixWord ++ tailWord_6975063) baseStart_6975063 baseEnd_6975063 := by
    simpa [prefixWord, tailWord_6975063, baseEnd_6975063] using wordTrace_append hprefix tailTrace_6975063
  have hstable : (prefixWord ++ tailWord_6975063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6975063).length < 2 ^ (prefixWord ++ tailWord_6975063).sum := by decide
  have hdescent : baseEnd_6975063 < baseStart_6975063 := by decide
  rcases family_descends (prefixWord ++ tailWord_6975063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6975083 : List Nat := [1, 1, 1, 1, 2, 2, 1, 2, 4, 6, 2]
def baseStart_6975083 : Nat := 118140960795 + 6975083 * 2 ^ 59
def prefixEnd_6975083 : Nat := 4983230072969 + 3 ^ 40 * 6975083 * 2
def baseEnd_6975083 : Nat := 3581570184004638689384683

theorem tailTrace_6975083 : CollatzResearch.WordTrace tailWord_6975083 prefixEnd_6975083 3581570184004638689384683 := by
  unfold tailWord_6975083
  simp only [CollatzResearch.WordTrace]
  refine ⟨254402176989473015181305903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169601451326315343454203935 254402176989473015181305903)
  ·
    refine ⟨381603265484209522771958855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254402176989473015181305903 381603265484209522771958855)
    ·
      refine ⟨572404898226314284157938283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 381603265484209522771958855 572404898226314284157938283)
      ·
        refine ⟨858607347339471426236907425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 572404898226314284157938283 858607347339471426236907425)
        ·
          refine ⟨643955510504603569677680569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 858607347339471426236907425 643955510504603569677680569)
          ·
            refine ⟨482966632878452677258260427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 643955510504603569677680569 482966632878452677258260427)
            ·
              refine ⟨724449949317679015887390641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 482966632878452677258260427 724449949317679015887390641)
              ·
                refine ⟨543337461988259261915542981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 724449949317679015887390641 543337461988259261915542981)
                ·
                  refine ⟨101875774122798611609164309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 543337461988259261915542981 101875774122798611609164309)
                  ·
                    refine ⟨4775426912006184919179577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 101875774122798611609164309 4775426912006184919179577)
                    ·
                      refine ⟨3581570184004638689384683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4775426912006184919179577 3581570184004638689384683)
                      ·
                        rfl

theorem cell23_6975083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 4, 6, 2].length) (baseStart_6975083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6975083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6975083 prefixEnd_6975083 := by exact prefixLift 6975083
  have htrace : WordTrace (prefixWord ++ tailWord_6975083) baseStart_6975083 baseEnd_6975083 := by
    simpa [prefixWord, tailWord_6975083, baseEnd_6975083] using wordTrace_append hprefix tailTrace_6975083
  have hstable : (prefixWord ++ tailWord_6975083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6975083).length < 2 ^ (prefixWord ++ tailWord_6975083).sum := by decide
  have hdescent : baseEnd_6975083 < baseStart_6975083 := by decide
  rcases family_descends (prefixWord ++ tailWord_6975083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6975113 : List Nat := [1, 2, 1, 1, 4, 1, 3, 3, 1, 2, 4]
def baseStart_6975113 : Nat := 118140960795 + 6975113 * 2 ^ 59
def prefixEnd_6975113 : Nat := 4983230072969 + 3 ^ 40 * 6975113 * 2
def baseEnd_6975113 : Nat := 3581585588424273572009545

theorem tailTrace_6975113 : CollatzResearch.WordTrace tailWord_6975113 prefixEnd_6975113 3581585588424273572009545 := by
  unfold tailWord_6975113
  simp only [CollatzResearch.WordTrace]
  refine ⟨254403271179364330304897993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169602180786242886869931995 254403271179364330304897993)
  ·
    refine ⟨190802453384523247728673495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254403271179364330304897993 190802453384523247728673495)
    ·
      refine ⟨286203680076784871593010243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190802453384523247728673495 286203680076784871593010243)
      ·
        refine ⟨429305520115177307389515365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286203680076784871593010243 429305520115177307389515365)
        ·
          refine ⟨80494785021595745135534131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 429305520115177307389515365 80494785021595745135534131)
          ·
            refine ⟨120742177532393617703301197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80494785021595745135534131 120742177532393617703301197)
            ·
              refine ⟨45278316574647606638737949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 120742177532393617703301197 45278316574647606638737949)
              ·
                refine ⟨16979368715492852489526731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45278316574647606638737949 16979368715492852489526731)
                ·
                  refine ⟨25469053073239278734290097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16979368715492852489526731 25469053073239278734290097)
                  ·
                    refine ⟨19101789804929459050717573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25469053073239278734290097 19101789804929459050717573)
                    ·
                      refine ⟨3581585588424273572009545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19101789804929459050717573 3581585588424273572009545)
                      ·
                        rfl

theorem cell23_6975113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 3, 1, 2, 4].length) (baseStart_6975113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6975113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6975113 prefixEnd_6975113 := by exact prefixLift 6975113
  have htrace : WordTrace (prefixWord ++ tailWord_6975113) baseStart_6975113 baseEnd_6975113 := by
    simpa [prefixWord, tailWord_6975113, baseEnd_6975113] using wordTrace_append hprefix tailTrace_6975113
  have hstable : (prefixWord ++ tailWord_6975113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6975113).length < 2 ^ (prefixWord ++ tailWord_6975113).sum := by decide
  have hdescent : baseEnd_6975113 < baseStart_6975113 := by decide
  rcases family_descends (prefixWord ++ tailWord_6975113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6975134 : List Nat := [4, 3, 1, 1, 1, 2, 4, 1, 1, 1, 4]
def baseStart_6975134 : Nat := 118140960795 + 6975134 * 2 ^ 59
def prefixEnd_6975134 : Nat := 4983230072969 + 3 ^ 40 * 6975134 * 2
def baseEnd_6975134 : Nat := 3581596371518017989846949

theorem tailTrace_6975134 : CollatzResearch.WordTrace tailWord_6975134 prefixEnd_6975134 3581596371518017989846949 := by
  unfold tailWord_6975134
  simp only [CollatzResearch.WordTrace]
  refine ⟨31800504639036031361426557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 169602691408192167260941637 31800504639036031361426557)
  ·
    refine ⟨11925189239638511760534959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31800504639036031361426557 11925189239638511760534959)
    ·
      refine ⟨17887783859457767640802439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11925189239638511760534959 17887783859457767640802439)
      ·
        refine ⟨26831675789186651461203659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17887783859457767640802439 26831675789186651461203659)
        ·
          refine ⟨40247513683779977191805489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26831675789186651461203659 40247513683779977191805489)
          ·
            refine ⟨30185635262834982893854117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40247513683779977191805489 30185635262834982893854117)
            ·
              refine ⟨5659806611781559292597647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30185635262834982893854117 5659806611781559292597647)
              ·
                refine ⟨8489709917672338938896471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5659806611781559292597647 8489709917672338938896471)
                ·
                  refine ⟨12734564876508508408344707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8489709917672338938896471 12734564876508508408344707)
                  ·
                    refine ⟨19101847314762762612517061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12734564876508508408344707 19101847314762762612517061)
                    ·
                      refine ⟨3581596371518017989846949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19101847314762762612517061 3581596371518017989846949)
                      ·
                        rfl

theorem cell23_6975134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 4, 1, 1, 1, 4].length) (baseStart_6975134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6975134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6975134 prefixEnd_6975134 := by exact prefixLift 6975134
  have htrace : WordTrace (prefixWord ++ tailWord_6975134) baseStart_6975134 baseEnd_6975134 := by
    simpa [prefixWord, tailWord_6975134, baseEnd_6975134] using wordTrace_append hprefix tailTrace_6975134
  have hstable : (prefixWord ++ tailWord_6975134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6975134).length < 2 ^ (prefixWord ++ tailWord_6975134).sum := by decide
  have hdescent : baseEnd_6975134 < baseStart_6975134 := by decide
  rcases family_descends (prefixWord ++ tailWord_6975134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6975137 : List Nat := [1, 2, 3, 3, 2, 2, 1, 3, 1, 2, 3]
def baseStart_6975137 : Nat := 118140960795 + 6975137 * 2 ^ 59
def prefixEnd_6975137 : Nat := 4983230072969 + 3 ^ 40 * 6975137 * 2
def baseEnd_6975137 : Nat := 3581597911959981478109435

theorem tailTrace_6975137 : CollatzResearch.WordTrace tailWord_6975137 prefixEnd_6975137 3581597911959981478109435 := by
  unfold tailWord_6975137
  simp only [CollatzResearch.WordTrace]
  refine ⟨254404146531277382403771665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169602764354184921602514443 254404146531277382403771665)
  ·
    refine ⟨190803109898458036802828749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254404146531277382403771665 190803109898458036802828749)
    ·
      refine ⟨71551166211921763801060781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 190803109898458036802828749 71551166211921763801060781)
      ·
        refine ⟨26831687329470661425397793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71551166211921763801060781 26831687329470661425397793)
        ·
          refine ⟨20123765497102996069048345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26831687329470661425397793 20123765497102996069048345)
          ·
            refine ⟨15092824122827247051786259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20123765497102996069048345 15092824122827247051786259)
            ·
              refine ⟨22639236184240870577679389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15092824122827247051786259 22639236184240870577679389)
              ·
                refine ⟨8489713569090326466629771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22639236184240870577679389 8489713569090326466629771)
                ·
                  refine ⟨12734570353635489699944657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8489713569090326466629771 12734570353635489699944657)
                  ·
                    refine ⟨9550927765226617274958493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12734570353635489699944657 9550927765226617274958493)
                    ·
                      refine ⟨3581597911959981478109435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9550927765226617274958493 3581597911959981478109435)
                      ·
                        rfl

theorem cell23_6975137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 3, 1, 2, 3].length) (baseStart_6975137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6975137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6975137 prefixEnd_6975137 := by exact prefixLift 6975137
  have htrace : WordTrace (prefixWord ++ tailWord_6975137) baseStart_6975137 baseEnd_6975137 := by
    simpa [prefixWord, tailWord_6975137, baseEnd_6975137] using wordTrace_append hprefix tailTrace_6975137
  have hstable : (prefixWord ++ tailWord_6975137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6975137).length < 2 ^ (prefixWord ++ tailWord_6975137).sum := by decide
  have hdescent : baseEnd_6975137 < baseStart_6975137 := by decide
  rcases family_descends (prefixWord ++ tailWord_6975137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6975160 : List Nat := [2, 1, 2, 1, 2, 1, 1, 3, 5, 3, 2]
def baseStart_6975160 : Nat := 118140960795 + 6975160 * 2 ^ 59
def prefixEnd_6975160 : Nat := 4983230072969 + 3 ^ 40 * 6975160 * 2
def baseEnd_6975160 : Nat := 3581609722015034888121829

theorem tailTrace_6975160 : CollatzResearch.WordTrace tailWord_6975160 prefixEnd_6975160 3581609722015034888121829 := by
  unfold tailWord_6975160
  simp only [CollatzResearch.WordTrace]
  refine ⟨127202492705097028665929467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169603323606796038221239289 127202492705097028665929467)
  ·
    refine ⟨190803739057645542998894201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127202492705097028665929467 190803739057645542998894201)
    ·
      refine ⟨143102804293234157249170651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190803739057645542998894201 143102804293234157249170651)
      ·
        refine ⟨214654206439851235873755977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143102804293234157249170651 214654206439851235873755977)
        ·
          refine ⟨160990654829888426905316983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 214654206439851235873755977 160990654829888426905316983)
          ·
            refine ⟨241485982244832640357975475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160990654829888426905316983 241485982244832640357975475)
            ·
              refine ⟨362228973367248960536963213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 241485982244832640357975475 362228973367248960536963213)
              ·
                refine ⟨135835865012718360201361205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 362228973367248960536963213 135835865012718360201361205)
                ·
                  refine ⟨12734612344942346268877613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 135835865012718360201361205 12734612344942346268877613)
                  ·
                    refine ⟨4775479629353379850829105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12734612344942346268877613 4775479629353379850829105)
                    ·
                      refine ⟨3581609722015034888121829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4775479629353379850829105 3581609722015034888121829)
                      ·
                        rfl

theorem cell23_6975160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 5, 3, 2].length) (baseStart_6975160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6975160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6975160 prefixEnd_6975160 := by exact prefixLift 6975160
  have htrace : WordTrace (prefixWord ++ tailWord_6975160) baseStart_6975160 baseEnd_6975160 := by
    simpa [prefixWord, tailWord_6975160, baseEnd_6975160] using wordTrace_append hprefix tailTrace_6975160
  have hstable : (prefixWord ++ tailWord_6975160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6975160).length < 2 ^ (prefixWord ++ tailWord_6975160).sum := by decide
  have hdescent : baseEnd_6975160 < baseStart_6975160 := by decide
  rcases family_descends (prefixWord ++ tailWord_6975160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6975174 : List Nat := [6, 1, 2, 1, 1, 1, 4, 7]
def baseStart_6975174 : Nat := 118140960795 + 6975174 * 2 ^ 59
def prefixEnd_6975174 : Nat := 4983230072969 + 3 ^ 40 * 6975174 * 2
def baseEnd_6975174 : Nat := 132652478175711030864695

theorem tailTrace_6975174 : CollatzResearch.WordTrace tailWord_6975174 prefixEnd_6975174 132652478175711030864695 := by
  unfold tailWord_6975174
  simp only [CollatzResearch.WordTrace]
  refine ⟨7950171751004479303839643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 169603664021428891815245717 7950171751004479303839643)
  ·
    refine ⟨11925257626506718955759465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7950171751004479303839643 11925257626506718955759465)
    ·
      refine ⟨8943943219880039216819599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11925257626506718955759465 8943943219880039216819599)
      ·
        refine ⟨13415914829820058825229399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8943943219880039216819599 13415914829820058825229399)
        ·
          refine ⟨20123872244730088237844099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13415914829820058825229399 20123872244730088237844099)
          ·
            refine ⟨30185808367095132356766149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20123872244730088237844099 30185808367095132356766149)
            ·
              refine ⟨5659839068830337316893653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30185808367095132356766149 5659839068830337316893653)
              ·
                refine ⟨132652478175711030864695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5659839068830337316893653 132652478175711030864695)
                ·
                  rfl

theorem cell23_6975174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 4, 7].length) (baseStart_6975174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6975174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6975174 prefixEnd_6975174 := by exact prefixLift 6975174
  have htrace : WordTrace (prefixWord ++ tailWord_6975174) baseStart_6975174 baseEnd_6975174 := by
    simpa [prefixWord, tailWord_6975174, baseEnd_6975174] using wordTrace_append hprefix tailTrace_6975174
  have hstable : (prefixWord ++ tailWord_6975174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6975174).length < 2 ^ (prefixWord ++ tailWord_6975174).sum := by decide
  have hdescent : baseEnd_6975174 < baseStart_6975174 := by decide
  rcases family_descends (prefixWord ++ tailWord_6975174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6975193 : List Nat := [1, 2, 1, 2, 3, 3, 1, 1, 1, 3, 5]
def baseStart_6975193 : Nat := 118140960795 + 6975193 * 2 ^ 59
def prefixEnd_6975193 : Nat := 4983230072969 + 3 ^ 40 * 6975193 * 2
def baseEnd_6975193 : Nat := 3581626666876633259009177

theorem tailTrace_6975193 : CollatzResearch.WordTrace tailWord_6975193 prefixEnd_6975193 3581626666876633259009177 := by
  unfold tailWord_6975193
  simp only [CollatzResearch.WordTrace]
  refine ⟨254406189019074503967810233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169604126012716335978540155 254406189019074503967810233)
  ·
    refine ⟨190804641764305877975857675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254406189019074503967810233 190804641764305877975857675)
    ·
      refine ⟨286206962646458816963786513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190804641764305877975857675 286206962646458816963786513)
      ·
        refine ⟨214655221984844112722839885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 286206962646458816963786513 214655221984844112722839885)
        ·
          refine ⟨80495708244316542271064957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 214655221984844112722839885 80495708244316542271064957)
          ·
            refine ⟨30185890591618703351649359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80495708244316542271064957 30185890591618703351649359)
            ·
              refine ⟨45278835887428055027474039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30185890591618703351649359 45278835887428055027474039)
              ·
                refine ⟨67918253831142082541211059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45278835887428055027474039 67918253831142082541211059)
                ·
                  refine ⟨101877380746713123811816589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67918253831142082541211059 101877380746713123811816589)
                  ·
                    refine ⟨38204017780017421429431221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 101877380746713123811816589 38204017780017421429431221)
                    ·
                      refine ⟨3581626666876633259009177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38204017780017421429431221 3581626666876633259009177)
                      ·
                        rfl

theorem cell23_6975193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 1, 1, 3, 5].length) (baseStart_6975193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6975193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6975193 prefixEnd_6975193 := by exact prefixLift 6975193
  have htrace : WordTrace (prefixWord ++ tailWord_6975193) baseStart_6975193 baseEnd_6975193 := by
    simpa [prefixWord, tailWord_6975193, baseEnd_6975193] using wordTrace_append hprefix tailTrace_6975193
  have hstable : (prefixWord ++ tailWord_6975193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6975193).length < 2 ^ (prefixWord ++ tailWord_6975193).sum := by decide
  have hdescent : baseEnd_6975193 < baseStart_6975193 := by decide
  rcases family_descends (prefixWord ++ tailWord_6975193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6975243 : List Nat := [1, 1, 1, 1, 5, 1, 2, 3, 1, 7]
def baseStart_6975243 : Nat := 118140960795 + 6975243 * 2 ^ 59
def prefixEnd_6975243 : Nat := 4983230072969 + 3 ^ 40 * 6975243 * 2
def baseEnd_6975243 : Nat := 1193884113636452687794649

theorem tailTrace_6975243 : CollatzResearch.WordTrace tailWord_6975243 prefixEnd_6975243 1193884113636452687794649 := by
  unfold tailWord_6975243
  simp only [CollatzResearch.WordTrace]
  refine ⟨254408012668893362507130383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169605341779262241671420255 254408012668893362507130383)
  ·
    refine ⟨381612019003340043760695575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254408012668893362507130383 381612019003340043760695575)
    ·
      refine ⟨572418028505010065641043363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 381612019003340043760695575 572418028505010065641043363)
      ·
        refine ⟨858627042757515098461565045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 572418028505010065641043363 858627042757515098461565045)
        ·
          refine ⟨80496285258517040480771723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 858627042757515098461565045 80496285258517040480771723)
          ·
            refine ⟨120744427887775560721157585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80496285258517040480771723 120744427887775560721157585)
            ·
              refine ⟨90558320915831670540868189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120744427887775560721157585 90558320915831670540868189)
              ·
                refine ⟨33959370343436876452825571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90558320915831670540868189 33959370343436876452825571)
                ·
                  refine ⟨50939055515155314679238357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33959370343436876452825571 50939055515155314679238357)
                  ·
                    refine ⟨1193884113636452687794649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50939055515155314679238357 1193884113636452687794649)
                    ·
                      rfl

theorem cell23_6975243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 3, 1, 7].length) (baseStart_6975243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6975243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6975243 prefixEnd_6975243 := by exact prefixLift 6975243
  have htrace : WordTrace (prefixWord ++ tailWord_6975243) baseStart_6975243 baseEnd_6975243 := by
    simpa [prefixWord, tailWord_6975243, baseEnd_6975243] using wordTrace_append hprefix tailTrace_6975243
  have hstable : (prefixWord ++ tailWord_6975243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6975243).length < 2 ^ (prefixWord ++ tailWord_6975243).sum := by decide
  have hdescent : baseEnd_6975243 < baseStart_6975243 := by decide
  rcases family_descends (prefixWord ++ tailWord_6975243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6975260 : List Nat := [2, 2, 3, 1, 1, 2, 1, 4, 2, 5]
def baseStart_6975260 : Nat := 118140960795 + 6975260 * 2 ^ 59
def prefixEnd_6975260 : Nat := 4983230072969 + 3 ^ 40 * 6975260 * 2
def baseEnd_6975260 : Nat := 1193887023360161498957123

theorem tailTrace_6975260 : CollatzResearch.WordTrace tailWord_6975260 prefixEnd_6975260 1193887023360161498957123 := by
  unfold tailWord_6975260
  simp only [CollatzResearch.WordTrace]
  refine ⟨127204316354915887205249617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169605755139887849606999489 127204316354915887205249617)
  ·
    refine ⟨95403237266186915403937213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127204316354915887205249617 95403237266186915403937213)
    ·
      refine ⟨35776213974820093276476455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95403237266186915403937213 35776213974820093276476455)
      ·
        refine ⟨53664320962230139914714683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35776213974820093276476455 53664320962230139914714683)
        ·
          refine ⟨80496481443345209872072025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53664320962230139914714683 80496481443345209872072025)
          ·
            refine ⟨60372361082508907404054019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80496481443345209872072025 60372361082508907404054019)
            ·
              refine ⟨90558541623763361106081029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60372361082508907404054019 90558541623763361106081029)
              ·
                refine ⟨16979726554455630207390193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 90558541623763361106081029 16979726554455630207390193)
                ·
                  refine ⟨12734794915841722655542645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16979726554455630207390193 12734794915841722655542645)
                  ·
                    refine ⟨1193887023360161498957123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12734794915841722655542645 1193887023360161498957123)
                    ·
                      rfl

theorem cell23_6975260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 4, 2, 5].length) (baseStart_6975260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6975260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6975260 prefixEnd_6975260 := by exact prefixLift 6975260
  have htrace : WordTrace (prefixWord ++ tailWord_6975260) baseStart_6975260 baseEnd_6975260 := by
    simpa [prefixWord, tailWord_6975260, baseEnd_6975260] using wordTrace_append hprefix tailTrace_6975260
  have hstable : (prefixWord ++ tailWord_6975260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6975260).length < 2 ^ (prefixWord ++ tailWord_6975260).sum := by decide
  have hdescent : baseEnd_6975260 < baseStart_6975260 := by decide
  rcases family_descends (prefixWord ++ tailWord_6975260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6975294 : List Nat := [4, 2, 1, 2, 2, 3, 1, 1, 2, 5]
def baseStart_6975294 : Nat := 118140960795 + 6975294 * 2 ^ 59
def prefixEnd_6975294 : Nat := 4983230072969 + 3 ^ 40 * 6975294 * 2
def baseEnd_6975294 : Nat := 1193892842807579121282071

theorem tailTrace_6975294 : CollatzResearch.WordTrace tailWord_6975294 prefixEnd_6975294 1193892842807579121282071 := by
  unfold tailWord_6975294
  simp only [CollatzResearch.WordTrace]
  refine ⟨31801234098963574777154617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 169606581861139065478157957 31801234098963574777154617)
  ·
    refine ⟨23850925574222681082865963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31801234098963574777154617 23850925574222681082865963)
    ·
      refine ⟨35776388361334021624298945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23850925574222681082865963 35776388361334021624298945)
      ·
        refine ⟨26832291271000516218224209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35776388361334021624298945 26832291271000516218224209)
        ·
          refine ⟨20124218453250387163668157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26832291271000516218224209 20124218453250387163668157)
          ·
            refine ⟨7546581919968895186375559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20124218453250387163668157 7546581919968895186375559)
            ·
              refine ⟨11319872879953342779563339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7546581919968895186375559 11319872879953342779563339)
              ·
                refine ⟨16979809319930014169345009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11319872879953342779563339 16979809319930014169345009)
                ·
                  refine ⟨12734856989947510627008757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16979809319930014169345009 12734856989947510627008757)
                  ·
                    refine ⟨1193892842807579121282071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12734856989947510627008757 1193892842807579121282071)
                    ·
                      rfl

theorem cell23_6975294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 1, 1, 2, 5].length) (baseStart_6975294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6975294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6975294 prefixEnd_6975294 := by exact prefixLift 6975294
  have htrace : WordTrace (prefixWord ++ tailWord_6975294) baseStart_6975294 baseEnd_6975294 := by
    simpa [prefixWord, tailWord_6975294, baseEnd_6975294] using wordTrace_append hprefix tailTrace_6975294
  have hstable : (prefixWord ++ tailWord_6975294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6975294).length < 2 ^ (prefixWord ++ tailWord_6975294).sum := by decide
  have hdescent : baseEnd_6975294 < baseStart_6975294 := by decide
  rcases family_descends (prefixWord ++ tailWord_6975294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6975358 : List Nat := [4, 2, 3, 1, 1, 1, 3, 3, 1, 4]
def baseStart_6975358 : Nat := 118140960795 + 6975358 * 2 ^ 59
def prefixEnd_6975358 : Nat := 4983230072969 + 3 ^ 40 * 6975358 * 2
def baseEnd_6975358 : Nat := 1193903797061541704481973

theorem tailTrace_6975358 : CollatzResearch.WordTrace tailWord_6975358 prefixEnd_6975358 1193903797061541704481973 := by
  unfold tailWord_6975358
  simp only [CollatzResearch.WordTrace]
  refine ⟨31801525882934592143445841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 169608138042317824765044485 31801525882934592143445841)
  ·
    refine ⟨23851144412200944107584381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31801525882934592143445841 23851144412200944107584381)
    ·
      refine ⟨8944179154575354040344143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23851144412200944107584381 8944179154575354040344143)
      ·
        refine ⟨13416268731863031060516215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8944179154575354040344143 13416268731863031060516215)
        ·
          refine ⟨20124403097794546590774323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13416268731863031060516215 20124403097794546590774323)
          ·
            refine ⟨30186604646691819886161485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20124403097794546590774323 30186604646691819886161485)
            ·
              refine ⟨11319976742509432457310557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30186604646691819886161485 11319976742509432457310557)
              ·
                refine ⟨4244991278441037171491459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11319976742509432457310557 4244991278441037171491459)
                ·
                  refine ⟨6367486917661555757237189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4244991278441037171491459 6367486917661555757237189)
                  ·
                    refine ⟨1193903797061541704481973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6367486917661555757237189 1193903797061541704481973)
                    ·
                      rfl

theorem cell23_6975358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_6975358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6975358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6975358 prefixEnd_6975358 := by exact prefixLift 6975358
  have htrace : WordTrace (prefixWord ++ tailWord_6975358) baseStart_6975358 baseEnd_6975358 := by
    simpa [prefixWord, tailWord_6975358, baseEnd_6975358] using wordTrace_append hprefix tailTrace_6975358
  have hstable : (prefixWord ++ tailWord_6975358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6975358).length < 2 ^ (prefixWord ++ tailWord_6975358).sum := by decide
  have hdescent : baseEnd_6975358 < baseStart_6975358 := by decide
  rcases family_descends (prefixWord ++ tailWord_6975358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6975407 : List Nat := [1, 1, 2, 1, 2, 2, 5, 1, 3, 2, 3]
def baseStart_6975407 : Nat := 118140960795 + 6975407 * 2 ^ 59
def prefixEnd_6975407 : Nat := 4983230072969 + 3 ^ 40 * 6975407 * 2
def baseEnd_6975407 : Nat := 3581736551736695421733193

theorem tailTrace_6975407 : CollatzResearch.WordTrace tailWord_6975407 prefixEnd_6975407 3581736551736695421733193 := by
  unfold tailWord_6975407
  simp only [CollatzResearch.WordTrace]
  refine ⟨254413994240299218516100475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169609329493532812344066983 254413994240299218516100475)
  ·
    refine ⟨381620991360448827774150713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254413994240299218516100475 381620991360448827774150713)
    ·
      refine ⟨286215743520336620830613035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 381620991360448827774150713 286215743520336620830613035)
      ·
        refine ⟨429323615280504931245919553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286215743520336620830613035 429323615280504931245919553)
        ·
          refine ⟨321992711460378698434439665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 429323615280504931245919553 321992711460378698434439665)
          ·
            refine ⟨241494533595284023825829749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 321992711460378698434439665 241494533595284023825829749)
            ·
              refine ⟨22640112524557877233671539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 241494533595284023825829749 22640112524557877233671539)
              ·
                refine ⟨33960168786836815850507309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22640112524557877233671539 33960168786836815850507309)
                ·
                  refine ⟨12735063295063805943940241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33960168786836815850507309 12735063295063805943940241)
                  ·
                    refine ⟨9551297471297854457955181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12735063295063805943940241 9551297471297854457955181)
                    ·
                      refine ⟨3581736551736695421733193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9551297471297854457955181 3581736551736695421733193)
                      ·
                        rfl

theorem cell23_6975407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 1, 3, 2, 3].length) (baseStart_6975407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6975407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6975407 prefixEnd_6975407 := by exact prefixLift 6975407
  have htrace : WordTrace (prefixWord ++ tailWord_6975407) baseStart_6975407 baseEnd_6975407 := by
    simpa [prefixWord, tailWord_6975407, baseEnd_6975407] using wordTrace_append hprefix tailTrace_6975407
  have hstable : (prefixWord ++ tailWord_6975407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6975407).length < 2 ^ (prefixWord ++ tailWord_6975407).sum := by decide
  have hdescent : baseEnd_6975407 < baseStart_6975407 := by decide
  rcases family_descends (prefixWord ++ tailWord_6975407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6975417 : List Nat := [1, 2, 1, 4, 2, 1, 3, 2, 1, 2, 4]
def baseStart_6975417 : Nat := 118140960795 + 6975417 * 2 ^ 59
def prefixEnd_6975417 : Nat := 4983230072969 + 3 ^ 40 * 6975417 * 2
def baseEnd_6975417 : Nat := 3581741686543240382608147

theorem tailTrace_6975417 : CollatzResearch.WordTrace tailWord_6975417 prefixEnd_6975417 3581741686543240382608147 := by
  unfold tailWord_6975417
  simp only [CollatzResearch.WordTrace]
  refine ⟨254414358970262990223964505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169609572646841993482643003 254414358970262990223964505)
  ·
    refine ⟨190810769227697242667973379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254414358970262990223964505 190810769227697242667973379)
    ·
      refine ⟨286216153841545864001960069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190810769227697242667973379 286216153841545864001960069)
      ·
        refine ⟨53665528845289849500367513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 286216153841545864001960069 53665528845289849500367513)
        ·
          refine ⟨40249146633967387125275635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53665528845289849500367513 40249146633967387125275635)
          ·
            refine ⟨60373719950951080687913453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40249146633967387125275635 60373719950951080687913453)
            ·
              refine ⟨22640144981606655257967545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60373719950951080687913453 22640144981606655257967545)
              ·
                refine ⟨16980108736204991443475659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22640144981606655257967545 16980108736204991443475659)
                ·
                  refine ⟨25470163104307487165213489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16980108736204991443475659 25470163104307487165213489)
                  ·
                    refine ⟨19102622328230615373910117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25470163104307487165213489 19102622328230615373910117)
                    ·
                      refine ⟨3581741686543240382608147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19102622328230615373910117 3581741686543240382608147)
                      ·
                        rfl

theorem cell23_6975417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 2, 1, 2, 4].length) (baseStart_6975417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6975417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6975417 prefixEnd_6975417 := by exact prefixLift 6975417
  have htrace : WordTrace (prefixWord ++ tailWord_6975417) baseStart_6975417 baseEnd_6975417 := by
    simpa [prefixWord, tailWord_6975417, baseEnd_6975417] using wordTrace_append hprefix tailTrace_6975417
  have hstable : (prefixWord ++ tailWord_6975417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6975417).length < 2 ^ (prefixWord ++ tailWord_6975417).sum := by decide
  have hdescent : baseEnd_6975417 < baseStart_6975417 := by decide
  rcases family_descends (prefixWord ++ tailWord_6975417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6975421 : List Nat := [1, 4, 1, 2, 3, 2, 3, 1, 1, 1, 4]
def baseStart_6975421 : Nat := 118140960795 + 6975421 * 2 ^ 59
def prefixEnd_6975421 : Nat := 4983230072969 + 3 ^ 40 * 6975421 * 2
def baseEnd_6975421 : Nat := 3581743740465858366958129

theorem tailTrace_6975421 : CollatzResearch.WordTrace tailWord_6975421 prefixEnd_6975421 3581743740465858366958129 := by
  unfold tailWord_6975421
  simp only [CollatzResearch.WordTrace]
  refine ⟨254414504862248498907110117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169609669908165665938073411 254414504862248498907110117)
  ·
    refine ⟨47702719661671593545083147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 254414504862248498907110117 47702719661671593545083147)
    ·
      refine ⟨71554079492507390317624721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47702719661671593545083147 71554079492507390317624721)
      ·
        refine ⟨53665559619380542738218541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71554079492507390317624721 53665559619380542738218541)
        ·
          refine ⟨20124584857267703526831953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53665559619380542738218541 20124584857267703526831953)
          ·
            refine ⟨15093438642950777645123965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20124584857267703526831953 15093438642950777645123965)
            ·
              refine ⟨5660039491106541616921487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15093438642950777645123965 5660039491106541616921487)
              ·
                refine ⟨8490059236659812425382231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5660039491106541616921487 8490059236659812425382231)
                ·
                  refine ⟨12735088854989718638073347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8490059236659812425382231 12735088854989718638073347)
                  ·
                    refine ⟨19102633282484577957110021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12735088854989718638073347 19102633282484577957110021)
                    ·
                      refine ⟨3581743740465858366958129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19102633282484577957110021 3581743740465858366958129)
                      ·
                        rfl

theorem cell23_6975421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 3, 1, 1, 1, 4].length) (baseStart_6975421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6975421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6975421 prefixEnd_6975421 := by exact prefixLift 6975421
  have htrace : WordTrace (prefixWord ++ tailWord_6975421) baseStart_6975421 baseEnd_6975421 := by
    simpa [prefixWord, tailWord_6975421, baseEnd_6975421] using wordTrace_append hprefix tailTrace_6975421
  have hstable : (prefixWord ++ tailWord_6975421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6975421).length < 2 ^ (prefixWord ++ tailWord_6975421).sum := by decide
  have hdescent : baseEnd_6975421 < baseStart_6975421 := by decide
  rcases family_descends (prefixWord ++ tailWord_6975421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6975438 : List Nat := [4, 1, 1, 1, 2, 2, 3, 4, 1, 2, 2]
def baseStart_6975438 : Nat := 118140960795 + 6975438 * 2 ^ 59
def prefixEnd_6975438 : Nat := 4983230072969 + 3 ^ 40 * 6975438 * 2
def baseEnd_6975438 : Nat := 3581752469636984800445551

theorem tailTrace_6975438 : CollatzResearch.WordTrace tailWord_6975438 prefixEnd_6975438 3581752469636984800445551 := by
  unfold tailWord_6975438
  simp only [CollatzResearch.WordTrace]
  refine ⟨31801890612898363851309871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 169610083268791273873652645 31801890612898363851309871)
  ·
    refine ⟨47702835919347545776964807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31801890612898363851309871 47702835919347545776964807)
    ·
      refine ⟨71554253879021318665447211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47702835919347545776964807 71554253879021318665447211)
      ·
        refine ⟨107331380818531977998170817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71554253879021318665447211 107331380818531977998170817)
        ·
          refine ⟨80498535613898983498628113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107331380818531977998170817 80498535613898983498628113)
          ·
            refine ⟨60373901710424237623971085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80498535613898983498628113 60373901710424237623971085)
            ·
              refine ⟨22640213141409089108989157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60373901710424237623971085 22640213141409089108989157)
              ·
                refine ⟨4245039964014204207935467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22640213141409089108989157 4245039964014204207935467)
                ·
                  refine ⟨6367559946021306311903201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4245039964014204207935467 6367559946021306311903201)
                  ·
                    refine ⟨4775669959515979733927401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6367559946021306311903201 4775669959515979733927401)
                    ·
                      refine ⟨3581752469636984800445551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4775669959515979733927401 3581752469636984800445551)
                      ·
                        rfl

theorem cell23_6975438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 4, 1, 2, 2].length) (baseStart_6975438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6975438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6975438 prefixEnd_6975438 := by exact prefixLift 6975438
  have htrace : WordTrace (prefixWord ++ tailWord_6975438) baseStart_6975438 baseEnd_6975438 := by
    simpa [prefixWord, tailWord_6975438, baseEnd_6975438] using wordTrace_append hprefix tailTrace_6975438
  have hstable : (prefixWord ++ tailWord_6975438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6975438).length < 2 ^ (prefixWord ++ tailWord_6975438).sum := by decide
  have hdescent : baseEnd_6975438 < baseStart_6975438 := by decide
  rcases family_descends (prefixWord ++ tailWord_6975438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6975440 : List Nat := [2, 1, 1, 1, 1, 2, 5, 1, 2, 7]
def baseStart_6975440 : Nat := 118140960795 + 6975440 * 2 ^ 59
def prefixEnd_6975440 : Nat := 4983230072969 + 3 ^ 40 * 6975440 * 2
def baseEnd_6975440 : Nat := 1193917832199431264206847

theorem tailTrace_6975440 : CollatzResearch.WordTrace tailWord_6975440 prefixEnd_6975440 1193917832199431264206847 := by
  unfold tailWord_6975440
  simp only [CollatzResearch.WordTrace]
  refine ⟨127207598924589832576025887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169610131899453110101367849 127207598924589832576025887)
  ·
    refine ⟨190811398386884748864038831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127207598924589832576025887 190811398386884748864038831)
    ·
      refine ⟨286217097580327123296058247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190811398386884748864038831 286217097580327123296058247)
      ·
        refine ⟨429325646370490684944087371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286217097580327123296058247 429325646370490684944087371)
        ·
          refine ⟨643988469555736027416131057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 429325646370490684944087371 643988469555736027416131057)
          ·
            refine ⟨482991352166802020562098293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 643988469555736027416131057 482991352166802020562098293)
            ·
              refine ⟨45280439265637689427696715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 482991352166802020562098293 45280439265637689427696715)
              ·
                refine ⟨67920658898456534141545073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45280439265637689427696715 67920658898456534141545073)
                ·
                  refine ⟨50940494173842400606158805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67920658898456534141545073 50940494173842400606158805)
                  ·
                    refine ⟨1193917832199431264206847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50940494173842400606158805 1193917832199431264206847)
                    ·
                      rfl

theorem cell23_6975440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 1, 2, 7].length) (baseStart_6975440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6975440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6975440 prefixEnd_6975440 := by exact prefixLift 6975440
  have htrace : WordTrace (prefixWord ++ tailWord_6975440) baseStart_6975440 baseEnd_6975440 := by
    simpa [prefixWord, tailWord_6975440, baseEnd_6975440] using wordTrace_append hprefix tailTrace_6975440
  have hstable : (prefixWord ++ tailWord_6975440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6975440).length < 2 ^ (prefixWord ++ tailWord_6975440).sum := by decide
  have hdescent : baseEnd_6975440 < baseStart_6975440 := by decide
  rcases family_descends (prefixWord ++ tailWord_6975440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6975481 : List Nat := [1, 2, 1, 3, 1, 5, 1, 3, 1, 3, 2]
def baseStart_6975481 : Nat := 118140960795 + 6975481 * 2 ^ 59
def prefixEnd_6975481 : Nat := 4983230072969 + 3 ^ 40 * 6975481 * 2
def baseEnd_6975481 : Nat := 3581774549305128132207853

theorem tailTrace_6975481 : CollatzResearch.WordTrace tailWord_6975481 prefixEnd_6975481 3581774549305128132207853 := by
  unfold tailWord_6975481
  simp only [CollatzResearch.WordTrace]
  refine ⟨254416693242031129154294297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169611128828020752769529531 254416693242031129154294297)
  ·
    refine ⟨190812519931523346865720723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254416693242031129154294297 190812519931523346865720723)
    ·
      refine ⟨286218779897285020298581085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190812519931523346865720723 286218779897285020298581085)
      ·
        refine ⟨107332042461481882611967907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 286218779897285020298581085 107332042461481882611967907)
        ·
          refine ⟨160998063692222823917951861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107332042461481882611967907 160998063692222823917951861)
          ·
            refine ⟨15093568471145889742307987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 160998063692222823917951861 15093568471145889742307987)
            ·
              refine ⟨22640352706718834613461981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15093568471145889742307987 22640352706718834613461981)
              ·
                refine ⟨8490132265019562980048243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22640352706718834613461981 8490132265019562980048243)
                ·
                  refine ⟨12735198397529344470072365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8490132265019562980048243 12735198397529344470072365)
                  ·
                    refine ⟨4775699399073504176277137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12735198397529344470072365 4775699399073504176277137)
                    ·
                      refine ⟨3581774549305128132207853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4775699399073504176277137 3581774549305128132207853)
                      ·
                        rfl

theorem cell23_6975481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 3, 1, 3, 2].length) (baseStart_6975481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6975481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6975481 prefixEnd_6975481 := by exact prefixLift 6975481
  have htrace : WordTrace (prefixWord ++ tailWord_6975481) baseStart_6975481 baseEnd_6975481 := by
    simpa [prefixWord, tailWord_6975481, baseEnd_6975481] using wordTrace_append hprefix tailTrace_6975481
  have hstable : (prefixWord ++ tailWord_6975481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6975481).length < 2 ^ (prefixWord ++ tailWord_6975481).sum := by decide
  have hdescent : baseEnd_6975481 < baseStart_6975481 := by decide
  rcases family_descends (prefixWord ++ tailWord_6975481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6975507 : List Nat := [1, 1, 1, 2, 1, 4, 4, 1, 2, 2, 4]
def baseStart_6975507 : Nat := 118140960795 + 6975507 * 2 ^ 59
def prefixEnd_6975507 : Nat := 4983230072969 + 3 ^ 40 * 6975507 * 2
def baseEnd_6975507 : Nat := 3581787899802145030482733

theorem tailTrace_6975507 : CollatzResearch.WordTrace tailWord_6975507 prefixEnd_6975507 3581787899802145030482733 := by
  unfold tailWord_6975507
  simp only [CollatzResearch.WordTrace]
  refine ⟨254417641539936935594740775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169611761026624623729827183 254417641539936935594740775)
  ·
    refine ⟨381626462309905403392111163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254417641539936935594740775 381626462309905403392111163)
    ·
      refine ⟨572439693464858105088166745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 381626462309905403392111163 572439693464858105088166745)
      ·
        refine ⟨429329770098643578816125059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 572439693464858105088166745 429329770098643578816125059)
        ·
          refine ⟨643994655147965368224187589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 429329770098643578816125059 643994655147965368224187589)
          ·
            refine ⟨120748997840243506542035173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 643994655147965368224187589 120748997840243506542035173)
            ·
              refine ⟨22640437095045657476631595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 120748997840243506542035173 22640437095045657476631595)
              ·
                refine ⟨33960655642568486214947393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22640437095045657476631595 33960655642568486214947393)
                ·
                  refine ⟨25470491731926364661210545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33960655642568486214947393 25470491731926364661210545)
                  ·
                    refine ⟨19102868798944773495907909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25470491731926364661210545 19102868798944773495907909)
                    ·
                      refine ⟨3581787899802145030482733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19102868798944773495907909 3581787899802145030482733)
                      ·
                        rfl

theorem cell23_6975507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 1, 2, 2, 4].length) (baseStart_6975507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6975507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6975507 prefixEnd_6975507 := by exact prefixLift 6975507
  have htrace : WordTrace (prefixWord ++ tailWord_6975507) baseStart_6975507 baseEnd_6975507 := by
    simpa [prefixWord, tailWord_6975507, baseEnd_6975507] using wordTrace_append hprefix tailTrace_6975507
  have hstable : (prefixWord ++ tailWord_6975507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6975507).length < 2 ^ (prefixWord ++ tailWord_6975507).sum := by decide
  have hdescent : baseEnd_6975507 < baseStart_6975507 := by decide
  rcases family_descends (prefixWord ++ tailWord_6975507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6975547 : List Nat := [1, 1, 1, 1, 1, 2, 1, 8, 2, 5]
def baseStart_6975547 : Nat := 118140960795 + 6975547 * 2 ^ 59
def prefixEnd_6975547 : Nat := 4983230072969 + 3 ^ 40 * 6975547 * 2
def baseEnd_6975547 : Nat := 1193936146342774957994183

theorem tailTrace_6975547 : CollatzResearch.WordTrace tailWord_6975547 prefixEnd_6975547 1193936146342774957994183 := by
  unfold tailWord_6975547
  simp only [CollatzResearch.WordTrace]
  refine ⟨254419100459792022426196895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169612733639861348284131263 254419100459792022426196895)
  ·
    refine ⟨381628650689688033639295343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254419100459792022426196895 381628650689688033639295343)
    ·
      refine ⟨572442976034532050458943015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 381628650689688033639295343 572442976034532050458943015)
      ·
        refine ⟨858664464051798075688414523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 572442976034532050458943015 858664464051798075688414523)
        ·
          refine ⟨1287996696077697113532621785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 858664464051798075688414523 1287996696077697113532621785)
          ·
            refine ⟨965997522058272835149466339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1287996696077697113532621785 965997522058272835149466339)
            ·
              refine ⟨1448996283087409252724199509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 965997522058272835149466339 1448996283087409252724199509)
              ·
                refine ⟨16980425192430577180361713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1448996283087409252724199509 16980425192430577180361713)
                ·
                  refine ⟨12735318894322932885271285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16980425192430577180361713 12735318894322932885271285)
                  ·
                    refine ⟨1193936146342774957994183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12735318894322932885271285 1193936146342774957994183)
                    ·
                      rfl

theorem cell23_6975547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 8, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 8, 2, 5].length) (baseStart_6975547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6975547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6975547 prefixEnd_6975547 := by exact prefixLift 6975547
  have htrace : WordTrace (prefixWord ++ tailWord_6975547) baseStart_6975547 baseEnd_6975547 := by
    simpa [prefixWord, tailWord_6975547, baseEnd_6975547] using wordTrace_append hprefix tailTrace_6975547
  have hstable : (prefixWord ++ tailWord_6975547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6975547).length < 2 ^ (prefixWord ++ tailWord_6975547).sum := by decide
  have hdescent : baseEnd_6975547 < baseStart_6975547 := by decide
  rcases family_descends (prefixWord ++ tailWord_6975547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6975581 : List Nat := [1, 4, 4, 1, 1, 1, 1, 3, 2, 5]
def baseStart_6975581 : Nat := 118140960795 + 6975581 * 2 ^ 59
def prefixEnd_6975581 : Nat := 4983230072969 + 3 ^ 40 * 6975581 * 2
def baseEnd_6975581 : Nat := 1193941965790192580319131

theorem tailTrace_6975581 : CollatzResearch.WordTrace tailWord_6975581 prefixEnd_6975581 1193941965790192580319131 := by
  unfold tailWord_6975581
  simp only [CollatzResearch.WordTrace]
  refine ⟨254420340541668846232934597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169613560361112564155289731 254420340541668846232934597)
  ·
    refine ⟨47703813851562908668675237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 254420340541668846232934597 47703813851562908668675237)
    ·
      refine ⟨8944465097168045375376607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47703813851562908668675237 8944465097168045375376607)
      ·
        refine ⟨13416697645752068063064911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8944465097168045375376607 13416697645752068063064911)
        ·
          refine ⟨20125046468628102094597367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13416697645752068063064911 20125046468628102094597367)
          ·
            refine ⟨30187569702942153141896051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20125046468628102094597367 30187569702942153141896051)
            ·
              refine ⟨45281354554413229712844077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30187569702942153141896051 45281354554413229712844077)
              ·
                refine ⟨16980507957904961142316529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45281354554413229712844077 16980507957904961142316529)
                ·
                  refine ⟨12735380968428720856737397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16980507957904961142316529 12735380968428720856737397)
                  ·
                    refine ⟨1193941965790192580319131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12735380968428720856737397 1193941965790192580319131)
                    ·
                      rfl

theorem cell23_6975581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_6975581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6975581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6975581 prefixEnd_6975581 := by exact prefixLift 6975581
  have htrace : WordTrace (prefixWord ++ tailWord_6975581) baseStart_6975581 baseEnd_6975581 := by
    simpa [prefixWord, tailWord_6975581, baseEnd_6975581] using wordTrace_append hprefix tailTrace_6975581
  have hstable : (prefixWord ++ tailWord_6975581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6975581).length < 2 ^ (prefixWord ++ tailWord_6975581).sum := by decide
  have hdescent : baseEnd_6975581 < baseStart_6975581 := by decide
  rcases family_descends (prefixWord ++ tailWord_6975581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6975584 : List Nat := [2, 1, 1, 3, 2, 3, 1, 3, 2, 1, 4]
def baseStart_6975584 : Nat := 118140960795 + 6975584 * 2 ^ 59
def prefixEnd_6975584 : Nat := 4983230072969 + 3 ^ 40 * 6975584 * 2
def baseEnd_6975584 : Nat := 3581827437812541229219879

theorem tailTrace_6975584 : CollatzResearch.WordTrace tailWord_6975584 prefixEnd_6975584 3581827437812541229219879 := by
  unfold tailWord_6975584
  simp only [CollatzResearch.WordTrace]
  refine ⟨127210224980328988872646903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169613633307105318496862537 127210224980328988872646903)
  ·
    refine ⟨190815337470493483308970355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127210224980328988872646903 190815337470493483308970355)
    ·
      refine ⟨286223006205740224963455533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190815337470493483308970355 286223006205740224963455533)
      ·
        refine ⟨107333627327152584361295825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 286223006205740224963455533 107333627327152584361295825)
        ·
          refine ⟨80500220495364438270971869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107333627327152584361295825 80500220495364438270971869)
          ·
            refine ⟨30187582685761664351614451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80500220495364438270971869 30187582685761664351614451)
            ·
              refine ⟨45281374028642496527421677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30187582685761664351614451 45281374028642496527421677)
              ·
                refine ⟨16980515260740936197783129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45281374028642496527421677 16980515260740936197783129)
                ·
                  refine ⟨12735386445555702148337347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16980515260740936197783129 12735386445555702148337347)
                  ·
                    refine ⟨19103079668333553222506021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12735386445555702148337347 19103079668333553222506021)
                    ·
                      refine ⟨3581827437812541229219879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19103079668333553222506021 3581827437812541229219879)
                      ·
                        rfl

theorem cell23_6975584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 3, 2, 1, 4].length) (baseStart_6975584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6975584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6975584 prefixEnd_6975584 := by exact prefixLift 6975584
  have htrace : WordTrace (prefixWord ++ tailWord_6975584) baseStart_6975584 baseEnd_6975584 := by
    simpa [prefixWord, tailWord_6975584, baseEnd_6975584] using wordTrace_append hprefix tailTrace_6975584
  have hstable : (prefixWord ++ tailWord_6975584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6975584).length < 2 ^ (prefixWord ++ tailWord_6975584).sum := by decide
  have hdescent : baseEnd_6975584 < baseStart_6975584 := by decide
  rcases family_descends (prefixWord ++ tailWord_6975584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6975674 : List Nat := [3, 1, 1, 1, 2, 2, 2, 1, 5, 1, 4]
def baseStart_6975674 : Nat := 118140960795 + 6975674 * 2 ^ 59
def prefixEnd_6975674 : Nat := 4983230072969 + 3 ^ 40 * 6975674 * 2
def baseEnd_6975674 : Nat := 3581873651071445877094465

theorem tailTrace_6975674 : CollatzResearch.WordTrace tailWord_6975674 prefixEnd_6975674 3581873651071445877094465 := by
  unfold tailWord_6975674
  simp only [CollatzResearch.WordTrace]
  refine ⟨63605933132582980779017519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169615821686887948744046717 63605933132582980779017519)
  ·
    refine ⟨95408899698874471168526279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63605933132582980779017519 95408899698874471168526279)
    ·
      refine ⟨143113349548311706752789419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95408899698874471168526279 143113349548311706752789419)
      ·
        refine ⟨214670024322467560129184129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143113349548311706752789419 214670024322467560129184129)
        ·
          refine ⟨161002518241850670096888097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 214670024322467560129184129 161002518241850670096888097)
          ·
            refine ⟨120751888681388002572666073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161002518241850670096888097 120751888681388002572666073)
            ·
              refine ⟨90563916511041001929499555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120751888681388002572666073 90563916511041001929499555)
              ·
                refine ⟨135845874766561502894249333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90563916511041001929499555 135845874766561502894249333)
                ·
                  refine ⟨12735550759365140896335875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 135845874766561502894249333 12735550759365140896335875)
                  ·
                    refine ⟨19103326139047711344503813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12735550759365140896335875 19103326139047711344503813)
                    ·
                      refine ⟨3581873651071445877094465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19103326139047711344503813 3581873651071445877094465)
                      ·
                        rfl

theorem cell23_6975674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 1, 5, 1, 4].length) (baseStart_6975674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6975674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6975674 prefixEnd_6975674 := by exact prefixLift 6975674
  have htrace : WordTrace (prefixWord ++ tailWord_6975674) baseStart_6975674 baseEnd_6975674 := by
    simpa [prefixWord, tailWord_6975674, baseEnd_6975674] using wordTrace_append hprefix tailTrace_6975674
  have hstable : (prefixWord ++ tailWord_6975674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6975674).length < 2 ^ (prefixWord ++ tailWord_6975674).sum := by decide
  have hdescent : baseEnd_6975674 < baseStart_6975674 := by decide
  rcases family_descends (prefixWord ++ tailWord_6975674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6975691 : List Nat := [1, 1, 1, 1, 3, 2, 6, 2, 1, 1, 4]
def baseStart_6975691 : Nat := 118140960795 + 6975691 * 2 ^ 59
def prefixEnd_6975691 : Nat := 4983230072969 + 3 ^ 40 * 6975691 * 2
def baseEnd_6975691 : Nat := 3581882380242572310581887

theorem tailTrace_6975691 : CollatzResearch.WordTrace tailWord_6975691 prefixEnd_6975691 3581882380242572310581887 := by
  unfold tailWord_6975691
  simp only [CollatzResearch.WordTrace]
  refine ⟨254424352571270335019438927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169616235047513556679625951 254424352571270335019438927)
  ·
    refine ⟨381636528856905502529158391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254424352571270335019438927 381636528856905502529158391)
    ·
      refine ⟨572454793285358253793737587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 381636528856905502529158391 572454793285358253793737587)
      ·
        refine ⟨858682189928037380690606381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 572454793285358253793737587 858682189928037380690606381)
        ·
          refine ⟨322005821223014017758977393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 858682189928037380690606381 322005821223014017758977393)
          ·
            refine ⟨241504365917260513319233045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 322005821223014017758977393 241504365917260513319233045)
            ·
              refine ⟨11320517152371586561839049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 241504365917260513319233045 11320517152371586561839049)
              ·
                refine ⟨8490387864278689921379287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11320517152371586561839049 8490387864278689921379287)
                ·
                  refine ⟨12735581796418034882068931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8490387864278689921379287 12735581796418034882068931)
                  ·
                    refine ⟨19103372694627052323103397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12735581796418034882068931 19103372694627052323103397)
                    ·
                      refine ⟨3581882380242572310581887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19103372694627052323103397 3581882380242572310581887)
                      ·
                        rfl

theorem cell23_6975691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 6, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 6, 2, 1, 1, 4].length) (baseStart_6975691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6975691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6975691 prefixEnd_6975691 := by exact prefixLift 6975691
  have htrace : WordTrace (prefixWord ++ tailWord_6975691) baseStart_6975691 baseEnd_6975691 := by
    simpa [prefixWord, tailWord_6975691, baseEnd_6975691] using wordTrace_append hprefix tailTrace_6975691
  have hstable : (prefixWord ++ tailWord_6975691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6975691).length < 2 ^ (prefixWord ++ tailWord_6975691).sum := by decide
  have hdescent : baseEnd_6975691 < baseStart_6975691 := by decide
  rcases family_descends (prefixWord ++ tailWord_6975691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6975754 : List Nat := [3, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5]
def baseStart_6975754 : Nat := 118140960795 + 6975754 * 2 ^ 59
def prefixEnd_6975754 : Nat := 4983230072969 + 3 ^ 40 * 6975754 * 2
def baseEnd_6975754 : Nat := 3581914729523805564094097

theorem tailTrace_6975754 : CollatzResearch.WordTrace tailWord_6975754 prefixEnd_6975754 3581914729523805564094097 := by
  unfold tailWord_6975754
  simp only [CollatzResearch.WordTrace]
  refine ⟨63606662592510524194745579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169617766913361397852654877 63606662592510524194745579)
  ·
    refine ⟨95409993888765786292118369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63606662592510524194745579 95409993888765786292118369)
    ·
      refine ⟨71557495416574339719088777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95409993888765786292118369 71557495416574339719088777)
      ·
        refine ⟨53668121562430754789316583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71557495416574339719088777 53668121562430754789316583)
        ·
          refine ⟨80502182343646132183974875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53668121562430754789316583 80502182343646132183974875)
          ·
            refine ⟨120753273515469198275962313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80502182343646132183974875 120753273515469198275962313)
            ·
              refine ⟨90564955136601898706971735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120753273515469198275962313 90564955136601898706971735)
              ·
                refine ⟨135847432704902848060457603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90564955136601898706971735 135847432704902848060457603)
                ·
                  refine ⟨203771149057354272090686405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 135847432704902848060457603 203771149057354272090686405)
                  ·
                    refine ⟨38207090448253926017003701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 203771149057354272090686405 38207090448253926017003701)
                    ·
                      refine ⟨3581914729523805564094097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38207090448253926017003701 3581914729523805564094097)
                      ·
                        rfl

theorem cell23_6975754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5].length) (baseStart_6975754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6975754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6975754 prefixEnd_6975754 := by exact prefixLift 6975754
  have htrace : WordTrace (prefixWord ++ tailWord_6975754) baseStart_6975754 baseEnd_6975754 := by
    simpa [prefixWord, tailWord_6975754, baseEnd_6975754] using wordTrace_append hprefix tailTrace_6975754
  have hstable : (prefixWord ++ tailWord_6975754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6975754).length < 2 ^ (prefixWord ++ tailWord_6975754).sum := by decide
  have hdescent : baseEnd_6975754 < baseStart_6975754 := by decide
  rcases family_descends (prefixWord ++ tailWord_6975754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6975775 : List Nat := [1, 1, 2, 4, 3, 2, 2, 2, 2, 1, 3]
def baseStart_6975775 : Nat := 118140960795 + 6975775 * 2 ^ 59
def prefixEnd_6975775 : Nat := 4983230072969 + 3 ^ 40 * 6975775 * 2
def baseEnd_6975775 : Nat := 3581925512617549981931501

theorem tailTrace_6975775 : CollatzResearch.WordTrace tailWord_6975775 prefixEnd_6975775 3581925512617549981931501 := by
  unfold tailWord_6975775
  simp only [CollatzResearch.WordTrace]
  refine ⟨254427416302966017365496779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169618277535310678243664519 254427416302966017365496779)
  ·
    refine ⟨381641124454449026048245169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254427416302966017365496779 381641124454449026048245169)
    ·
      refine ⟨286230843340836769536183877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 381641124454449026048245169 286230843340836769536183877)
      ·
        refine ⟨53668283126406894288034477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 286230843340836769536183877 53668283126406894288034477)
        ·
          refine ⟨20125606172402585358012929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53668283126406894288034477 20125606172402585358012929)
          ·
            refine ⟨15094204629301939018509697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20125606172402585358012929 15094204629301939018509697)
            ·
              refine ⟨11320653471976454263882273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15094204629301939018509697 11320653471976454263882273)
              ·
                refine ⟨8490490103982340697911705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11320653471976454263882273 8490490103982340697911705)
                ·
                  refine ⟨6367867577986755523433779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8490490103982340697911705 6367867577986755523433779)
                  ·
                    refine ⟨9551801366980133285150669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6367867577986755523433779 9551801366980133285150669)
                    ·
                      refine ⟨3581925512617549981931501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9551801366980133285150669 3581925512617549981931501)
                      ·
                        rfl

theorem cell23_6975775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 2, 2, 2, 1, 3].length) (baseStart_6975775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6975775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6975775 prefixEnd_6975775 := by exact prefixLift 6975775
  have htrace : WordTrace (prefixWord ++ tailWord_6975775) baseStart_6975775 baseEnd_6975775 := by
    simpa [prefixWord, tailWord_6975775, baseEnd_6975775] using wordTrace_append hprefix tailTrace_6975775
  have hstable : (prefixWord ++ tailWord_6975775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6975775).length < 2 ^ (prefixWord ++ tailWord_6975775).sum := by decide
  have hdescent : baseEnd_6975775 < baseStart_6975775 := by decide
  rcases family_descends (prefixWord ++ tailWord_6975775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6975831 : List Nat := [1, 1, 3, 2, 3, 1, 1, 1, 4, 3, 3]
def baseStart_6975831 : Nat := 118140960795 + 6975831 * 2 ^ 59
def prefixEnd_6975831 : Nat := 4983230072969 + 3 ^ 40 * 6975831 * 2
def baseEnd_6975831 : Nat := 3581954267534201762831243

theorem tailTrace_6975831 : CollatzResearch.WordTrace tailWord_6975831 prefixEnd_6975831 3581954267534201762831243 := by
  unfold tailWord_6975831
  simp only [CollatzResearch.WordTrace]
  refine ⟨254429458790763138929535347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169619639193842092619690231 254429458790763138929535347)
  ·
    refine ⟨381644188186144708394303021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254429458790763138929535347 381644188186144708394303021)
    ·
      refine ⟨143116570569804265647863633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 381644188186144708394303021 143116570569804265647863633)
      ·
        refine ⟨107337427927353199235897725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143116570569804265647863633 107337427927353199235897725)
        ·
          refine ⟨40251535472757449713461647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107337427927353199235897725 40251535472757449713461647)
          ·
            refine ⟨60377303209136174570192471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40251535472757449713461647 60377303209136174570192471)
            ·
              refine ⟨90565954813704261855288707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60377303209136174570192471 90565954813704261855288707)
              ·
                refine ⟨135848932220556392782933061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90565954813704261855288707 135848932220556392782933061)
                ·
                  refine ⟨25471674791354323646799949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 135848932220556392782933061 25471674791354323646799949)
                  ·
                    refine ⟨9551878046757871367549981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25471674791354323646799949 9551878046757871367549981)
                    ·
                      refine ⟨3581954267534201762831243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9551878046757871367549981 3581954267534201762831243)
                      ·
                        rfl

theorem cell23_6975831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 1, 4, 3, 3].length) (baseStart_6975831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6975831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6975831 prefixEnd_6975831 := by exact prefixLift 6975831
  have htrace : WordTrace (prefixWord ++ tailWord_6975831) baseStart_6975831 baseEnd_6975831 := by
    simpa [prefixWord, tailWord_6975831, baseEnd_6975831] using wordTrace_append hprefix tailTrace_6975831
  have hstable : (prefixWord ++ tailWord_6975831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6975831).length < 2 ^ (prefixWord ++ tailWord_6975831).sum := by decide
  have hdescent : baseEnd_6975831 < baseStart_6975831 := by decide
  rcases family_descends (prefixWord ++ tailWord_6975831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6975848 : List Nat := [2, 1, 4, 2, 2, 1, 2, 1, 2, 3, 3]
def baseStart_6975848 : Nat := 118140960795 + 6975848 * 2 ^ 59
def prefixEnd_6975848 : Nat := 4983230072969 + 3 ^ 40 * 6975848 * 2
def baseEnd_6975848 : Nat := 3581962996705328196318665

theorem tailTrace_6975848 : CollatzResearch.WordTrace tailWord_6975848 prefixEnd_6975848 3581962996705328196318665 := by
  unfold tailWord_6975848
  simp only [CollatzResearch.WordTrace]
  refine ⟨127215039415850775416452099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169620052554467700555269465 127215039415850775416452099)
  ·
    refine ⟨190822559123776163124678149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127215039415850775416452099 190822559123776163124678149)
    ·
      refine ⟨35779229835708030585877153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 190822559123776163124678149 35779229835708030585877153)
      ·
        refine ⟨26834422376781022939407865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35779229835708030585877153 26834422376781022939407865)
        ·
          refine ⟨20125816782585767204555899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26834422376781022939407865 20125816782585767204555899)
          ·
            refine ⟨30188725173878650806833849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20125816782585767204555899 30188725173878650806833849)
            ·
              refine ⟨22641543880408988105125387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30188725173878650806833849 22641543880408988105125387)
              ·
                refine ⟨33962315820613482157688081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22641543880408988105125387 33962315820613482157688081)
                ·
                  refine ⟨25471736865460111618266061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33962315820613482157688081 25471736865460111618266061)
                  ·
                    refine ⟨9551901324547541856849773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25471736865460111618266061 9551901324547541856849773)
                    ·
                      refine ⟨3581962996705328196318665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9551901324547541856849773 3581962996705328196318665)
                      ·
                        rfl

theorem cell23_6975848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 1, 2, 3, 3].length) (baseStart_6975848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6975848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6975848 prefixEnd_6975848 := by exact prefixLift 6975848
  have htrace : WordTrace (prefixWord ++ tailWord_6975848) baseStart_6975848 baseEnd_6975848 := by
    simpa [prefixWord, tailWord_6975848, baseEnd_6975848] using wordTrace_append hprefix tailTrace_6975848
  have hstable : (prefixWord ++ tailWord_6975848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6975848).length < 2 ^ (prefixWord ++ tailWord_6975848).sum := by decide
  have hdescent : baseEnd_6975848 < baseStart_6975848 := by decide
  rcases family_descends (prefixWord ++ tailWord_6975848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6975965 : List Nat := [1, 4, 3, 1, 1, 1, 2, 2, 1, 5, 2]
def baseStart_6975965 : Nat := 118140960795 + 6975965 * 2 ^ 59
def prefixEnd_6975965 : Nat := 4983230072969 + 3 ^ 40 * 6975965 * 2
def baseEnd_6975965 : Nat := 3582023073941904238555627

theorem tailTrace_6975965 : CollatzResearch.WordTrace tailWord_6975965 prefixEnd_6975965 3582023073941904238555627 := by
  unfold tailWord_6975965
  simp only [CollatzResearch.WordTrace]
  refine ⟨254434346172277679814913349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169622897448185119876608899 254434346172277679814913349)
  ·
    refine ⟨47706439907302064965296253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 254434346172277679814913349 47706439907302064965296253)
    ·
      refine ⟨17889914965238274361986095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47706439907302064965296253 17889914965238274361986095)
      ·
        refine ⟨26834872447857411542979143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17889914965238274361986095 26834872447857411542979143)
        ·
          refine ⟨40252308671786117314468715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26834872447857411542979143 40252308671786117314468715)
          ·
            refine ⟨60378463007679175971703073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40252308671786117314468715 60378463007679175971703073)
            ·
              refine ⟨45283847255759381978777305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60378463007679175971703073 45283847255759381978777305)
              ·
                refine ⟨33962885441819536484082979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45283847255759381978777305 33962885441819536484082979)
                ·
                  refine ⟨50944328162729304726124469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33962885441819536484082979 50944328162729304726124469)
                  ·
                    refine ⟨4776030765255872318074169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50944328162729304726124469 4776030765255872318074169)
                    ·
                      refine ⟨3582023073941904238555627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4776030765255872318074169 3582023073941904238555627)
                      ·
                        rfl

theorem cell23_6975965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 2, 1, 5, 2].length) (baseStart_6975965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6975965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6975965 prefixEnd_6975965 := by exact prefixLift 6975965
  have htrace : WordTrace (prefixWord ++ tailWord_6975965) baseStart_6975965 baseEnd_6975965 := by
    simpa [prefixWord, tailWord_6975965, baseEnd_6975965] using wordTrace_append hprefix tailTrace_6975965
  have hstable : (prefixWord ++ tailWord_6975965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6975965).length < 2 ^ (prefixWord ++ tailWord_6975965).sum := by decide
  have hdescent : baseEnd_6975965 < baseStart_6975965 := by decide
  rcases family_descends (prefixWord ++ tailWord_6975965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6975982 : List Nat := [4, 1, 2, 1, 2, 2, 3, 1, 2, 3, 2]
def baseStart_6975982 : Nat := 118140960795 + 6975982 * 2 ^ 59
def prefixEnd_6975982 : Nat := 4983230072969 + 3 ^ 40 * 6975982 * 2
def baseEnd_6975982 : Nat := 3582031803113030672043049

theorem tailTrace_6975982 : CollatzResearch.WordTrace tailWord_6975982 prefixEnd_6975982 3582031803113030672043049 := by
  unfold tailWord_6975982
  simp only [CollatzResearch.WordTrace]
  refine ⟨31804370776652011464785275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 169623310808810727812188133 31804370776652011464785275)
  ·
    refine ⟨47706556164978017197177913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31804370776652011464785275 47706556164978017197177913)
    ·
      refine ⟨35779917123733512897883435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47706556164978017197177913 35779917123733512897883435)
      ·
        refine ⟨53669875685600269346825153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35779917123733512897883435 53669875685600269346825153)
        ·
          refine ⟨40252406764200202010118865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53669875685600269346825153 40252406764200202010118865)
          ·
            refine ⟨30189305073150151507589149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40252406764200202010118865 30189305073150151507589149)
            ·
              refine ⟨11320989402431306815345931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30189305073150151507589149 11320989402431306815345931)
              ·
                refine ⟨16981484103646960223018897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11320989402431306815345931 16981484103646960223018897)
                ·
                  refine ⟨12736113077735220167264173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16981484103646960223018897 12736113077735220167264173)
                  ·
                    refine ⟨4776042404150707562724065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12736113077735220167264173 4776042404150707562724065)
                    ·
                      refine ⟨3582031803113030672043049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4776042404150707562724065 3582031803113030672043049)
                      ·
                        rfl

theorem cell23_6975982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 3, 1, 2, 3, 2].length) (baseStart_6975982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6975982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6975982 prefixEnd_6975982 := by exact prefixLift 6975982
  have htrace : WordTrace (prefixWord ++ tailWord_6975982) baseStart_6975982 baseEnd_6975982 := by
    simpa [prefixWord, tailWord_6975982, baseEnd_6975982] using wordTrace_append hprefix tailTrace_6975982
  have hstable : (prefixWord ++ tailWord_6975982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6975982).length < 2 ^ (prefixWord ++ tailWord_6975982).sum := by decide
  have hdescent : baseEnd_6975982 < baseStart_6975982 := by decide
  rcases family_descends (prefixWord ++ tailWord_6975982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6975991 : List Nat := [1, 1, 3, 1, 1, 1, 1, 2, 2, 6, 4]
def baseStart_6975991 : Nat := 118140960795 + 6975991 * 2 ^ 59
def prefixEnd_6975991 : Nat := 4983230072969 + 3 ^ 40 * 6975991 * 2
def baseEnd_6975991 : Nat := 3582036424438921136830507

theorem tailTrace_6975991 : CollatzResearch.WordTrace tailWord_6975991 prefixEnd_6975991 3582036424438921136830507 := by
  unfold tailWord_6975991
  simp only [CollatzResearch.WordTrace]
  refine ⟨254435294470183486255359827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169623529646788990836906551 254435294470183486255359827)
  ·
    refine ⟨381652941705275229383039741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254435294470183486255359827 381652941705275229383039741)
    ·
      refine ⟨143119853139478211018639903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 381652941705275229383039741 143119853139478211018639903)
      ·
        refine ⟨214679779709217316527959855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143119853139478211018639903 214679779709217316527959855)
        ·
          refine ⟨322019669563825974791939783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214679779709217316527959855 322019669563825974791939783)
          ·
            refine ⟨483029504345738962187909675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 322019669563825974791939783 483029504345738962187909675)
            ·
              refine ⟨724544256518608443281864513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 483029504345738962187909675 724544256518608443281864513)
              ·
                refine ⟨543408192388956332461398385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 724544256518608443281864513 543408192388956332461398385)
                ·
                  refine ⟨407556144291717249346048789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 543408192388956332461398385 407556144291717249346048789)
                  ·
                    refine ⟨19104194263674246063096037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 407556144291717249346048789 19104194263674246063096037)
                    ·
                      refine ⟨3582036424438921136830507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19104194263674246063096037 3582036424438921136830507)
                      ·
                        rfl

theorem cell23_6975991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 6, 4].length) (baseStart_6975991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6975991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6975991 prefixEnd_6975991 := by exact prefixLift 6975991
  have htrace : WordTrace (prefixWord ++ tailWord_6975991) baseStart_6975991 baseEnd_6975991 := by
    simpa [prefixWord, tailWord_6975991, baseEnd_6975991] using wordTrace_append hprefix tailTrace_6975991
  have hstable : (prefixWord ++ tailWord_6975991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6975991).length < 2 ^ (prefixWord ++ tailWord_6975991).sum := by decide
  have hdescent : baseEnd_6975991 < baseStart_6975991 := by decide
  rcases family_descends (prefixWord ++ tailWord_6975991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6976005 : List Nat := [1, 3, 1, 1, 2, 2, 5, 2, 2, 4]
def baseStart_6976005 : Nat := 118140960795 + 6976005 * 2 ^ 59
def prefixEnd_6976005 : Nat := 4983230072969 + 3 ^ 40 * 6976005 * 2
def baseEnd_6976005 : Nat := 1194014537722694694018481

theorem tailTrace_6976005 : CollatzResearch.WordTrace tailWord_6976005 prefixEnd_6976005 1194014537722694694018481 := by
  unfold tailWord_6976005
  simp only [CollatzResearch.WordTrace]
  refine ⟨254435805092132766646369469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169623870061421844430912979 254435805092132766646369469)
  ·
    refine ⟨95413426909549787492388551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 254435805092132766646369469 95413426909549787492388551)
    ·
      refine ⟨143120140364324681238582827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95413426909549787492388551 143120140364324681238582827)
      ·
        refine ⟨214680210546487021857874241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143120140364324681238582827 214680210546487021857874241)
        ·
          refine ⟨161010157909865266393405681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 214680210546487021857874241 161010157909865266393405681)
          ·
            refine ⟨120757618432398949795054261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161010157909865266393405681 120757618432398949795054261)
            ·
              refine ⟨11321026728037401543286337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 120757618432398949795054261 11321026728037401543286337)
              ·
                refine ⟨8490770046028051157464753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11321026728037401543286337 8490770046028051157464753)
                ·
                  refine ⟨6368077534521038368098565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8490770046028051157464753 6368077534521038368098565)
                  ·
                    refine ⟨1194014537722694694018481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6368077534521038368098565 1194014537722694694018481)
                    ·
                      rfl

theorem cell23_6976005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 5, 2, 2, 4].length) (baseStart_6976005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6976005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6976005 prefixEnd_6976005 := by exact prefixLift 6976005
  have htrace : WordTrace (prefixWord ++ tailWord_6976005) baseStart_6976005 baseEnd_6976005 := by
    simpa [prefixWord, tailWord_6976005, baseEnd_6976005] using wordTrace_append hprefix tailTrace_6976005
  have hstable : (prefixWord ++ tailWord_6976005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6976005).length < 2 ^ (prefixWord ++ tailWord_6976005).sum := by decide
  have hdescent : baseEnd_6976005 < baseStart_6976005 := by decide
  rcases family_descends (prefixWord ++ tailWord_6976005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6976006 : List Nat := [6, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3]
def baseStart_6976006 : Nat := 118140960795 + 6976006 * 2 ^ 59
def prefixEnd_6976006 : Nat := 4983230072969 + 3 ^ 40 * 6976006 * 2
def baseEnd_6976006 : Nat := 3582044126648738578142939

theorem tailTrace_6976006 : CollatzResearch.WordTrace tailWord_6976006 prefixEnd_6976006 3582044126648738578142939 := by
  unfold tailWord_6976006
  simp only [CollatzResearch.WordTrace]
  refine ⟨7951120048910285744286121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 169623894376752762544770581 7951120048910285744286121)
  ·
    refine ⟨5963340036682714308214591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7951120048910285744286121 5963340036682714308214591)
    ·
      refine ⟨8945010055024071462321887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5963340036682714308214591 8945010055024071462321887)
      ·
        refine ⟨13417515082536107193482831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8945010055024071462321887 13417515082536107193482831)
        ·
          refine ⟨20126272623804160790224247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13417515082536107193482831 20126272623804160790224247)
          ·
            refine ⟨30189408935706241185336371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20126272623804160790224247 30189408935706241185336371)
            ·
              refine ⟨45284113403559361778004557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30189408935706241185336371 45284113403559361778004557)
              ·
                refine ⟨16981542526334760666751709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45284113403559361778004557 16981542526334760666751709)
                ·
                  refine ⟨6368078447375535250031891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16981542526334760666751709 6368078447375535250031891)
                  ·
                    refine ⟨9552117671063302875047837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6368078447375535250031891 9552117671063302875047837)
                    ·
                      refine ⟨3582044126648738578142939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9552117671063302875047837 3582044126648738578142939)
                      ·
                        rfl

theorem cell23_6976006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_6976006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6976006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6976006 prefixEnd_6976006 := by exact prefixLift 6976006
  have htrace : WordTrace (prefixWord ++ tailWord_6976006) baseStart_6976006 baseEnd_6976006 := by
    simpa [prefixWord, tailWord_6976006, baseEnd_6976006] using wordTrace_append hprefix tailTrace_6976006
  have hstable : (prefixWord ++ tailWord_6976006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6976006).length < 2 ^ (prefixWord ++ tailWord_6976006).sum := by decide
  have hdescent : baseEnd_6976006 < baseStart_6976006 := by decide
  rcases family_descends (prefixWord ++ tailWord_6976006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6976012 : List Nat := [2, 2, 1, 2, 4, 1, 1, 3, 3, 2, 2]
def baseStart_6976012 : Nat := 118140960795 + 6976012 * 2 ^ 59
def prefixEnd_6976012 : Nat := 4983230072969 + 3 ^ 40 * 6976012 * 2
def baseEnd_6976012 : Nat := 3582047207532665554667911

theorem tailTrace_6976012 : CollatzResearch.WordTrace tailWord_6976012 prefixEnd_6976012 3582047207532665554667911 := by
  unfold tailWord_6976012
  simp only [CollatzResearch.WordTrace]
  refine ⟨127218030201553703420937145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169624040268738271227916193 127218030201553703420937145)
  ·
    refine ⟨95413522651165277565702859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127218030201553703420937145 95413522651165277565702859)
    ·
      refine ⟨143120283976747916348554289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95413522651165277565702859 143120283976747916348554289)
      ·
        refine ⟨107340212982560937261415717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143120283976747916348554289 107340212982560937261415717)
        ·
          refine ⟨20126289934230175736515447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 107340212982560937261415717 20126289934230175736515447)
          ·
            refine ⟨30189434901345263604773171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20126289934230175736515447 30189434901345263604773171)
            ·
              refine ⟨45284152352017895407159757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30189434901345263604773171 45284152352017895407159757)
              ·
                refine ⟨16981557132006710777684909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45284152352017895407159757 16981557132006710777684909)
                ·
                  refine ⟨6368083924502516541631841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16981557132006710777684909 6368083924502516541631841)
                  ·
                    refine ⟨4776062943376887406223881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6368083924502516541631841 4776062943376887406223881)
                    ·
                      refine ⟨3582047207532665554667911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4776062943376887406223881 3582047207532665554667911)
                      ·
                        rfl

theorem cell23_6976012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 3, 3, 2, 2].length) (baseStart_6976012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6976012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6976012 prefixEnd_6976012 := by exact prefixLift 6976012
  have htrace : WordTrace (prefixWord ++ tailWord_6976012) baseStart_6976012 baseEnd_6976012 := by
    simpa [prefixWord, tailWord_6976012, baseEnd_6976012] using wordTrace_append hprefix tailTrace_6976012
  have hstable : (prefixWord ++ tailWord_6976012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6976012).length < 2 ^ (prefixWord ++ tailWord_6976012).sum := by decide
  have hdescent : baseEnd_6976012 < baseStart_6976012 := by decide
  rcases family_descends (prefixWord ++ tailWord_6976012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6976035 : List Nat := [1, 1, 1, 4, 4, 3, 2, 7]
def baseStart_6976035 : Nat := 118140960795 + 6976035 * 2 ^ 59
def prefixEnd_6976035 : Nat := 4983230072969 + 3 ^ 40 * 6976035 * 2
def baseEnd_6976035 : Nat := 132668852503248850543715

theorem tailTrace_6976035 : CollatzResearch.WordTrace tailWord_6976035 prefixEnd_6976035 132668852503248850543715 := by
  unfold tailWord_6976035
  simp only [CollatzResearch.WordTrace]
  refine ⟨254436899282024081769961559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169624599521349387846641039 254436899282024081769961559)
  ·
    refine ⟨381655348923036122654942339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254436899282024081769961559 381655348923036122654942339)
    ·
      refine ⟨572483023384554183982413509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 381655348923036122654942339 572483023384554183982413509)
      ·
        refine ⟨107340566884603909496702533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 572483023384554183982413509 107340566884603909496702533)
        ·
          refine ⟨20126356290863233030631725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 107340566884603909496702533 20126356290863233030631725)
          ·
            refine ⟨7547383609073712386486897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20126356290863233030631725 7547383609073712386486897)
            ·
              refine ⟨5660537706805284289865173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7547383609073712386486897 5660537706805284289865173)
              ·
                refine ⟨132668852503248850543715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5660537706805284289865173 132668852503248850543715)
                ·
                  rfl

theorem cell23_6976035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 2, 7].length) (baseStart_6976035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6976035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6976035 prefixEnd_6976035 := by exact prefixLift 6976035
  have htrace : WordTrace (prefixWord ++ tailWord_6976035) baseStart_6976035 baseEnd_6976035 := by
    simpa [prefixWord, tailWord_6976035, baseEnd_6976035] using wordTrace_append hprefix tailTrace_6976035
  have hstable : (prefixWord ++ tailWord_6976035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6976035).length < 2 ^ (prefixWord ++ tailWord_6976035).sum := by decide
  have hdescent : baseEnd_6976035 < baseStart_6976035 := by decide
  rcases family_descends (prefixWord ++ tailWord_6976035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6976052 : List Nat := [2, 5, 1, 3, 1, 2, 9]
def baseStart_6976052 : Nat := 118140960795 + 6976052 * 2 ^ 59
def prefixEnd_6976052 : Nat := 4983230072969 + 3 ^ 40 * 6976052 * 2
def baseEnd_6976052 : Nat := 44223058601961054298367

theorem tailTrace_6976052 : CollatzResearch.WordTrace tailWord_6976052 prefixEnd_6976052 44223058601961054298367 := by
  unfold tailWord_6976052
  simp only [CollatzResearch.WordTrace]
  refine ⟨127218759661481246836665205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169625012881974995782220273 127218759661481246836665205)
  ·
    refine ⟨11926758718263866890937363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 127218759661481246836665205 11926758718263866890937363)
    ·
      refine ⟨17890138077395800336406045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11926758718263866890937363 17890138077395800336406045)
      ·
        refine ⟨6708801779023425126152267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17890138077395800336406045 6708801779023425126152267)
        ·
          refine ⟨10063202668535137689228401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6708801779023425126152267 10063202668535137689228401)
          ·
            refine ⟨7547402001401353266921301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10063202668535137689228401 7547402001401353266921301)
            ·
              refine ⟨44223058601961054298367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7547402001401353266921301 44223058601961054298367)
              ·
                rfl

theorem cell23_6976052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 9].length) (baseStart_6976052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6976052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6976052 prefixEnd_6976052 := by exact prefixLift 6976052
  have htrace : WordTrace (prefixWord ++ tailWord_6976052) baseStart_6976052 baseEnd_6976052 := by
    simpa [prefixWord, tailWord_6976052, baseEnd_6976052] using wordTrace_append hprefix tailTrace_6976052
  have hstable : (prefixWord ++ tailWord_6976052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6976052).length < 2 ^ (prefixWord ++ tailWord_6976052).sum := by decide
  have hdescent : baseEnd_6976052 < baseStart_6976052 := by decide
  rcases family_descends (prefixWord ++ tailWord_6976052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6976078 : List Nat := [4, 1, 1, 1, 1, 2, 2, 3, 2, 6]
def baseStart_6976078 : Nat := 118140960795 + 6976078 * 2 ^ 59
def prefixEnd_6976078 : Nat := 4983230072969 + 3 ^ 40 * 6976078 * 2
def baseEnd_6976078 : Nat := 1194027032418620765480869

theorem tailTrace_6976078 : CollatzResearch.WordTrace tailWord_6976078 prefixEnd_6976078 1194027032418620765480869 := by
  unfold tailWord_6976078
  simp only [CollatzResearch.WordTrace]
  refine ⟨31804808452608537514222111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 169625645080578866742517925 31804808452608537514222111)
  ·
    refine ⟨47707212678912806271333167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31804808452608537514222111 47707212678912806271333167)
    ·
      refine ⟨71560819018369209406999751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47707212678912806271333167 71560819018369209406999751)
      ·
        refine ⟨107341228527553814110499627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71560819018369209406999751 107341228527553814110499627)
        ·
          refine ⟨161011842791330721165749441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107341228527553814110499627 161011842791330721165749441)
          ·
            refine ⟨120758882093498040874312081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161011842791330721165749441 120758882093498040874312081)
            ·
              refine ⟨90569161570123530655734061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120758882093498040874312081 90569161570123530655734061)
              ·
                refine ⟨33963435588796323995900273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90569161570123530655734061 33963435588796323995900273)
                ·
                  refine ⟨25472576691597242996925205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33963435588796323995900273 25472576691597242996925205)
                  ·
                    refine ⟨1194027032418620765480869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25472576691597242996925205 1194027032418620765480869)
                    ·
                      rfl

theorem cell23_6976078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 3, 2, 6].length) (baseStart_6976078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6976078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6976078 prefixEnd_6976078 := by exact prefixLift 6976078
  have htrace : WordTrace (prefixWord ++ tailWord_6976078) baseStart_6976078 baseEnd_6976078 := by
    simpa [prefixWord, tailWord_6976078, baseEnd_6976078] using wordTrace_append hprefix tailTrace_6976078
  have hstable : (prefixWord ++ tailWord_6976078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6976078).length < 2 ^ (prefixWord ++ tailWord_6976078).sum := by decide
  have hdescent : baseEnd_6976078 < baseStart_6976078 := by decide
  rcases family_descends (prefixWord ++ tailWord_6976078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6976088 : List Nat := [2, 1, 2, 2, 1, 2, 3, 2, 2, 1, 5]
def baseStart_6976088 : Nat := 118140960795 + 6976088 * 2 ^ 59
def prefixEnd_6976088 : Nat := 4983230072969 + 3 ^ 40 * 6976088 * 2
def baseEnd_6976088 : Nat := 3582086232062407257317561

theorem tailTrace_6976088 : CollatzResearch.WordTrace tailWord_6976088 prefixEnd_6976088 3582086232062407257317561 := by
  unfold tailWord_6976088
  simp only [CollatzResearch.WordTrace]
  refine ⟨127219416175416035910820459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169625888233888047881093945 127219416175416035910820459)
  ·
    refine ⟨190829124263124053866230689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127219416175416035910820459 190829124263124053866230689)
    ·
      refine ⟨143121843197343040399673017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190829124263124053866230689 143121843197343040399673017)
      ·
        refine ⟨107341382398007280299754763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143121843197343040399673017 107341382398007280299754763)
        ·
          refine ⟨161012073597010920449632145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107341382398007280299754763 161012073597010920449632145)
          ·
            refine ⟨120759055197758190337224109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161012073597010920449632145 120759055197758190337224109)
            ·
              refine ⟨45284645699159321376459041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 120759055197758190337224109 45284645699159321376459041)
              ·
                refine ⟨33963484274369491032344281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45284645699159321376459041 33963484274369491032344281)
                ·
                  refine ⟨25472613205777118274258211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33963484274369491032344281 25472613205777118274258211)
                  ·
                    refine ⟨38208919808665677411387317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25472613205777118274258211 38208919808665677411387317)
                    ·
                      refine ⟨3582086232062407257317561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38208919808665677411387317 3582086232062407257317561)
                      ·
                        rfl

theorem cell23_6976088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 2, 2, 1, 5].length) (baseStart_6976088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6976088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6976088 prefixEnd_6976088 := by exact prefixLift 6976088
  have htrace : WordTrace (prefixWord ++ tailWord_6976088) baseStart_6976088 baseEnd_6976088 := by
    simpa [prefixWord, tailWord_6976088, baseEnd_6976088] using wordTrace_append hprefix tailTrace_6976088
  have hstable : (prefixWord ++ tailWord_6976088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6976088).length < 2 ^ (prefixWord ++ tailWord_6976088).sum := by decide
  have hdescent : baseEnd_6976088 < baseStart_6976088 := by decide
  rcases family_descends (prefixWord ++ tailWord_6976088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6976135 : List Nat := [1, 1, 4, 2, 1, 2, 3, 1, 2, 3, 3]
def baseStart_6976135 : Nat := 118140960795 + 6976135 * 2 ^ 59
def prefixEnd_6976135 : Nat := 4983230072969 + 3 ^ 40 * 6976135 * 2
def baseEnd_6976135 : Nat := 3582110365653168573429845

theorem tailTrace_6976135 : CollatzResearch.WordTrace tailWord_6976135 prefixEnd_6976135 3582110365653168573429845 := by
  unfold tailWord_6976135
  simp only [CollatzResearch.WordTrace]
  refine ⟨254440546581661798848601859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169627031054441199232401239 254440546581661798848601859)
  ·
    refine ⟨381660819872492698272902789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254440546581661798848601859 381660819872492698272902789)
    ·
      refine ⟨71561403726092380926169273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 381660819872492698272902789 71561403726092380926169273)
      ·
        refine ⟨53671052794569285694626955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71561403726092380926169273 53671052794569285694626955)
        ·
          refine ⟨80506579191853928541940433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53671052794569285694626955 80506579191853928541940433)
          ·
            refine ⟨60379934393890446406455325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80506579191853928541940433 60379934393890446406455325)
            ·
              refine ⟨22642475397708917402420747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60379934393890446406455325 22642475397708917402420747)
              ·
                refine ⟨33963713096563376103631121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22642475397708917402420747 33963713096563376103631121)
                ·
                  refine ⟨25472784822422532077723341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33963713096563376103631121 25472784822422532077723341)
                  ·
                    refine ⟨9552294308408449529146253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25472784822422532077723341 9552294308408449529146253)
                    ·
                      refine ⟨3582110365653168573429845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9552294308408449529146253 3582110365653168573429845)
                      ·
                        rfl

theorem cell23_6976135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 1, 2, 3, 3].length) (baseStart_6976135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6976135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6976135 prefixEnd_6976135 := by exact prefixLift 6976135
  have htrace : WordTrace (prefixWord ++ tailWord_6976135) baseStart_6976135 baseEnd_6976135 := by
    simpa [prefixWord, tailWord_6976135, baseEnd_6976135] using wordTrace_append hprefix tailTrace_6976135
  have hstable : (prefixWord ++ tailWord_6976135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6976135).length < 2 ^ (prefixWord ++ tailWord_6976135).sum := by decide
  have hdescent : baseEnd_6976135 < baseStart_6976135 := by decide
  rcases family_descends (prefixWord ++ tailWord_6976135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6976170 : List Nat := [3, 1, 5, 2, 1, 2, 1, 2, 2, 2, 2]
def baseStart_6976170 : Nat := 118140960795 + 6976170 * 2 ^ 59
def prefixEnd_6976170 : Nat := 4983230072969 + 3 ^ 40 * 6976170 * 2
def baseEnd_6976170 : Nat := 3582128337476075936492185

theorem tailTrace_6976170 : CollatzResearch.WordTrace tailWord_6976170 prefixEnd_6976170 3582128337476075936492185 := by
  unfold tailWord_6976170
  simp only [CollatzResearch.WordTrace]
  refine ⟨63610455784133749956531491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169627882091023333217417309 63610455784133749956531491)
  ·
    refine ⟨95415683676200624934797237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63610455784133749956531491 95415683676200624934797237)
    ·
      refine ⟨8945220344643808587637241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 95415683676200624934797237 8945220344643808587637241)
      ·
        refine ⟨6708915258482856440727931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8945220344643808587637241 6708915258482856440727931)
        ·
          refine ⟨10063372887724284661091897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6708915258482856440727931 10063372887724284661091897)
          ·
            refine ⟨7547529665793213495818923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10063372887724284661091897 7547529665793213495818923)
            ·
              refine ⟨11321294498689820243728385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7547529665793213495818923 11321294498689820243728385)
              ·
                refine ⟨8490970874017365182796289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11321294498689820243728385 8490970874017365182796289)
                ·
                  refine ⟨6368228155513023887097217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8490970874017365182796289 6368228155513023887097217)
                  ·
                    refine ⟨4776171116634767915322913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6368228155513023887097217 4776171116634767915322913)
                    ·
                      refine ⟨3582128337476075936492185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4776171116634767915322913 3582128337476075936492185)
                      ·
                        rfl

theorem cell23_6976170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_6976170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6976170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6976170 prefixEnd_6976170 := by exact prefixLift 6976170
  have htrace : WordTrace (prefixWord ++ tailWord_6976170) baseStart_6976170 baseEnd_6976170 := by
    simpa [prefixWord, tailWord_6976170, baseEnd_6976170] using wordTrace_append hprefix tailTrace_6976170
  have hstable : (prefixWord ++ tailWord_6976170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6976170).length < 2 ^ (prefixWord ++ tailWord_6976170).sum := by decide
  have hdescent : baseEnd_6976170 < baseStart_6976170 := by decide
  rcases family_descends (prefixWord ++ tailWord_6976170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6976192 : List Nat := [2, 1, 1, 2, 4, 2, 2, 1, 2, 4, 2]
def baseStart_6976192 : Nat := 118140960795 + 6976192 * 2 ^ 59
def prefixEnd_6976192 : Nat := 4983230072969 + 3 ^ 40 * 6976192 * 2
def baseEnd_6976192 : Nat := 3582139634050474850417083

theorem tailTrace_6976192 : CollatzResearch.WordTrace tailWord_6976192 prefixEnd_6976192 3582139634050474850417083 := by
  unfold tailWord_6976192
  simp only [CollatzResearch.WordTrace]
  refine ⟨127221312771227648791713415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169628417028303531722284553 127221312771227648791713415)
  ·
    refine ⟨190831969156841473187570123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127221312771227648791713415 190831969156841473187570123)
    ·
      refine ⟨286247953735262209781355185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190831969156841473187570123 286247953735262209781355185)
      ·
        refine ⟨214685965301446657336016389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 286247953735262209781355185 214685965301446657336016389)
        ·
          refine ⟨40253618494021248250503073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 214685965301446657336016389 40253618494021248250503073)
          ·
            refine ⟨30190213870515936187877305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40253618494021248250503073 30190213870515936187877305)
            ·
              refine ⟨22642660402886952140907979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30190213870515936187877305 22642660402886952140907979)
              ·
                refine ⟨33963990604330428211361969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22642660402886952140907979 33963990604330428211361969)
                ·
                  refine ⟨25472992953247821158521477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33963990604330428211361969 25472992953247821158521477)
                  ·
                    refine ⟨4776186178733966467222777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25472992953247821158521477 4776186178733966467222777)
                    ·
                      refine ⟨3582139634050474850417083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4776186178733966467222777 3582139634050474850417083)
                      ·
                        rfl

theorem cell23_6976192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 1, 2, 4, 2].length) (baseStart_6976192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6976192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6976192 prefixEnd_6976192 := by exact prefixLift 6976192
  have htrace : WordTrace (prefixWord ++ tailWord_6976192) baseStart_6976192 baseEnd_6976192 := by
    simpa [prefixWord, tailWord_6976192, baseEnd_6976192] using wordTrace_append hprefix tailTrace_6976192
  have hstable : (prefixWord ++ tailWord_6976192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6976192).length < 2 ^ (prefixWord ++ tailWord_6976192).sum := by decide
  have hdescent : baseEnd_6976192 < baseStart_6976192 := by decide
  rcases family_descends (prefixWord ++ tailWord_6976192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6976202 : List Nat := [3, 1, 2, 1, 4, 1, 2, 2, 3, 4]
def baseStart_6976202 : Nat := 118140960795 + 6976202 * 2 ^ 59
def prefixEnd_6976202 : Nat := 4983230072969 + 3 ^ 40 * 6976202 * 2
def baseEnd_6976202 : Nat := 1194048256285673270430679

theorem tailTrace_6976202 : CollatzResearch.WordTrace tailWord_6976202 prefixEnd_6976202 1194048256285673270430679 := by
  unfold tailWord_6976202
  simp only [CollatzResearch.WordTrace]
  refine ⟨63610747568104767322822715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169628660181612712860860573 63610747568104767322822715)
  ·
    refine ⟨95416121352157150984234073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63610747568104767322822715 95416121352157150984234073)
    ·
      refine ⟨71562091014117863238175555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95416121352157150984234073 71562091014117863238175555)
      ·
        refine ⟨107343136521176794857263333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71562091014117863238175555 107343136521176794857263333)
        ·
          refine ⟨20126838097720649035736875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 107343136521176794857263333 20126838097720649035736875)
          ·
            refine ⟨30190257146580973553605313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20126838097720649035736875 30190257146580973553605313)
            ·
              refine ⟨22642692859935730165203985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30190257146580973553605313 22642692859935730165203985)
              ·
                refine ⟨16982019644951797623902989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22642692859935730165203985 16982019644951797623902989)
                ·
                  refine ⟨6368257366856924108963621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16982019644951797623902989 6368257366856924108963621)
                  ·
                    refine ⟨1194048256285673270430679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6368257366856924108963621 1194048256285673270430679)
                    ·
                      rfl

theorem cell23_6976202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 2, 3, 4].length) (baseStart_6976202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6976202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6976202 prefixEnd_6976202 := by exact prefixLift 6976202
  have htrace : WordTrace (prefixWord ++ tailWord_6976202) baseStart_6976202 baseEnd_6976202 := by
    simpa [prefixWord, tailWord_6976202, baseEnd_6976202] using wordTrace_append hprefix tailTrace_6976202
  have hstable : (prefixWord ++ tailWord_6976202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6976202).length < 2 ^ (prefixWord ++ tailWord_6976202).sum := by decide
  have hdescent : baseEnd_6976202 < baseStart_6976202 := by decide
  rcases family_descends (prefixWord ++ tailWord_6976202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6976275 : List Nat := [1, 1, 1, 2, 1, 3, 5, 2, 1, 6]
def baseStart_6976275 : Nat := 118140960795 + 6976275 * 2 ^ 59
def prefixEnd_6976275 : Nat := 4983230072969 + 3 ^ 40 * 6976275 * 2
def baseEnd_6976275 : Nat := 1194060750981599341893067

theorem tailTrace_6976275 : CollatzResearch.WordTrace tailWord_6976275 prefixEnd_6976275 1194060750981599341893067 := by
  unfold tailWord_6976275
  simp only [CollatzResearch.WordTrace]
  refine ⟨254445652801154602758698279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169630435200769735172465519 254445652801154602758698279)
  ·
    refine ⟨381668479201731904138047419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254445652801154602758698279 381668479201731904138047419)
    ·
      refine ⟨572502718802597856207071129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 381668479201731904138047419 572502718802597856207071129)
      ·
        refine ⟨429377039101948392155303347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 572502718802597856207071129 429377039101948392155303347)
        ·
          refine ⟨644065558652922588232955021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 429377039101948392155303347 644065558652922588232955021)
          ·
            refine ⟨241524584494845970587358133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 644065558652922588232955021 241524584494845970587358133)
            ·
              refine ⟨22642929796391809742564825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 241524584494845970587358133 22642929796391809742564825)
              ·
                refine ⟨16982197347293857306923619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22642929796391809742564825 16982197347293857306923619)
                ·
                  refine ⟨25473296020940785960385429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16982197347293857306923619 25473296020940785960385429)
                  ·
                    refine ⟨1194060750981599341893067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25473296020940785960385429 1194060750981599341893067)
                    ·
                      rfl

theorem cell23_6976275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 2, 1, 6].length) (baseStart_6976275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6976275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6976275 prefixEnd_6976275 := by exact prefixLift 6976275
  have htrace : WordTrace (prefixWord ++ tailWord_6976275) baseStart_6976275 baseEnd_6976275 := by
    simpa [prefixWord, tailWord_6976275, baseEnd_6976275] using wordTrace_append hprefix tailTrace_6976275
  have hstable : (prefixWord ++ tailWord_6976275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6976275).length < 2 ^ (prefixWord ++ tailWord_6976275).sum := by decide
  have hdescent : baseEnd_6976275 < baseStart_6976275 := by decide
  rcases family_descends (prefixWord ++ tailWord_6976275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6976309 : List Nat := [1, 3, 3, 1, 3, 1, 2, 3, 2, 4]
def baseStart_6976309 : Nat := 118140960795 + 6976309 * 2 ^ 59
def prefixEnd_6976309 : Nat := 4983230072969 + 3 ^ 40 * 6976309 * 2
def baseEnd_6976309 : Nat := 1194066570429016964218015

theorem tailTrace_6976309 : CollatzResearch.WordTrace tailWord_6976309 prefixEnd_6976309 1194066570429016964218015 := by
  unfold tailWord_6976309
  simp only [CollatzResearch.WordTrace]
  refine ⟨254446892883031426565435981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169631261922020951043623987 254446892883031426565435981)
  ·
    refine ⟨95417584831136784962038493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 254446892883031426565435981 95417584831136784962038493)
    ·
      refine ⟨35781594311676294360764435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95417584831136784962038493 35781594311676294360764435)
      ·
        refine ⟨53672391467514441541146653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35781594311676294360764435 53672391467514441541146653)
        ·
          refine ⟨20127146800317915577929995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53672391467514441541146653 20127146800317915577929995)
          ·
            refine ⟨30190720200476873366894993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20127146800317915577929995 30190720200476873366894993)
            ·
              refine ⟨22643040150357655025171245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30190720200476873366894993 22643040150357655025171245)
              ·
                refine ⟨8491140056384120634439217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22643040150357655025171245 8491140056384120634439217)
                ·
                  refine ⟨6368355042288090475829413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8491140056384120634439217 6368355042288090475829413)
                  ·
                    refine ⟨1194066570429016964218015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6368355042288090475829413 1194066570429016964218015)
                    ·
                      rfl

theorem cell23_6976309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 3, 2, 4].length) (baseStart_6976309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6976309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6976309 prefixEnd_6976309 := by exact prefixLift 6976309
  have htrace : WordTrace (prefixWord ++ tailWord_6976309) baseStart_6976309 baseEnd_6976309 := by
    simpa [prefixWord, tailWord_6976309, baseEnd_6976309] using wordTrace_append hprefix tailTrace_6976309
  have hstable : (prefixWord ++ tailWord_6976309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6976309).length < 2 ^ (prefixWord ++ tailWord_6976309).sum := by decide
  have hdescent : baseEnd_6976309 < baseStart_6976309 := by decide
  rcases family_descends (prefixWord ++ tailWord_6976309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6976312 : List Nat := [2, 1, 2, 1, 3, 2, 4, 1, 1, 2, 4]
def baseStart_6976312 : Nat := 118140960795 + 6976312 * 2 ^ 59
def prefixEnd_6976312 : Nat := 4983230072969 + 3 ^ 40 * 6976312 * 2
def baseEnd_6976312 : Nat := 3582201251729014380916531

theorem tailTrace_6976312 : CollatzResearch.WordTrace tailWord_6976312 prefixEnd_6976312 3582201251729014380916531 := by
  unfold tailWord_6976312
  simp only [CollatzResearch.WordTrace]
  refine ⟨127223501151010279038897595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169631334868013705385196793 127223501151010279038897595)
  ·
    refine ⟨190835251726515418558346393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127223501151010279038897595 190835251726515418558346393)
    ·
      refine ⟨143126438794886563918759795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190835251726515418558346393 143126438794886563918759795)
      ·
        refine ⟨214689658192329845878139693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143126438794886563918759795 214689658192329845878139693)
        ·
          refine ⟨80508621822123692204302385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 214689658192329845878139693 80508621822123692204302385)
          ·
            refine ⟨60381466366592769153226789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80508621822123692204302385 60381466366592769153226789)
            ·
              refine ⟨11321524943736144216230023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60381466366592769153226789 11321524943736144216230023)
              ·
                refine ⟨16982287415604216324345035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11321524943736144216230023 16982287415604216324345035)
                ·
                  refine ⟨25473431123406324486517553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16982287415604216324345035 25473431123406324486517553)
                  ·
                    refine ⟨19105073342554743364888165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25473431123406324486517553 19105073342554743364888165)
                    ·
                      refine ⟨3582201251729014380916531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19105073342554743364888165 3582201251729014380916531)
                      ·
                        rfl

theorem cell23_6976312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 4, 1, 1, 2, 4].length) (baseStart_6976312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6976312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6976312 prefixEnd_6976312 := by exact prefixLift 6976312
  have htrace : WordTrace (prefixWord ++ tailWord_6976312) baseStart_6976312 baseEnd_6976312 := by
    simpa [prefixWord, tailWord_6976312, baseEnd_6976312] using wordTrace_append hprefix tailTrace_6976312
  have hstable : (prefixWord ++ tailWord_6976312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6976312).length < 2 ^ (prefixWord ++ tailWord_6976312).sum := by decide
  have hdescent : baseEnd_6976312 < baseStart_6976312 := by decide
  rcases family_descends (prefixWord ++ tailWord_6976312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6976375 : List Nat := [1, 1, 3, 1, 1, 2, 1, 2, 3, 3, 5]
def baseStart_6976375 : Nat := 118140960795 + 6976375 * 2 ^ 59
def prefixEnd_6976375 : Nat := 4983230072969 + 3 ^ 40 * 6976375 * 2
def baseEnd_6976375 : Nat := 3582233601010247634428741

theorem tailTrace_6976375 : CollatzResearch.WordTrace tailWord_6976375 prefixEnd_6976375 3582233601010247634428741 := by
  unfold tailWord_6976375
  simp only [CollatzResearch.WordTrace]
  refine ⟨254449300100792319837338579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169632866733861546558225719 254449300100792319837338579)
  ·
    refine ⟨381673950151188479756007869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254449300100792319837338579 381673950151188479756007869)
    ·
      refine ⟨143127731306695679908502951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 381673950151188479756007869 143127731306695679908502951)
      ·
        refine ⟨214691596960043519862754427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143127731306695679908502951 214691596960043519862754427)
        ·
          refine ⟨322037395440065279794131641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214691596960043519862754427 322037395440065279794131641)
          ·
            refine ⟨241528046580048959845598731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 322037395440065279794131641 241528046580048959845598731)
            ·
              refine ⟨362292069870073439768398097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 241528046580048959845598731 362292069870073439768398097)
              ·
                refine ⟨271719052402555079826298573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 362292069870073439768398097 271719052402555079826298573)
                ·
                  refine ⟨101894644650958154934861965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 271719052402555079826298573 101894644650958154934861965)
                  ·
                    refine ⟨38210491744109308100573237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 101894644650958154934861965 38210491744109308100573237)
                    ·
                      refine ⟨3582233601010247634428741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38210491744109308100573237 3582233601010247634428741)
                      ·
                        rfl

theorem cell23_6976375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 3, 3, 5].length) (baseStart_6976375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6976375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6976375 prefixEnd_6976375 := by exact prefixLift 6976375
  have htrace : WordTrace (prefixWord ++ tailWord_6976375) baseStart_6976375 baseEnd_6976375 := by
    simpa [prefixWord, tailWord_6976375, baseEnd_6976375] using wordTrace_append hprefix tailTrace_6976375
  have hstable : (prefixWord ++ tailWord_6976375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6976375).length < 2 ^ (prefixWord ++ tailWord_6976375).sum := by decide
  have hdescent : baseEnd_6976375 < baseStart_6976375 := by decide
  rcases family_descends (prefixWord ++ tailWord_6976375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6976392 : List Nat := [2, 1, 3, 3, 2, 1, 1, 1, 1, 3, 5]
def baseStart_6976392 : Nat := 118140960795 + 6976392 * 2 ^ 59
def prefixEnd_6976392 : Nat := 4983230072969 + 3 ^ 40 * 6976392 * 2
def baseEnd_6976392 : Nat := 3582242330181374067916163

theorem tailTrace_6976392 : CollatzResearch.WordTrace tailWord_6976392 prefixEnd_6976392 3582242330181374067916163 := by
  unfold tailWord_6976392
  simp only [CollatzResearch.WordTrace]
  refine ⟨127224960070865365870353715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169633280094487154493804953 127224960070865365870353715)
  ·
    refine ⟨190837440106298048805530573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127224960070865365870353715 190837440106298048805530573)
    ·
      refine ⟨71564040039861768302073965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 190837440106298048805530573 71564040039861768302073965)
      ·
        refine ⟨26836515014948163113277737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71564040039861768302073965 26836515014948163113277737)
        ·
          refine ⟨20127386261211122334958303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26836515014948163113277737 20127386261211122334958303)
          ·
            refine ⟨30191079391816683502437455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20127386261211122334958303 30191079391816683502437455)
            ·
              refine ⟨45286619087725025253656183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30191079391816683502437455 45286619087725025253656183)
              ·
                refine ⟨67929928631587537880484275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45286619087725025253656183 67929928631587537880484275)
                ·
                  refine ⟨101894892947381306820726413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67929928631587537880484275 101894892947381306820726413)
                  ·
                    refine ⟨38210584855267990057772405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 101894892947381306820726413 38210584855267990057772405)
                    ·
                      refine ⟨3582242330181374067916163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38210584855267990057772405 3582242330181374067916163)
                      ·
                        rfl

theorem cell23_6976392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_6976392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6976392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6976392 prefixEnd_6976392 := by exact prefixLift 6976392
  have htrace : WordTrace (prefixWord ++ tailWord_6976392) baseStart_6976392 baseEnd_6976392 := by
    simpa [prefixWord, tailWord_6976392, baseEnd_6976392] using wordTrace_append hprefix tailTrace_6976392
  have hstable : (prefixWord ++ tailWord_6976392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6976392).length < 2 ^ (prefixWord ++ tailWord_6976392).sum := by decide
  have hdescent : baseEnd_6976392 < baseStart_6976392 := by decide
  rcases family_descends (prefixWord ++ tailWord_6976392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6976395 : List Nat := [1, 1, 1, 1, 4, 2, 2, 2, 9]
def baseStart_6976395 : Nat := 118140960795 + 6976395 * 2 ^ 59
def prefixEnd_6976395 : Nat := 4983230072969 + 3 ^ 40 * 6976395 * 2
def baseEnd_6976395 : Nat := 398027096735926395130961

theorem tailTrace_6976395 : CollatzResearch.WordTrace tailWord_6976395 prefixEnd_6976395 398027096735926395130961 := by
  unfold tailWord_6976395
  simp only [CollatzResearch.WordTrace]
  refine ⟨254450029560719863253066639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169633353040479908835377759 254450029560719863253066639)
  ·
    refine ⟨381675044341079794879599959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254450029560719863253066639 381675044341079794879599959)
    ·
      refine ⟨572512566511619692319399939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 381675044341079794879599959 572512566511619692319399939)
      ·
        refine ⟨858768849767429538479099909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 572512566511619692319399939 858768849767429538479099909)
        ·
          refine ⟨161019159331393038464831233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 858768849767429538479099909 161019159331393038464831233)
          ·
            refine ⟨120764369498544778848623425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161019159331393038464831233 120764369498544778848623425)
            ·
              refine ⟨90573277123908584136467569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120764369498544778848623425 90573277123908584136467569)
              ·
                refine ⟨67929957842931438102350677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90573277123908584136467569 67929957842931438102350677)
                ·
                  refine ⟨398027096735926395130961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 67929957842931438102350677 398027096735926395130961)
                  ·
                    rfl

theorem cell23_6976395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 2, 9].length) (baseStart_6976395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6976395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6976395 prefixEnd_6976395 := by exact prefixLift 6976395
  have htrace : WordTrace (prefixWord ++ tailWord_6976395) baseStart_6976395 baseEnd_6976395 := by
    simpa [prefixWord, tailWord_6976395, baseEnd_6976395] using wordTrace_append hprefix tailTrace_6976395
  have hstable : (prefixWord ++ tailWord_6976395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6976395).length < 2 ^ (prefixWord ++ tailWord_6976395).sum := by decide
  have hdescent : baseEnd_6976395 < baseStart_6976395 := by decide
  rcases family_descends (prefixWord ++ tailWord_6976395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6976466 : List Nat := [3, 2, 2, 3, 1, 1, 1, 1, 2, 5, 2]
def baseStart_6976466 : Nat := 118140960795 + 6976466 * 2 ^ 59
def prefixEnd_6976466 : Nat := 4983230072969 + 3 ^ 40 * 6976466 * 2
def baseEnd_6976466 : Nat := 3582280327749806778390823

theorem tailTrace_6976466 : CollatzResearch.WordTrace tailWord_6976466 prefixEnd_6976466 3582280327749806778390823 := by
  unfold tailWord_6976466
  simp only [CollatzResearch.WordTrace]
  refine ⟨63613154785865660594725313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169635079428975094919267501 63613154785865660594725313)
  ·
    refine ⟨47709866089399245446043985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63613154785865660594725313 47709866089399245446043985)
    ·
      refine ⟨35782399567049434084532989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47709866089399245446043985 35782399567049434084532989)
      ·
        refine ⟨13418399837643537781699871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35782399567049434084532989 13418399837643537781699871)
        ·
          refine ⟨20127599756465306672549807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13418399837643537781699871 20127599756465306672549807)
          ·
            refine ⟨30191399634697960008824711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20127599756465306672549807 30191399634697960008824711)
            ·
              refine ⟨45287099452046940013237067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30191399634697960008824711 45287099452046940013237067)
              ·
                refine ⟨67930649178070410019855601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45287099452046940013237067 67930649178070410019855601)
                ·
                  refine ⟨50947986883552807514891701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67930649178070410019855601 50947986883552807514891701)
                  ·
                    refine ⟨4776373770333075704521097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50947986883552807514891701 4776373770333075704521097)
                    ·
                      refine ⟨3582280327749806778390823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4776373770333075704521097 3582280327749806778390823)
                      ·
                        rfl

theorem cell23_6976466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 1, 2, 5, 2].length) (baseStart_6976466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6976466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6976466 prefixEnd_6976466 := by exact prefixLift 6976466
  have htrace : WordTrace (prefixWord ++ tailWord_6976466) baseStart_6976466 baseEnd_6976466 := by
    simpa [prefixWord, tailWord_6976466, baseEnd_6976466] using wordTrace_append hprefix tailTrace_6976466
  have hstable : (prefixWord ++ tailWord_6976466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6976466).length < 2 ^ (prefixWord ++ tailWord_6976466).sum := by decide
  have hdescent : baseEnd_6976466 < baseStart_6976466 := by decide
  rcases family_descends (prefixWord ++ tailWord_6976466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6976536 : List Nat := [2, 1, 2, 3, 2, 3, 3, 1, 6]
def baseStart_6976536 : Nat := 118140960795 + 6976536 * 2 ^ 59
def prefixEnd_6976536 : Nat := 4983230072969 + 3 ^ 40 * 6976536 * 2
def baseEnd_6976536 : Nat := 398035141266180167168389

theorem tailTrace_6976536 : CollatzResearch.WordTrace tailWord_6976536 prefixEnd_6976536 398035141266180167168389 := by
  unfold tailWord_6976536
  simp only [CollatzResearch.WordTrace]
  refine ⟨127227586126604522166974731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169636781502139362889299641 127227586126604522166974731)
  ·
    refine ⟨190841379189906783250462097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127227586126604522166974731 190841379189906783250462097)
    ·
      refine ⟨143131034392430087437846573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190841379189906783250462097 143131034392430087437846573)
      ·
        refine ⟨53674137897161282789192465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143131034392430087437846573 53674137897161282789192465)
        ·
          refine ⟨40255603422870962091894349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53674137897161282789192465 40255603422870962091894349)
          ·
            refine ⟨15095851283576610784460381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40255603422870962091894349 15095851283576610784460381)
            ·
              refine ⟨5660944231341229044172643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15095851283576610784460381 5660944231341229044172643)
              ·
                refine ⟨8491416347011843566258965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5660944231341229044172643 8491416347011843566258965)
                ·
                  refine ⟨398035141266180167168389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8491416347011843566258965 398035141266180167168389)
                  ·
                    rfl

theorem cell23_6976536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 3, 1, 6].length) (baseStart_6976536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6976536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6976536 prefixEnd_6976536 := by exact prefixLift 6976536
  have htrace : WordTrace (prefixWord ++ tailWord_6976536) baseStart_6976536 baseEnd_6976536 := by
    simpa [prefixWord, tailWord_6976536, baseEnd_6976536] using wordTrace_append hprefix tailTrace_6976536
  have hstable : (prefixWord ++ tailWord_6976536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6976536).length < 2 ^ (prefixWord ++ tailWord_6976536).sum := by decide
  have hdescent : baseEnd_6976536 < baseStart_6976536 := by decide
  rcases family_descends (prefixWord ++ tailWord_6976536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6976556 : List Nat := [2, 2, 1, 1, 1, 2, 4, 3, 2, 3, 2]
def baseStart_6976556 : Nat := 118140960795 + 6976556 * 2 ^ 59
def prefixEnd_6976556 : Nat := 4983230072969 + 3 ^ 40 * 6976556 * 2
def baseEnd_6976556 : Nat := 3582326541008711426265409

theorem tailTrace_6976556 : CollatzResearch.WordTrace tailWord_6976556 prefixEnd_6976556 3582326541008711426265409 := by
  unfold tailWord_6976556
  simp only [CollatzResearch.WordTrace]
  refine ⟨127227950856568293874838761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169637267808757725166451681 127227950856568293874838761)
  ·
    refine ⟨95420963142426220406129071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127227950856568293874838761 95420963142426220406129071)
    ·
      refine ⟨143131444713639330609193607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95420963142426220406129071 143131444713639330609193607)
      ·
        refine ⟨214697167070458995913790411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143131444713639330609193607 214697167070458995913790411)
        ·
          refine ⟨322045750605688493870685617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214697167070458995913790411 322045750605688493870685617)
          ·
            refine ⟨241534312954266370403014213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 322045750605688493870685617 241534312954266370403014213)
            ·
              refine ⟨45287683678924944450565165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 241534312954266370403014213 45287683678924944450565165)
              ·
                refine ⟨16982881379596854168961937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45287683678924944450565165 16982881379596854168961937)
                ·
                  refine ⟨12737161034697640626721453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16982881379596854168961937 12737161034697640626721453)
                  ·
                    refine ⟨4776435388011615235020545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12737161034697640626721453 4776435388011615235020545)
                    ·
                      refine ⟨3582326541008711426265409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4776435388011615235020545 3582326541008711426265409)
                      ·
                        rfl

theorem cell23_6976556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 3, 2].length) (baseStart_6976556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6976556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6976556 prefixEnd_6976556 := by exact prefixLift 6976556
  have htrace : WordTrace (prefixWord ++ tailWord_6976556) baseStart_6976556 baseEnd_6976556 := by
    simpa [prefixWord, tailWord_6976556, baseEnd_6976556] using wordTrace_append hprefix tailTrace_6976556
  have hstable : (prefixWord ++ tailWord_6976556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6976556).length < 2 ^ (prefixWord ++ tailWord_6976556).sum := by decide
  have hdescent : baseEnd_6976556 < baseStart_6976556 := by decide
  rcases family_descends (prefixWord ++ tailWord_6976556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6976573 : List Nat := [1, 4, 1, 3, 1, 3, 1, 2, 2, 3, 2]
def baseStart_6976573 : Nat := 118140960795 + 6976573 * 2 ^ 59
def prefixEnd_6976573 : Nat := 4983230072969 + 3 ^ 40 * 6976573 * 2
def baseEnd_6976573 : Nat := 3582335270179837859752831

theorem tailTrace_6976573 : CollatzResearch.WordTrace tailWord_6976573 prefixEnd_6976573 3582335270179837859752831 := by
  unfold tailWord_6976573
  simp only [CollatzResearch.WordTrace]
  refine ⟨254456521754074999653046373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169637681169383333102030915 254456521754074999653046373)
  ·
    refine ⟨47710597828889062434946195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 254456521754074999653046373 47710597828889062434946195)
    ·
      refine ⟨71565896743333593652419293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47710597828889062434946195 71565896743333593652419293)
      ·
        refine ⟨26837211278750097619657235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71565896743333593652419293 26837211278750097619657235)
        ·
          refine ⟨40255816918125146429485853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26837211278750097619657235 40255816918125146429485853)
          ·
            refine ⟨15095931344296929911057195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40255816918125146429485853 15095931344296929911057195)
            ·
              refine ⟨22643897016445394866585793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15095931344296929911057195 22643897016445394866585793)
              ·
                refine ⟨16982922762334046149939345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22643897016445394866585793 16982922762334046149939345)
                ·
                  refine ⟨12737192071750534612454509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16982922762334046149939345 12737192071750534612454509)
                  ·
                    refine ⟨4776447026906450479670441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12737192071750534612454509 4776447026906450479670441)
                    ·
                      refine ⟨3582335270179837859752831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4776447026906450479670441 3582335270179837859752831)
                      ·
                        rfl

theorem cell23_6976573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 2, 2, 3, 2].length) (baseStart_6976573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6976573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6976573 prefixEnd_6976573 := by exact prefixLift 6976573
  have htrace : WordTrace (prefixWord ++ tailWord_6976573) baseStart_6976573 baseEnd_6976573 := by
    simpa [prefixWord, tailWord_6976573, baseEnd_6976573] using wordTrace_append hprefix tailTrace_6976573
  have hstable : (prefixWord ++ tailWord_6976573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6976573).length < 2 ^ (prefixWord ++ tailWord_6976573).sum := by decide
  have hdescent : baseEnd_6976573 < baseStart_6976573 := by decide
  rcases family_descends (prefixWord ++ tailWord_6976573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6976579 : List Nat := [1, 1, 1, 3, 1, 2, 3, 3, 4, 4]
def baseStart_6976579 : Nat := 118140960795 + 6976579 * 2 ^ 59
def prefixEnd_6976579 : Nat := 4983230072969 + 3 ^ 40 * 6976579 * 2
def baseEnd_6976579 : Nat := 1194112783687921612092601

theorem tailTrace_6976579 : CollatzResearch.WordTrace tailWord_6976579 prefixEnd_6976579 1194112783687921612092601 := by
  unfold tailWord_6976579
  simp only [CollatzResearch.WordTrace]
  refine ⟨254456740592053262677764791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169637827061368841785176527 254456740592053262677764791)
  ·
    refine ⟨381685110888079894016647187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254456740592053262677764791 381685110888079894016647187)
    ·
      refine ⟨572527666332119841024970781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 381685110888079894016647187 572527666332119841024970781)
      ·
        refine ⟨214697874874544940384364043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 572527666332119841024970781 214697874874544940384364043)
        ·
          refine ⟨322046812311817410576546065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214697874874544940384364043 322046812311817410576546065)
          ·
            refine ⟨241535109233863057932409549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 322046812311817410576546065 241535109233863057932409549)
            ·
              refine ⟨90575665962698646724653581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 241535109233863057932409549 90575665962698646724653581)
              ·
                refine ⟨33965874736011992521745093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90575665962698646724653581 33965874736011992521745093)
                ·
                  refine ⟨6368601513002248597827205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33965874736011992521745093 6368601513002248597827205)
                  ·
                    refine ⟨1194112783687921612092601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6368601513002248597827205 1194112783687921612092601)
                    ·
                      rfl

theorem cell23_6976579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 3, 4, 4].length) (baseStart_6976579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6976579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6976579 prefixEnd_6976579 := by exact prefixLift 6976579
  have htrace : WordTrace (prefixWord ++ tailWord_6976579) baseStart_6976579 baseEnd_6976579 := by
    simpa [prefixWord, tailWord_6976579, baseEnd_6976579] using wordTrace_append hprefix tailTrace_6976579
  have hstable : (prefixWord ++ tailWord_6976579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6976579).length < 2 ^ (prefixWord ++ tailWord_6976579).sum := by decide
  have hdescent : baseEnd_6976579 < baseStart_6976579 := by decide
  rcases family_descends (prefixWord ++ tailWord_6976579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6976599 : List Nat := [1, 1, 3, 2, 2, 1, 1, 5, 1, 2, 4]
def baseStart_6976599 : Nat := 118140960795 + 6976599 * 2 ^ 59
def prefixEnd_6976599 : Nat := 4983230072969 + 3 ^ 40 * 6976599 * 2
def baseEnd_6976599 : Nat := 3582348620676854758027711

theorem tailTrace_6976599 : CollatzResearch.WordTrace tailWord_6976599 prefixEnd_6976599 3582348620676854758027711 := by
  unfold tailWord_6976599
  simp only [CollatzResearch.WordTrace]
  refine ⟨254457470051980806093492851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169638313367987204062328567 254457470051980806093492851)
  ·
    refine ⟨381686205077971209140239277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254457470051980806093492851 381686205077971209140239277)
    ·
      refine ⟨143132326904239203427589729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 381686205077971209140239277 143132326904239203427589729)
      ·
        refine ⟨107349245178179402570692297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143132326904239203427589729 107349245178179402570692297)
        ·
          refine ⟨80511933883634551928019223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107349245178179402570692297 80511933883634551928019223)
          ·
            refine ⟨120767900825451827892028835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80511933883634551928019223 120767900825451827892028835)
            ·
              refine ⟨181151851238177741838043253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120767900825451827892028835 181151851238177741838043253)
              ·
                refine ⟨16982986053579163297316555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 181151851238177741838043253 16982986053579163297316555)
                ·
                  refine ⟨25474479080368744945974833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16982986053579163297316555 25474479080368744945974833)
                  ·
                    refine ⟨19105859310276558709481125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25474479080368744945974833 19105859310276558709481125)
                    ·
                      refine ⟨3582348620676854758027711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19105859310276558709481125 3582348620676854758027711)
                      ·
                        rfl

theorem cell23_6976599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 5, 1, 2, 4].length) (baseStart_6976599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6976599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6976599 prefixEnd_6976599 := by exact prefixLift 6976599
  have htrace : WordTrace (prefixWord ++ tailWord_6976599) baseStart_6976599 baseEnd_6976599 := by
    simpa [prefixWord, tailWord_6976599, baseEnd_6976599] using wordTrace_append hprefix tailTrace_6976599
  have hstable : (prefixWord ++ tailWord_6976599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6976599).length < 2 ^ (prefixWord ++ tailWord_6976599).sum := by decide
  have hdescent : baseEnd_6976599 < baseStart_6976599 := by decide
  rcases family_descends (prefixWord ++ tailWord_6976599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6976620 : List Nat := [2, 2, 1, 1, 3, 2, 2, 5, 1, 2, 2]
def baseStart_6976620 : Nat := 118140960795 + 6976620 * 2 ^ 59
def prefixEnd_6976620 : Nat := 4983230072969 + 3 ^ 40 * 6976620 * 2
def baseEnd_6976620 : Nat := 3582359403770599175865115

theorem tailTrace_6976620 : CollatzResearch.WordTrace tailWord_6976620 prefixEnd_6976620 3582359403770599175865115 := by
  unfold tailWord_6976620
  simp only [CollatzResearch.WordTrace]
  refine ⟨127229117992452363340003657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169638823989936484453338209 127229117992452363340003657)
  ·
    refine ⟨95421838494339272505002743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127229117992452363340003657 95421838494339272505002743)
    ·
      refine ⟨143132757741508908757504115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95421838494339272505002743 143132757741508908757504115)
      ·
        refine ⟨214699136612263363136256173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143132757741508908757504115 214699136612263363136256173)
        ·
          refine ⟨80512176229598761176096065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 214699136612263363136256173 80512176229598761176096065)
          ·
            refine ⟨60384132172199070882072049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80512176229598761176096065 60384132172199070882072049)
            ·
              refine ⟨45288099129149303161554037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60384132172199070882072049 45288099129149303161554037)
              ·
                refine ⟨4245759293357747171395691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45288099129149303161554037 4245759293357747171395691)
                ·
                  refine ⟨6368638940036620757093537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4245759293357747171395691 6368638940036620757093537)
                  ·
                    refine ⟨4776479205027465567820153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6368638940036620757093537 4776479205027465567820153)
                    ·
                      refine ⟨3582359403770599175865115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4776479205027465567820153 3582359403770599175865115)
                      ·
                        rfl

theorem cell23_6976620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 5, 1, 2, 2].length) (baseStart_6976620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6976620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6976620 prefixEnd_6976620 := by exact prefixLift 6976620
  have htrace : WordTrace (prefixWord ++ tailWord_6976620) baseStart_6976620 baseEnd_6976620 := by
    simpa [prefixWord, tailWord_6976620, baseEnd_6976620] using wordTrace_append hprefix tailTrace_6976620
  have hstable : (prefixWord ++ tailWord_6976620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6976620).length < 2 ^ (prefixWord ++ tailWord_6976620).sum := by decide
  have hdescent : baseEnd_6976620 < baseStart_6976620 := by decide
  rcases family_descends (prefixWord ++ tailWord_6976620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6976623 : List Nat := [1, 1, 2, 1, 3, 3, 5, 1, 1, 2, 3]
def baseStart_6976623 : Nat := 118140960795 + 6976623 * 2 ^ 59
def prefixEnd_6976623 : Nat := 4983230072969 + 3 ^ 40 * 6976623 * 2
def baseEnd_6976623 : Nat := 3582360944212562664127601

theorem tailTrace_6976623 : CollatzResearch.WordTrace tailWord_6976623 prefixEnd_6976623 3582360944212562664127601 := by
  unfold tailWord_6976623
  simp only [CollatzResearch.WordTrace]
  refine ⟨254458345403893858192366523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169638896935929238794911015 254458345403893858192366523)
  ·
    refine ⟨381687518105840787288549785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254458345403893858192366523 381687518105840787288549785)
    ·
      refine ⟨286265638579380590466412339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 381687518105840787288549785 286265638579380590466412339)
      ·
        refine ⟨429398457869070885699618509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286265638579380590466412339 429398457869070885699618509)
        ·
          refine ⟨161024421700901582137356941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 429398457869070885699618509 161024421700901582137356941)
          ·
            refine ⟨60384158137838093301508853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 161024421700901582137356941 60384158137838093301508853)
            ·
              refine ⟨5661014825422321247016455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 60384158137838093301508853 5661014825422321247016455)
              ·
                refine ⟨8491522238133481870524683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5661014825422321247016455 8491522238133481870524683)
                ·
                  refine ⟨12737283357200222805787025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8491522238133481870524683 12737283357200222805787025)
                  ·
                    refine ⟨9552962517900167104340269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12737283357200222805787025 9552962517900167104340269)
                    ·
                      refine ⟨3582360944212562664127601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9552962517900167104340269 3582360944212562664127601)
                      ·
                        rfl

theorem cell23_6976623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 5, 1, 1, 2, 3].length) (baseStart_6976623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6976623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6976623 prefixEnd_6976623 := by exact prefixLift 6976623
  have htrace : WordTrace (prefixWord ++ tailWord_6976623) baseStart_6976623 baseEnd_6976623 := by
    simpa [prefixWord, tailWord_6976623, baseEnd_6976623] using wordTrace_append hprefix tailTrace_6976623
  have hstable : (prefixWord ++ tailWord_6976623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6976623).length < 2 ^ (prefixWord ++ tailWord_6976623).sum := by decide
  have hdescent : baseEnd_6976623 < baseStart_6976623 := by decide
  rcases family_descends (prefixWord ++ tailWord_6976623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6976663 : List Nat := [1, 1, 3, 3, 3, 1, 2, 1, 3, 3, 2]
def baseStart_6976663 : Nat := 118140960795 + 6976663 * 2 ^ 59
def prefixEnd_6976663 : Nat := 4983230072969 + 3 ^ 40 * 6976663 * 2
def baseEnd_6976663 : Nat := 3582381483438742507627417

theorem tailTrace_6976663 : CollatzResearch.WordTrace tailWord_6976663 prefixEnd_6976663 3582381483438742507627417 := by
  unfold tailWord_6976663
  simp only [CollatzResearch.WordTrace]
  refine ⟨254459804323748945023822643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169639869549165963349215095 254459804323748945023822643)
  ·
    refine ⟨381689706485623417535733965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254459804323748945023822643 381689706485623417535733965)
    ·
      refine ⟨143133639932108781575900237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 381689706485623417535733965 143133639932108781575900237)
      ·
        refine ⟨53675114974540793090962589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143133639932108781575900237 53675114974540793090962589)
        ·
          refine ⟨20128168115452797409110971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53675114974540793090962589 20128168115452797409110971)
          ·
            refine ⟨30192252173179196113666457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20128168115452797409110971 30192252173179196113666457)
            ·
              refine ⟨22644189129884397085249843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30192252173179196113666457 22644189129884397085249843)
              ·
                refine ⟨33966283694826595627874765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22644189129884397085249843 33966283694826595627874765)
                ·
                  refine ⟨12737356385559973360453037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33966283694826595627874765 12737356385559973360453037)
                  ·
                    refine ⟨4776508644584990010169889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12737356385559973360453037 4776508644584990010169889)
                    ·
                      refine ⟨3582381483438742507627417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4776508644584990010169889 3582381483438742507627417)
                      ·
                        rfl

theorem cell23_6976663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 1, 3, 3, 2].length) (baseStart_6976663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6976663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6976663 prefixEnd_6976663 := by exact prefixLift 6976663
  have htrace : WordTrace (prefixWord ++ tailWord_6976663) baseStart_6976663 baseEnd_6976663 := by
    simpa [prefixWord, tailWord_6976663, baseEnd_6976663] using wordTrace_append hprefix tailTrace_6976663
  have hstable : (prefixWord ++ tailWord_6976663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6976663).length < 2 ^ (prefixWord ++ tailWord_6976663).sum := by decide
  have hdescent : baseEnd_6976663 < baseStart_6976663 := by decide
  rcases family_descends (prefixWord ++ tailWord_6976663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6976669 : List Nat := [1, 4, 2, 1, 1, 2, 1, 2, 1, 8]
def baseStart_6976669 : Nat := 118140960795 + 6976669 * 2 ^ 59
def prefixEnd_6976669 : Nat := 4983230072969 + 3 ^ 40 * 6976669 * 2
def baseEnd_6976669 : Nat := 1194128188107556494717463

theorem tailTrace_6976669 : CollatzResearch.WordTrace tailWord_6976669 prefixEnd_6976669 1194128188107556494717463 := by
  unfold tailWord_6976669
  simp only [CollatzResearch.WordTrace]
  refine ⟨254460023161727208048541061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169640015441151472032360707 254460023161727208048541061)
  ·
    refine ⟨47711254342823851509101449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 254460023161727208048541061 47711254342823851509101449)
    ·
      refine ⟨35783440757117888631826087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47711254342823851509101449 35783440757117888631826087)
      ·
        refine ⟨53675161135676832947739131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35783440757117888631826087 53675161135676832947739131)
        ·
          refine ⟨80512741703515249421608697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53675161135676832947739131 80512741703515249421608697)
          ·
            refine ⟨60384556277636437066206523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80512741703515249421608697 60384556277636437066206523)
            ·
              refine ⟨90576834416454655599309785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60384556277636437066206523 90576834416454655599309785)
              ·
                refine ⟨67932625812340991699482339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90576834416454655599309785 67932625812340991699482339)
                ·
                  refine ⟨101898938718511487549223509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67932625812340991699482339 101898938718511487549223509)
                  ·
                    refine ⟨1194128188107556494717463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 101898938718511487549223509 1194128188107556494717463)
                    ·
                      rfl

theorem cell23_6976669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 2, 1, 8].length) (baseStart_6976669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6976669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6976669 prefixEnd_6976669 := by exact prefixLift 6976669
  have htrace : WordTrace (prefixWord ++ tailWord_6976669) baseStart_6976669 baseEnd_6976669 := by
    simpa [prefixWord, tailWord_6976669, baseEnd_6976669] using wordTrace_append hprefix tailTrace_6976669
  have hstable : (prefixWord ++ tailWord_6976669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6976669).length < 2 ^ (prefixWord ++ tailWord_6976669).sum := by decide
  have hdescent : baseEnd_6976669 < baseStart_6976669 := by decide
  rcases family_descends (prefixWord ++ tailWord_6976669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6976674 : List Nat := [3, 3, 1, 3, 3, 1, 2, 1, 1, 2, 3]
def baseStart_6976674 : Nat := 118140960795 + 6976674 * 2 ^ 59
def prefixEnd_6976674 : Nat := 4983230072969 + 3 ^ 40 * 6976674 * 2
def baseEnd_6976674 : Nat := 3582387131725941964589867

theorem tailTrace_6976674 : CollatzResearch.WordTrace tailWord_6976674 prefixEnd_6976674 3582387131725941964589867 := by
  unfold tailWord_6976674
  simp only [CollatzResearch.WordTrace]
  refine ⟨63615051381677273475618269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169640137017806062601648717 63615051381677273475618269)
  ·
    refine ⟨23855644268128977553356851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63615051381677273475618269 23855644268128977553356851)
    ·
      refine ⟨35783466402193466330035277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23855644268128977553356851 35783466402193466330035277)
      ·
        refine ⟨13418799900822549873763229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35783466402193466330035277 13418799900822549873763229)
        ·
          refine ⟨5032049962808456202661211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13418799900822549873763229 5032049962808456202661211)
          ·
            refine ⟨7548074944212684303991817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5032049962808456202661211 7548074944212684303991817)
            ·
              refine ⟨5661056208159513227993863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7548074944212684303991817 5661056208159513227993863)
              ·
                refine ⟨8491584312239269841990795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5661056208159513227993863 8491584312239269841990795)
                ·
                  refine ⟨12737376468358904762986193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8491584312239269841990795 12737376468358904762986193)
                  ·
                    refine ⟨9553032351269178572239645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12737376468358904762986193 9553032351269178572239645)
                    ·
                      refine ⟨3582387131725941964589867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9553032351269178572239645 3582387131725941964589867)
                      ·
                        rfl

theorem cell23_6976674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 2, 1, 1, 2, 3].length) (baseStart_6976674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6976674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6976674 prefixEnd_6976674 := by exact prefixLift 6976674
  have htrace : WordTrace (prefixWord ++ tailWord_6976674) baseStart_6976674 baseEnd_6976674 := by
    simpa [prefixWord, tailWord_6976674, baseEnd_6976674] using wordTrace_append hprefix tailTrace_6976674
  have hstable : (prefixWord ++ tailWord_6976674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6976674).length < 2 ^ (prefixWord ++ tailWord_6976674).sum := by decide
  have hdescent : baseEnd_6976674 < baseStart_6976674 := by decide
  rcases family_descends (prefixWord ++ tailWord_6976674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6976746 : List Nat := [3, 1, 3, 1, 1, 3, 1, 1, 4, 5]
def baseStart_6976746 : Nat := 118140960795 + 6976746 * 2 ^ 59
def prefixEnd_6976746 : Nat := 4983230072969 + 3 ^ 40 * 6976746 * 2
def baseEnd_6976746 : Nat := 1194141367444355227629845

theorem tailTrace_6976746 : CollatzResearch.WordTrace tailWord_6976746 prefixEnd_6976746 1194141367444355227629845 := by
  unfold tailWord_6976746
  simp only [CollatzResearch.WordTrace]
  refine ⟨63615707895612062549773523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169641887721632166799396061 63615707895612062549773523)
  ·
    refine ⟨95423561843418093824660285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63615707895612062549773523 95423561843418093824660285)
    ·
      refine ⟨35783835691281785184247607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95423561843418093824660285 35783835691281785184247607)
      ·
        refine ⟨53675753536922677776371411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35783835691281785184247607 53675753536922677776371411)
        ·
          refine ⟨80513630305384016664557117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53675753536922677776371411 80513630305384016664557117)
          ·
            refine ⟨30192611364519006249208919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80513630305384016664557117 30192611364519006249208919)
            ·
              refine ⟨45288917046778509373813379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30192611364519006249208919 45288917046778509373813379)
              ·
                refine ⟨67933375570167764060720069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45288917046778509373813379 67933375570167764060720069)
                ·
                  refine ⟨12737507919406455761385013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67933375570167764060720069 12737507919406455761385013)
                  ·
                    refine ⟨1194141367444355227629845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12737507919406455761385013 1194141367444355227629845)
                    ·
                      rfl

theorem cell23_6976746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 1, 4, 5].length) (baseStart_6976746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6976746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6976746 prefixEnd_6976746 := by exact prefixLift 6976746
  have htrace : WordTrace (prefixWord ++ tailWord_6976746) baseStart_6976746 baseEnd_6976746 := by
    simpa [prefixWord, tailWord_6976746, baseEnd_6976746] using wordTrace_append hprefix tailTrace_6976746
  have hstable : (prefixWord ++ tailWord_6976746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6976746).length < 2 ^ (prefixWord ++ tailWord_6976746).sum := by decide
  have hdescent : baseEnd_6976746 < baseStart_6976746 := by decide
  rcases family_descends (prefixWord ++ tailWord_6976746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6976803 : List Nat := [1, 1, 1, 4, 2, 3, 2, 2, 2, 2, 3]
def baseStart_6976803 : Nat := 118140960795 + 6976803 * 2 ^ 59
def prefixEnd_6976803 : Nat := 4983230072969 + 3 ^ 40 * 6976803 * 2
def baseEnd_6976803 : Nat := 3582453370730371959876773

theorem tailTrace_6976803 : CollatzResearch.WordTrace tailWord_6976803 prefixEnd_6976803 3582453370730371959876773 := by
  unfold tailWord_6976803
  simp only [CollatzResearch.WordTrace]
  refine ⟨254464910543241748933919063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169643273695494499289279375 254464910543241748933919063)
  ·
    refine ⟨381697365814862623400878595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254464910543241748933919063 381697365814862623400878595)
    ·
      refine ⟨572546048722293935101317893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 381697365814862623400878595 572546048722293935101317893)
      ·
        refine ⟨107352384135430112831497105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 572546048722293935101317893 107352384135430112831497105)
        ·
          refine ⟨80514288101572584623622829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107352384135430112831497105 80514288101572584623622829)
          ·
            refine ⟨30192858038089719233858561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80514288101572584623622829 30192858038089719233858561)
            ·
              refine ⟨22644643528567289425393921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30192858038089719233858561 22644643528567289425393921)
              ·
                refine ⟨16983482646425467069045441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22644643528567289425393921 16983482646425467069045441)
                ·
                  refine ⟨12737611984819100301784081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16983482646425467069045441 12737611984819100301784081)
                  ·
                    refine ⟨9553208988614325226338061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12737611984819100301784081 9553208988614325226338061)
                    ·
                      refine ⟨3582453370730371959876773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9553208988614325226338061 3582453370730371959876773)
                      ·
                        rfl

theorem cell23_6976803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 2, 2, 2, 3].length) (baseStart_6976803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6976803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6976803 prefixEnd_6976803 := by exact prefixLift 6976803
  have htrace : WordTrace (prefixWord ++ tailWord_6976803) baseStart_6976803 baseEnd_6976803 := by
    simpa [prefixWord, tailWord_6976803, baseEnd_6976803] using wordTrace_append hprefix tailTrace_6976803
  have hstable : (prefixWord ++ tailWord_6976803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6976803).length < 2 ^ (prefixWord ++ tailWord_6976803).sum := by decide
  have hdescent : baseEnd_6976803 < baseStart_6976803 := by decide
  rcases family_descends (prefixWord ++ tailWord_6976803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6976867 : List Nat := [1, 1, 1, 5, 2, 2, 2, 4, 1, 1, 3]
def baseStart_6976867 : Nat := 118140960795 + 6976867 * 2 ^ 59
def prefixEnd_6976867 : Nat := 4983230072969 + 3 ^ 40 * 6976867 * 2
def baseEnd_6976867 : Nat := 3582486233492259709476479

theorem tailTrace_6976867 : CollatzResearch.WordTrace tailWord_6976867 prefixEnd_6976867 3582486233492259709476479 := by
  unfold tailWord_6976867
  simp only [CollatzResearch.WordTrace]
  refine ⟨254467244815009887864248855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169644829876673258576165903 254467244815009887864248855)
  ·
    refine ⟨381700867222514831796373283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254467244815009887864248855 381700867222514831796373283)
    ·
      refine ⟨572551300833772247694559925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 381700867222514831796373283 572551300833772247694559925)
      ·
        refine ⟨53676684453166148221364993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 572551300833772247694559925 53676684453166148221364993)
        ·
          refine ⟨40257513339874611166023745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53676684453166148221364993 40257513339874611166023745)
          ·
            refine ⟨30193135004905958374517809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40257513339874611166023745 30193135004905958374517809)
            ·
              refine ⟨22644851253679468780888357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30193135004905958374517809 22644851253679468780888357)
              ·
                refine ⟨4245909610064900396416567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22644851253679468780888357 4245909610064900396416567)
                ·
                  refine ⟨6368864415097350594624851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4245909610064900396416567 6368864415097350594624851)
                  ·
                    refine ⟨9553296622646025891937277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6368864415097350594624851 9553296622646025891937277)
                    ·
                      refine ⟨3582486233492259709476479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9553296622646025891937277 3582486233492259709476479)
                      ·
                        rfl

theorem cell23_6976867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 4, 1, 1, 3].length) (baseStart_6976867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6976867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6976867 prefixEnd_6976867 := by exact prefixLift 6976867
  have htrace : WordTrace (prefixWord ++ tailWord_6976867) baseStart_6976867 baseEnd_6976867 := by
    simpa [prefixWord, tailWord_6976867, baseEnd_6976867] using wordTrace_append hprefix tailTrace_6976867
  have hstable : (prefixWord ++ tailWord_6976867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6976867).length < 2 ^ (prefixWord ++ tailWord_6976867).sum := by decide
  have hdescent : baseEnd_6976867 < baseStart_6976867 := by decide
  rcases family_descends (prefixWord ++ tailWord_6976867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6976993 : List Nat := [1, 2, 3, 1, 2, 3, 1, 1, 1, 4, 4]
def baseStart_6976993 : Nat := 118140960795 + 6976993 * 2 ^ 59
def prefixEnd_6976993 : Nat := 4983230072969 + 3 ^ 40 * 6976993 * 2
def baseEnd_6976993 : Nat := 3582550932054726216500899

theorem tailTrace_6976993 : CollatzResearch.WordTrace tailWord_6976993 prefixEnd_6976993 3582550932054726216500899 := by
  unfold tailWord_6976993
  simp only [CollatzResearch.WordTrace]
  refine ⟨254471840412553411383335633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169647893608368940922223755 254471840412553411383335633)
  ·
    refine ⟨190853880309415058537501725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254471840412553411383335633 190853880309415058537501725)
    ·
      refine ⟨71570205116030646951563147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 190853880309415058537501725 71570205116030646951563147)
      ·
        refine ⟨107355307674045970427344721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71570205116030646951563147 107355307674045970427344721)
        ·
          refine ⟨80516480755534477820508541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107355307674045970427344721 80516480755534477820508541)
          ·
            refine ⟨30193680283325429182690703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80516480755534477820508541 30193680283325429182690703)
            ·
              refine ⟨45290520424988143774036055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30193680283325429182690703 45290520424988143774036055)
              ·
                refine ⟨67935780637482215661054083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45290520424988143774036055 67935780637482215661054083)
                ·
                  refine ⟨101903670956223323491581125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67935780637482215661054083 101903670956223323491581125)
                  ·
                    refine ⟨19106938304291873154671461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 101903670956223323491581125 19106938304291873154671461)
                    ·
                      refine ⟨3582550932054726216500899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19106938304291873154671461 3582550932054726216500899)
                      ·
                        rfl

theorem cell23_6976993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 1, 1, 4, 4].length) (baseStart_6976993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6976993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6976993 prefixEnd_6976993 := by exact prefixLift 6976993
  have htrace : WordTrace (prefixWord ++ tailWord_6976993) baseStart_6976993 baseEnd_6976993 := by
    simpa [prefixWord, tailWord_6976993, baseEnd_6976993] using wordTrace_append hprefix tailTrace_6976993
  have hstable : (prefixWord ++ tailWord_6976993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6976993).length < 2 ^ (prefixWord ++ tailWord_6976993).sum := by decide
  have hdescent : baseEnd_6976993 < baseStart_6976993 := by decide
  rcases family_descends (prefixWord ++ tailWord_6976993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6976997 : List Nat := [1, 3, 1, 5, 1, 1, 1, 3, 1, 4, 2]
def baseStart_6976997 : Nat := 118140960795 + 6976997 * 2 ^ 59
def prefixEnd_6976997 : Nat := 4983230072969 + 3 ^ 40 * 6976997 * 2
def baseEnd_6976997 : Nat := 3582552985977344200850881

theorem tailTrace_6976997 : CollatzResearch.WordTrace tailWord_6976997 prefixEnd_6976997 3582552985977344200850881 := by
  unfold tailWord_6976997
  simp only [CollatzResearch.WordTrace]
  refine ⟨254471986304538920066481245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169647990869692613377654163 254471986304538920066481245)
  ·
    refine ⟨95426994864202095024930467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 254471986304538920066481245 95426994864202095024930467)
    ·
      refine ⟨143140492296303142537395701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95426994864202095024930467 143140492296303142537395701)
      ·
        refine ⟨13419421152778419612880847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 143140492296303142537395701 13419421152778419612880847)
        ·
          refine ⟨20129131729167629419321271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13419421152778419612880847 20129131729167629419321271)
          ·
            refine ⟨30193697593751444128981907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20129131729167629419321271 30193697593751444128981907)
            ·
              refine ⟨45290546390627166193472861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30193697593751444128981907 45290546390627166193472861)
              ·
                refine ⟨16983954896485187322552323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45290546390627166193472861 16983954896485187322552323)
                ·
                  refine ⟨25475932344727780983828485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16983954896485187322552323 25475932344727780983828485)
                  ·
                    refine ⟨4776737314636458934467841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25475932344727780983828485 4776737314636458934467841)
                    ·
                      refine ⟨3582552985977344200850881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4776737314636458934467841 3582552985977344200850881)
                      ·
                        rfl

theorem cell23_6976997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 3, 1, 4, 2].length) (baseStart_6976997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6976997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6976997 prefixEnd_6976997 := by exact prefixLift 6976997
  have htrace : WordTrace (prefixWord ++ tailWord_6976997) baseStart_6976997 baseEnd_6976997 := by
    simpa [prefixWord, tailWord_6976997, baseEnd_6976997] using wordTrace_append hprefix tailTrace_6976997
  have hstable : (prefixWord ++ tailWord_6976997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6976997).length < 2 ^ (prefixWord ++ tailWord_6976997).sum := by decide
  have hdescent : baseEnd_6976997 < baseStart_6976997 := by decide
  rcases family_descends (prefixWord ++ tailWord_6976997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6977020 : List Nat := [2, 2, 2, 1, 2, 1, 3, 5, 5]
def baseStart_6977020 : Nat := 118140960795 + 6977020 * 2 ^ 59
def prefixEnd_6977020 : Nat := 4983230072969 + 3 ^ 40 * 6977020 * 2
def baseEnd_6977020 : Nat := 398062755114710845651475

theorem tailTrace_6977020 : CollatzResearch.WordTrace tailWord_6977020 prefixEnd_6977020 398062755114710845651475 := by
  unfold tailWord_6977020
  simp only [CollatzResearch.WordTrace]
  refine ⟨127236412591727797497284257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169648550122303729996379009 127236412591727797497284257)
  ·
    refine ⟨95427309443795848122963193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127236412591727797497284257 95427309443795848122963193)
    ·
      refine ⟨71570482082846886092222395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95427309443795848122963193 71570482082846886092222395)
      ·
        refine ⟨107355723124270329138333593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71570482082846886092222395 107355723124270329138333593)
        ·
          refine ⟨80516792343202746853750195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107355723124270329138333593 80516792343202746853750195)
          ·
            refine ⟨120775188514804120280625293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80516792343202746853750195 120775188514804120280625293)
            ·
              refine ⟨45290695693051545105234485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 120775188514804120280625293 45290695693051545105234485)
              ·
                refine ⟨4246002721223582353615733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45290695693051545105234485 4246002721223582353615733)
                ·
                  refine ⟨398062755114710845651475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4246002721223582353615733 398062755114710845651475)
                  ·
                    rfl

theorem cell23_6977020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 5, 5].length) (baseStart_6977020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6977020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6977020 prefixEnd_6977020 := by exact prefixLift 6977020
  have htrace : WordTrace (prefixWord ++ tailWord_6977020) baseStart_6977020 baseEnd_6977020 := by
    simpa [prefixWord, tailWord_6977020, baseEnd_6977020] using wordTrace_append hprefix tailTrace_6977020
  have hstable : (prefixWord ++ tailWord_6977020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6977020).length < 2 ^ (prefixWord ++ tailWord_6977020).sum := by decide
  have hdescent : baseEnd_6977020 < baseStart_6977020 := by decide
  rcases family_descends (prefixWord ++ tailWord_6977020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6977031 : List Nat := [1, 1, 4, 3, 2, 3, 1, 2, 2, 2, 2]
def baseStart_6977031 : Nat := 118140960795 + 6977031 * 2 ^ 59
def prefixEnd_6977031 : Nat := 4983230072969 + 3 ^ 40 * 6977031 * 2
def baseEnd_6977031 : Nat := 3582570444319597067825725

theorem tailTrace_6977031 : CollatzResearch.WordTrace tailWord_6977031 prefixEnd_6977031 3582570444319597067825725 := by
  unfold tailWord_6977031
  simp only [CollatzResearch.WordTrace]
  refine ⟨254473226386415743873218947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169648817590943829248812631 254473226386415743873218947)
  ·
    refine ⟨381709839579623615809828421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254473226386415743873218947 381709839579623615809828421)
    ·
      refine ⟨71570594921179427964342829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 381709839579623615809828421 71570594921179427964342829)
      ·
        refine ⟨26838973095442285486628561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71570594921179427964342829 26838973095442285486628561)
        ·
          refine ⟨20129229821581714114971421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26838973095442285486628561 20129229821581714114971421)
          ·
            refine ⟨7548461183093142793114283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20129229821581714114971421 7548461183093142793114283)
            ·
              refine ⟨11322691774639714189671425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7548461183093142793114283 11322691774639714189671425)
              ·
                refine ⟨8492018830979785642253569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11322691774639714189671425 8492018830979785642253569)
                ·
                  refine ⟨6369014123234839231690177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8492018830979785642253569 6369014123234839231690177)
                  ·
                    refine ⟨4776760592426129423767633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6369014123234839231690177 4776760592426129423767633)
                    ·
                      refine ⟨3582570444319597067825725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4776760592426129423767633 3582570444319597067825725)
                      ·
                        rfl

theorem cell23_6977031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 1, 2, 2, 2, 2].length) (baseStart_6977031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6977031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6977031 prefixEnd_6977031 := by exact prefixLift 6977031
  have htrace : WordTrace (prefixWord ++ tailWord_6977031) baseStart_6977031 baseEnd_6977031 := by
    simpa [prefixWord, tailWord_6977031, baseEnd_6977031] using wordTrace_append hprefix tailTrace_6977031
  have hstable : (prefixWord ++ tailWord_6977031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6977031).length < 2 ^ (prefixWord ++ tailWord_6977031).sum := by decide
  have hdescent : baseEnd_6977031 < baseStart_6977031 := by decide
  rcases family_descends (prefixWord ++ tailWord_6977031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6977033 : List Nat := [1, 2, 1, 1, 3, 1, 4, 1, 4, 5]
def baseStart_6977033 : Nat := 118140960795 + 6977033 * 2 ^ 59
def prefixEnd_6977033 : Nat := 4983230072969 + 3 ^ 40 * 6977033 * 2
def baseEnd_6977033 : Nat := 1194190490426968686666905

theorem tailTrace_6977033 : CollatzResearch.WordTrace tailWord_6977033 prefixEnd_6977033 1194190490426968686666905 := by
  unfold tailWord_6977033
  simp only [CollatzResearch.WordTrace]
  refine ⟨254473299332408498214791753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169648866221605665476527835 254473299332408498214791753)
  ·
    refine ⟨190854974499306373661093815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254473299332408498214791753 190854974499306373661093815)
    ·
      refine ⟨286282461748959560491640723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190854974499306373661093815 286282461748959560491640723)
      ·
        refine ⟨429423692623439340737461085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286282461748959560491640723 429423692623439340737461085)
        ·
          refine ⟨161033884733789752776547907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 429423692623439340737461085 161033884733789752776547907)
          ·
            refine ⟨241550827100684629164821861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161033884733789752776547907 241550827100684629164821861)
            ·
              refine ⟨45290780081378367968404099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 241550827100684629164821861 45290780081378367968404099)
              ·
                refine ⟨67936170122067551952606149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45290780081378367968404099 67936170122067551952606149)
                ·
                  refine ⟨12738031897887665991113653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67936170122067551952606149 12738031897887665991113653)
                  ·
                    refine ⟨1194190490426968686666905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12738031897887665991113653 1194190490426968686666905)
                    ·
                      rfl

theorem cell23_6977033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 1, 4, 5].length) (baseStart_6977033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6977033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6977033 prefixEnd_6977033 := by exact prefixLift 6977033
  have htrace : WordTrace (prefixWord ++ tailWord_6977033) baseStart_6977033 baseEnd_6977033 := by
    simpa [prefixWord, tailWord_6977033, baseEnd_6977033] using wordTrace_append hprefix tailTrace_6977033
  have hstable : (prefixWord ++ tailWord_6977033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6977033).length < 2 ^ (prefixWord ++ tailWord_6977033).sum := by decide
  have hdescent : baseEnd_6977033 < baseStart_6977033 := by decide
  rcases family_descends (prefixWord ++ tailWord_6977033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6977073 : List Nat := [1, 2, 2, 3, 1, 1, 1, 2, 2, 3, 5]
def baseStart_6977073 : Nat := 118140960795 + 6977073 * 2 ^ 59
def prefixEnd_6977073 : Nat := 4983230072969 + 3 ^ 40 * 6977073 * 2
def baseEnd_6977073 : Nat := 3582592010507085903500531

theorem tailTrace_6977073 : CollatzResearch.WordTrace tailWord_6977073 prefixEnd_6977073 3582592010507085903500531 := by
  unfold tailWord_6977073
  simp only [CollatzResearch.WordTrace]
  refine ⟨254474758252263585046247873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169649838834842390030831915 254474758252263585046247873)
  ·
    refine ⟨190856068689197688784685905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254474758252263585046247873 190856068689197688784685905)
    ·
      refine ⟨143142051516898266588514429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190856068689197688784685905 143142051516898266588514429)
      ·
        refine ⟨53678269318836849970692911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143142051516898266588514429 53678269318836849970692911)
        ·
          refine ⟨80517403978255274956039367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53678269318836849970692911 80517403978255274956039367)
          ·
            refine ⟨120776105967382912434059051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80517403978255274956039367 120776105967382912434059051)
            ·
              refine ⟨181164158951074368651088577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120776105967382912434059051 181164158951074368651088577)
              ·
                refine ⟨135873119213305776488316433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 181164158951074368651088577 135873119213305776488316433)
                ·
                  refine ⟨101904839409979332366237325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 135873119213305776488316433 101904839409979332366237325)
                  ·
                    refine ⟨38214314778742249637338997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 101904839409979332366237325 38214314778742249637338997)
                    ·
                      refine ⟨3582592010507085903500531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38214314778742249637338997 3582592010507085903500531)
                      ·
                        rfl

theorem cell23_6977073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 2, 2, 3, 5].length) (baseStart_6977073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6977073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6977073 prefixEnd_6977073 := by exact prefixLift 6977073
  have htrace : WordTrace (prefixWord ++ tailWord_6977073) baseStart_6977073 baseEnd_6977073 := by
    simpa [prefixWord, tailWord_6977073, baseEnd_6977073] using wordTrace_append hprefix tailTrace_6977073
  have hstable : (prefixWord ++ tailWord_6977073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6977073).length < 2 ^ (prefixWord ++ tailWord_6977073).sum := by decide
  have hdescent : baseEnd_6977073 < baseStart_6977073 := by decide
  rcases family_descends (prefixWord ++ tailWord_6977073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6977093 : List Nat := [1, 3, 1, 1, 1, 4, 1, 3, 8]
def baseStart_6977093 : Nat := 118140960795 + 6977093 * 2 ^ 59
def prefixEnd_6977093 : Nat := 4983230072969 + 3 ^ 40 * 6977093 * 2
def baseEnd_6977093 : Nat := 398066920013352869472271

theorem tailTrace_6977093 : CollatzResearch.WordTrace tailWord_6977093 prefixEnd_6977093 398066920013352869472271 := by
  unfold tailWord_6977093
  simp only [CollatzResearch.WordTrace]
  refine ⟨254475487712191128461975933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169650325141460752307983955 254475487712191128461975933)
  ·
    refine ⟨95428307892071673173240975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 254475487712191128461975933 95428307892071673173240975)
    ·
      refine ⟨143142461838107509759861463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95428307892071673173240975 143142461838107509759861463)
      ·
        refine ⟨214713692757161264639792195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143142461838107509759861463 214713692757161264639792195)
        ·
          refine ⟨322070539135741896959688293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214713692757161264639792195 322070539135741896959688293)
          ·
            refine ⟨60388226087951605679941555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 322070539135741896959688293 60388226087951605679941555)
            ·
              refine ⟨90582339131927408519912333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60388226087951605679941555 90582339131927408519912333)
              ·
                refine ⟨33968377174472778194967125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90582339131927408519912333 33968377174472778194967125)
                ·
                  refine ⟨398066920013352869472271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33968377174472778194967125 398066920013352869472271)
                  ·
                    rfl

theorem cell23_6977093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 3, 8].length) (baseStart_6977093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6977093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6977093 prefixEnd_6977093 := by exact prefixLift 6977093
  have htrace : WordTrace (prefixWord ++ tailWord_6977093) baseStart_6977093 baseEnd_6977093 := by
    simpa [prefixWord, tailWord_6977093, baseEnd_6977093] using wordTrace_append hprefix tailTrace_6977093
  have hstable : (prefixWord ++ tailWord_6977093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6977093).length < 2 ^ (prefixWord ++ tailWord_6977093).sum := by decide
  have hdescent : baseEnd_6977093 < baseStart_6977093 := by decide
  rcases family_descends (prefixWord ++ tailWord_6977093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6977094 : List Nat := [6, 1, 1, 1, 3, 1, 1, 1, 1, 2, 5]
def baseStart_6977094 : Nat := 118140960795 + 6977094 * 2 ^ 59
def prefixEnd_6977094 : Nat := 4983230072969 + 3 ^ 40 * 6977094 * 2
def baseEnd_6977094 : Nat := 3582602793600830321337935

theorem tailTrace_6977094 : CollatzResearch.WordTrace tailWord_6977094 prefixEnd_6977094 3582602793600830321337935 := by
  unfold tailWord_6977094
  simp only [CollatzResearch.WordTrace]
  refine ⟨7952360130787109551023823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 169650349456791670421841557 7952360130787109551023823)
  ·
    refine ⟨11928540196180664326535735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7952360130787109551023823 11928540196180664326535735)
    ·
      refine ⟨17892810294270996489803603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11928540196180664326535735 17892810294270996489803603)
      ·
        refine ⟨26839215441406494734705405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17892810294270996489803603 26839215441406494734705405)
        ·
          refine ⟨10064705790527435525514527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26839215441406494734705405 10064705790527435525514527)
          ·
            refine ⟨15097058685791153288271791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10064705790527435525514527 15097058685791153288271791)
            ·
              refine ⟨22645588028686729932407687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15097058685791153288271791 22645588028686729932407687)
              ·
                refine ⟨33968382043030094898611531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22645588028686729932407687 33968382043030094898611531)
                ·
                  refine ⟨50952573064545142347917297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33968382043030094898611531 50952573064545142347917297)
                  ·
                    refine ⟨38214429798408856760937973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50952573064545142347917297 38214429798408856760937973)
                    ·
                      refine ⟨3582602793600830321337935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38214429798408856760937973 3582602793600830321337935)
                      ·
                        rfl

theorem cell23_6977094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 1, 1, 2, 5].length) (baseStart_6977094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6977094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6977094 prefixEnd_6977094 := by exact prefixLift 6977094
  have htrace : WordTrace (prefixWord ++ tailWord_6977094) baseStart_6977094 baseEnd_6977094 := by
    simpa [prefixWord, tailWord_6977094, baseEnd_6977094] using wordTrace_append hprefix tailTrace_6977094
  have hstable : (prefixWord ++ tailWord_6977094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6977094).length < 2 ^ (prefixWord ++ tailWord_6977094).sum := by decide
  have hdescent : baseEnd_6977094 < baseStart_6977094 := by decide
  rcases family_descends (prefixWord ++ tailWord_6977094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6977097 : List Nat := [1, 2, 1, 1, 2, 2, 1, 8, 1, 4]
def baseStart_6977097 : Nat := 118140960795 + 6977097 * 2 ^ 59
def prefixEnd_6977097 : Nat := 4983230072969 + 3 ^ 40 * 6977097 * 2
def baseEnd_6977097 : Nat := 1194201444680931269866807

theorem tailTrace_6977097 : CollatzResearch.WordTrace tailWord_6977097 prefixEnd_6977097 1194201444680931269866807 := by
  unfold tailWord_6977097
  simp only [CollatzResearch.WordTrace]
  refine ⟨254475633604176637145121545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169650422402784424763414363 254475633604176637145121545)
  ·
    refine ⟨190856725203132477858841159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254475633604176637145121545 190856725203132477858841159)
    ·
      refine ⟨286285087804698716788261739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190856725203132477858841159 286285087804698716788261739)
      ·
        refine ⟨429427631707048075182392609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286285087804698716788261739 429427631707048075182392609)
        ·
          refine ⟨322070723780286056386794457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 429427631707048075182392609 322070723780286056386794457)
          ·
            refine ⟨241553042835214542290095843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 322070723780286056386794457 241553042835214542290095843)
            ·
              refine ⟨362329564252821813435143765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 241553042835214542290095843 362329564252821813435143765)
              ·
                refine ⟨4246049581087755626193091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 362329564252821813435143765 4246049581087755626193091)
                ·
                  refine ⟨6369074371631633439289637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4246049581087755626193091 6369074371631633439289637)
                  ·
                    refine ⟨1194201444680931269866807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6369074371631633439289637 1194201444680931269866807)
                    ·
                      rfl

theorem cell23_6977097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 8, 1, 4].length) (baseStart_6977097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6977097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6977097 prefixEnd_6977097 := by exact prefixLift 6977097
  have htrace : WordTrace (prefixWord ++ tailWord_6977097) baseStart_6977097 baseEnd_6977097 := by
    simpa [prefixWord, tailWord_6977097, baseEnd_6977097] using wordTrace_append hprefix tailTrace_6977097
  have hstable : (prefixWord ++ tailWord_6977097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6977097).length < 2 ^ (prefixWord ++ tailWord_6977097).sum := by decide
  have hdescent : baseEnd_6977097 < baseStart_6977097 := by decide
  rcases family_descends (prefixWord ++ tailWord_6977097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6977113 : List Nat := [1, 2, 1, 2, 2, 1, 1, 4, 1, 2, 6]
def baseStart_6977113 : Nat := 118140960795 + 6977113 * 2 ^ 59
def prefixEnd_6977113 : Nat := 4983230072969 + 3 ^ 40 * 6977113 * 2
def baseEnd_6977113 : Nat := 3582612549733265747000347

theorem tailTrace_6977113 : CollatzResearch.WordTrace tailWord_6977113 prefixEnd_6977113 3582612549733265747000347 := by
  unfold tailWord_6977113
  simp only [CollatzResearch.WordTrace]
  refine ⟨254476217172118671877703993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169650811448079114585135995 254476217172118671877703993)
  ·
    refine ⟨190857162879089003908277995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254476217172118671877703993 190857162879089003908277995)
    ·
      refine ⟨286285744318633505862416993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190857162879089003908277995 286285744318633505862416993)
      ·
        refine ⟨214714308238975129396812745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 286285744318633505862416993 214714308238975129396812745)
        ·
          refine ⟨161035731179231347047609559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 214714308238975129396812745 161035731179231347047609559)
          ·
            refine ⟨241553596768847020571414339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161035731179231347047609559 241553596768847020571414339)
            ·
              refine ⟨362330395153270530857121509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 241553596768847020571414339 362330395153270530857121509)
              ·
                refine ⟨67936949091238224535710283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 362330395153270530857121509 67936949091238224535710283)
                ·
                  refine ⟨101905423636857336803565425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67936949091238224535710283 101905423636857336803565425)
                  ·
                    refine ⟨76429067727643002602674069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 101905423636857336803565425 76429067727643002602674069)
                    ·
                      refine ⟨3582612549733265747000347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76429067727643002602674069 3582612549733265747000347)
                      ·
                        rfl

theorem cell23_6977113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 4, 1, 2, 6].length) (baseStart_6977113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6977113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6977113 prefixEnd_6977113 := by exact prefixLift 6977113
  have htrace : WordTrace (prefixWord ++ tailWord_6977113) baseStart_6977113 baseEnd_6977113 := by
    simpa [prefixWord, tailWord_6977113, baseEnd_6977113] using wordTrace_append hprefix tailTrace_6977113
  have hstable : (prefixWord ++ tailWord_6977113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6977113).length < 2 ^ (prefixWord ++ tailWord_6977113).sum := by decide
  have hdescent : baseEnd_6977113 < baseStart_6977113 := by decide
  rcases family_descends (prefixWord ++ tailWord_6977113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6977147 : List Nat := [1, 1, 1, 1, 1, 4, 3, 4, 2, 3, 2]
def baseStart_6977147 : Nat := 118140960795 + 6977147 * 2 ^ 59
def prefixEnd_6977147 : Nat := 4983230072969 + 3 ^ 40 * 6977147 * 2
def baseEnd_6977147 : Nat := 3582630008075518613975191

theorem tailTrace_6977147 : CollatzResearch.WordTrace tailWord_6977147 prefixEnd_6977147 3582630008075518613975191 := by
  unfold tailWord_6977147
  simp only [CollatzResearch.WordTrace]
  refine ⟨254477457253995495684441695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169651638169330330456294463 254477457253995495684441695)
  ·
    refine ⟨381716185880993243526662543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254477457253995495684441695 381716185880993243526662543)
    ·
      refine ⟨572574278821489865289993815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 381716185880993243526662543 572574278821489865289993815)
      ·
        refine ⟨858861418232234797934990723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 572574278821489865289993815 858861418232234797934990723)
        ·
          refine ⟨1288292127348352196902486085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 858861418232234797934990723 1288292127348352196902486085)
          ·
            refine ⟨241554773877816036919216141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1288292127348352196902486085 241554773877816036919216141)
            ·
              refine ⟨90583040204181013844706053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 241554773877816036919216141 90583040204181013844706053)
              ·
                refine ⟨16984320038283940095882385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 90583040204181013844706053 16984320038283940095882385)
                ·
                  refine ⟨12738240028712955071911789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16984320038283940095882385 12738240028712955071911789)
                  ·
                    refine ⟨4776840010767358151966921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12738240028712955071911789 4776840010767358151966921)
                    ·
                      refine ⟨3582630008075518613975191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4776840010767358151966921 3582630008075518613975191)
                      ·
                        rfl

theorem cell23_6977147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 4, 2, 3, 2].length) (baseStart_6977147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6977147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6977147 prefixEnd_6977147 := by exact prefixLift 6977147
  have htrace : WordTrace (prefixWord ++ tailWord_6977147) baseStart_6977147 baseEnd_6977147 := by
    simpa [prefixWord, tailWord_6977147, baseEnd_6977147] using wordTrace_append hprefix tailTrace_6977147
  have hstable : (prefixWord ++ tailWord_6977147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6977147).length < 2 ^ (prefixWord ++ tailWord_6977147).sum := by decide
  have hdescent : baseEnd_6977147 < baseStart_6977147 := by decide
  rcases family_descends (prefixWord ++ tailWord_6977147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6977197 : List Nat := [1, 5, 2, 1, 1, 1, 2, 3, 1, 1, 5]
def baseStart_6977197 : Nat := 118140960795 + 6977197 * 2 ^ 59
def prefixEnd_6977197 : Nat := 4983230072969 + 3 ^ 40 * 6977197 * 2
def baseEnd_6977197 : Nat := 3582655682108243418349961

theorem tailTrace_6977197 : CollatzResearch.WordTrace tailWord_6977197 prefixEnd_6977197 3582655682108243418349961 := by
  unfold tailWord_6977197
  simp only [CollatzResearch.WordTrace]
  refine ⟨254479280903814354223761845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169652853935876236149174563 254479280903814354223761845)
  ·
    refine ⟨23857432584732595708477673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 254479280903814354223761845 23857432584732595708477673)
    ·
      refine ⟨17893074438549446781358255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23857432584732595708477673 17893074438549446781358255)
      ·
        refine ⟨26839611657824170172037383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17893074438549446781358255 26839611657824170172037383)
        ·
          refine ⟨40259417486736255258056075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26839611657824170172037383 40259417486736255258056075)
          ·
            refine ⟨60389126230104382887084113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40259417486736255258056075 60389126230104382887084113)
            ·
              refine ⟨45291844672578287165313085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60389126230104382887084113 45291844672578287165313085)
              ·
                refine ⟨16984441752216857686992407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45291844672578287165313085 16984441752216857686992407)
                ·
                  refine ⟨25476662628325286530488611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16984441752216857686992407 25476662628325286530488611)
                  ·
                    refine ⟨38214993942487929795732917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25476662628325286530488611 38214993942487929795732917)
                    ·
                      refine ⟨3582655682108243418349961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38214993942487929795732917 3582655682108243418349961)
                      ·
                        rfl

theorem cell23_6977197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_6977197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6977197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6977197 prefixEnd_6977197 := by exact prefixLift 6977197
  have htrace : WordTrace (prefixWord ++ tailWord_6977197) baseStart_6977197 baseEnd_6977197 := by
    simpa [prefixWord, tailWord_6977197, baseEnd_6977197] using wordTrace_append hprefix tailTrace_6977197
  have hstable : (prefixWord ++ tailWord_6977197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6977197).length < 2 ^ (prefixWord ++ tailWord_6977197).sum := by decide
  have hdescent : baseEnd_6977197 < baseStart_6977197 := by decide
  rcases family_descends (prefixWord ++ tailWord_6977197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6977234 : List Nat := [3, 2, 2, 2, 2, 3, 2, 7]
def baseStart_6977234 : Nat := 118140960795 + 6977234 * 2 ^ 59
def prefixEnd_6977234 : Nat := 4983230072969 + 3 ^ 40 * 6977234 * 2
def baseEnd_6977234 : Nat := 132691654847868880503233

theorem tailTrace_6977234 : CollatzResearch.WordTrace tailWord_6977234 prefixEnd_6977234 132691654847868880503233 := by
  unfold tailWord_6977234
  simp only [CollatzResearch.WordTrace]
  refine ⟨63620157601170077385714689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169653753603120206361905837 63620157601170077385714689)
  ·
    refine ⟨47715118200877558039286017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63620157601170077385714689 47715118200877558039286017)
    ·
      refine ⟨35786338650658168529464513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47715118200877558039286017 35786338650658168529464513)
      ·
        refine ⟨26839753987993626397098385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35786338650658168529464513 26839753987993626397098385)
        ·
          refine ⟨20129815490995219797823789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26839753987993626397098385 20129815490995219797823789)
          ·
            refine ⟨7548680809123207424183921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20129815490995219797823789 7548680809123207424183921)
            ·
              refine ⟨5661510606842405568137941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7548680809123207424183921 5661510606842405568137941)
              ·
                refine ⟨132691654847868880503233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5661510606842405568137941 132691654847868880503233)
                ·
                  rfl

theorem cell23_6977234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 2, 7].length) (baseStart_6977234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6977234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6977234 prefixEnd_6977234 := by exact prefixLift 6977234
  have htrace : WordTrace (prefixWord ++ tailWord_6977234) baseStart_6977234 baseEnd_6977234 := by
    simpa [prefixWord, tailWord_6977234, baseEnd_6977234] using wordTrace_append hprefix tailTrace_6977234
  have hstable : (prefixWord ++ tailWord_6977234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6977234).length < 2 ^ (prefixWord ++ tailWord_6977234).sum := by decide
  have hdescent : baseEnd_6977234 < baseStart_6977234 := by decide
  rcases family_descends (prefixWord ++ tailWord_6977234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6977240 : List Nat := [2, 1, 2, 2, 3, 1, 1, 1, 1, 4, 5]
def baseStart_6977240 : Nat := 118140960795 + 6977240 * 2 ^ 59
def prefixEnd_6977240 : Nat := 4983230072969 + 3 ^ 40 * 6977240 * 2
def baseEnd_6977240 : Nat := 3582677761776386750112263

theorem tailTrace_6977240 : CollatzResearch.WordTrace tailWord_6977240 prefixEnd_6977240 3582677761776386750112263 := by
  unfold tailWord_6977240
  simp only [CollatzResearch.WordTrace]
  refine ⟨127240424621329286283788587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169653899495105715045051449 127240424621329286283788587)
  ·
    refine ⟨190860636931993929425682881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127240424621329286283788587 190860636931993929425682881)
    ·
      refine ⟨143145477698995447069262161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190860636931993929425682881 143145477698995447069262161)
      ·
        refine ⟨107359108274246585301946621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143145477698995447069262161 107359108274246585301946621)
        ·
          refine ⟨40259665602842469488229983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107359108274246585301946621 40259665602842469488229983)
          ·
            refine ⟨60389498404263704232344975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40259665602842469488229983 60389498404263704232344975)
            ·
              refine ⟨90584247606395556348517463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60389498404263704232344975 90584247606395556348517463)
              ·
                refine ⟨135876371409593334522776195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90584247606395556348517463 135876371409593334522776195)
                ·
                  refine ⟨203814557114390001784164293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 135876371409593334522776195 203814557114390001784164293)
                  ·
                    refine ⟨38215229458948125334530805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 203814557114390001784164293 38215229458948125334530805)
                    ·
                      refine ⟨3582677761776386750112263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38215229458948125334530805 3582677761776386750112263)
                      ·
                        rfl

theorem cell23_6977240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 1, 1, 4, 5].length) (baseStart_6977240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6977240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6977240 prefixEnd_6977240 := by exact prefixLift 6977240
  have htrace : WordTrace (prefixWord ++ tailWord_6977240) baseStart_6977240 baseEnd_6977240 := by
    simpa [prefixWord, tailWord_6977240, baseEnd_6977240] using wordTrace_append hprefix tailTrace_6977240
  have hstable : (prefixWord ++ tailWord_6977240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6977240).length < 2 ^ (prefixWord ++ tailWord_6977240).sum := by decide
  have hdescent : baseEnd_6977240 < baseStart_6977240 := by decide
  rcases family_descends (prefixWord ++ tailWord_6977240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6977260 : List Nat := [2, 2, 1, 1, 2, 2, 2, 1, 4, 6]
def baseStart_6977260 : Nat := 118140960795 + 6977260 * 2 ^ 59
def prefixEnd_6977260 : Nat := 4983230072969 + 3 ^ 40 * 6977260 * 2
def baseEnd_6977260 : Nat := 1194229343796492223954057

theorem tailTrace_6977260 : CollatzResearch.WordTrace tailWord_6977260 prefixEnd_6977260 1194229343796492223954057 := by
  unfold tailWord_6977260
  simp only [CollatzResearch.WordTrace]
  refine ⟨127240789351293057991652617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169654385801724077322203489 127240789351293057991652617)
  ·
    refine ⟨95430592013469793493739463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127240789351293057991652617 95430592013469793493739463)
    ·
      refine ⟨143145888020204690240609195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95430592013469793493739463 143145888020204690240609195)
      ·
        refine ⟨214718832030307035360913793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143145888020204690240609195 214718832030307035360913793)
        ·
          refine ⟨161039124022730276520685345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 214718832030307035360913793 161039124022730276520685345)
          ·
            refine ⟨120779343017047707390514009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161039124022730276520685345 120779343017047707390514009)
            ·
              refine ⟨90584507262785780542885507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120779343017047707390514009 90584507262785780542885507)
              ·
                refine ⟨135876760894178670814328261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90584507262785780542885507 135876760894178670814328261)
                ·
                  refine ⟨25476892667658500777686549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 135876760894178670814328261 25476892667658500777686549)
                  ·
                    refine ⟨1194229343796492223954057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25476892667658500777686549 1194229343796492223954057)
                    ·
                      rfl

theorem cell23_6977260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 6].length) (baseStart_6977260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6977260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6977260 prefixEnd_6977260 := by exact prefixLift 6977260
  have htrace : WordTrace (prefixWord ++ tailWord_6977260) baseStart_6977260 baseEnd_6977260 := by
    simpa [prefixWord, tailWord_6977260, baseEnd_6977260] using wordTrace_append hprefix tailTrace_6977260
  have hstable : (prefixWord ++ tailWord_6977260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6977260).length < 2 ^ (prefixWord ++ tailWord_6977260).sum := by decide
  have hdescent : baseEnd_6977260 < baseStart_6977260 := by decide
  rcases family_descends (prefixWord ++ tailWord_6977260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6977278 : List Nat := [4, 2, 2, 1, 3, 1, 1, 3, 2, 1, 3]
def baseStart_6977278 : Nat := 118140960795 + 6977278 * 2 ^ 59
def prefixEnd_6977278 : Nat := 4983230072969 + 3 ^ 40 * 6977278 * 2
def baseEnd_6977278 : Nat := 3582697274041257601437089

theorem tailTrace_6977278 : CollatzResearch.WordTrace tailWord_6977278 prefixEnd_6977278 3582697274041257601437089 := by
  unfold tailWord_6977278
  simp only [CollatzResearch.WordTrace]
  refine ⟨31810279402065113132182561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 169654823477680603371640325 31810279402065113132182561)
  ·
    refine ⟨23857709551548834849136921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31810279402065113132182561 23857709551548834849136921)
    ·
      refine ⟨17893282163661626136852691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23857709551548834849136921 17893282163661626136852691)
      ·
        refine ⟨26839923245492439205279037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17893282163661626136852691 26839923245492439205279037)
        ·
          refine ⟨10064971217059664701979639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26839923245492439205279037 10064971217059664701979639)
          ·
            refine ⟨15097456825589497052969459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10064971217059664701979639 15097456825589497052969459)
            ·
              refine ⟨22646185238384245579454189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15097456825589497052969459 22646185238384245579454189)
              ·
                refine ⟨8492319464394092092295321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22646185238384245579454189 8492319464394092092295321)
                ·
                  refine ⟨6369239598295569069221491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8492319464394092092295321 6369239598295569069221491)
                  ·
                    refine ⟨9553859397443353603832237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6369239598295569069221491 9553859397443353603832237)
                    ·
                      refine ⟨3582697274041257601437089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9553859397443353603832237 3582697274041257601437089)
                      ·
                        rfl

theorem cell23_6977278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 3, 2, 1, 3].length) (baseStart_6977278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6977278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6977278 prefixEnd_6977278 := by exact prefixLift 6977278
  have htrace : WordTrace (prefixWord ++ tailWord_6977278) baseStart_6977278 baseEnd_6977278 := by
    simpa [prefixWord, tailWord_6977278, baseEnd_6977278] using wordTrace_append hprefix tailTrace_6977278
  have hstable : (prefixWord ++ tailWord_6977278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6977278).length < 2 ^ (prefixWord ++ tailWord_6977278).sum := by decide
  have hdescent : baseEnd_6977278 < baseStart_6977278 := by decide
  rcases family_descends (prefixWord ++ tailWord_6977278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6977324 : List Nat := [2, 2, 1, 1, 1, 6, 1, 4, 5]
def baseStart_6977324 : Nat := 118140960795 + 6977324 * 2 ^ 59
def prefixEnd_6977324 : Nat := 4983230072969 + 3 ^ 40 * 6977324 * 2
def baseEnd_6977324 : Nat := 398080099350151602384653

theorem tailTrace_6977324 : CollatzResearch.WordTrace tailWord_6977324 prefixEnd_6977324 398080099350151602384653 := by
  unfold tailWord_6977324
  simp only [CollatzResearch.WordTrace]
  refine ⟨127241956487177127456817513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169655941982902836609090017 127241956487177127456817513)
  ·
    refine ⟨95431467365382845592613135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127241956487177127456817513 95431467365382845592613135)
    ·
      refine ⟨143147201048074268388919703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95431467365382845592613135 143147201048074268388919703)
      ·
        refine ⟨214720801572111402583379555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143147201048074268388919703 214720801572111402583379555)
        ·
          refine ⟨322081202358167103875069333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214720801572111402583379555 322081202358167103875069333)
          ·
            refine ⟨15097556360539082994143875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 322081202358167103875069333 15097556360539082994143875)
            ·
              refine ⟨22646334540808624491215813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15097556360539082994143875 22646334540808624491215813)
              ·
                refine ⟨4246187726401617092102965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22646334540808624491215813 4246187726401617092102965)
                ·
                  refine ⟨398080099350151602384653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4246187726401617092102965 398080099350151602384653)
                  ·
                    rfl

theorem cell23_6977324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 4, 5].length) (baseStart_6977324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6977324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6977324 prefixEnd_6977324 := by exact prefixLift 6977324
  have htrace : WordTrace (prefixWord ++ tailWord_6977324) baseStart_6977324 baseEnd_6977324 := by
    simpa [prefixWord, tailWord_6977324, baseEnd_6977324] using wordTrace_append hprefix tailTrace_6977324
  have hstable : (prefixWord ++ tailWord_6977324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6977324).length < 2 ^ (prefixWord ++ tailWord_6977324).sum := by decide
  have hdescent : baseEnd_6977324 < baseStart_6977324 := by decide
  rcases family_descends (prefixWord ++ tailWord_6977324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6977407 : List Nat := [1, 1, 2, 2, 1, 1, 3, 1, 1, 7, 3]
def baseStart_6977407 : Nat := 118140960795 + 6977407 * 2 ^ 59
def prefixEnd_6977407 : Nat := 4983230072969 + 3 ^ 40 * 6977407 * 2
def baseEnd_6977407 : Nat := 3582763513045687596723995

theorem tailTrace_6977407 : CollatzResearch.WordTrace tailWord_6977407 prefixEnd_6977407 3582763513045687596723995 := by
  unfold tailWord_6977407
  simp only [CollatzResearch.WordTrace]
  refine ⟨254486940233053560088906475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169657960155369040059270983 254486940233053560088906475)
  ·
    refine ⟨381730410349580340133359713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254486940233053560088906475 381730410349580340133359713)
    ·
      refine ⟨286297807762185255100019785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 381730410349580340133359713 286297807762185255100019785)
      ·
        refine ⟨214723355821638941325014839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 286297807762185255100019785 214723355821638941325014839)
        ·
          refine ⟨322085033732458411987522259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214723355821638941325014839 322085033732458411987522259)
          ·
            refine ⟨483127550598687617981283389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 322085033732458411987522259 483127550598687617981283389)
            ·
              refine ⟨181172831474507856742981271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 483127550598687617981283389 181172831474507856742981271)
              ·
                refine ⟨271759247211761785114471907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 181172831474507856742981271 271759247211761785114471907)
                ·
                  refine ⟨407638870817642677671707861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 271759247211761785114471907 407638870817642677671707861)
                  ·
                    refine ⟨9554036034788500257930653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 407638870817642677671707861 9554036034788500257930653)
                    ·
                      refine ⟨3582763513045687596723995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9554036034788500257930653 3582763513045687596723995)
                      ·
                        rfl

theorem cell23_6977407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 7, 3].length) (baseStart_6977407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6977407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6977407 prefixEnd_6977407 := by exact prefixLift 6977407
  have htrace : WordTrace (prefixWord ++ tailWord_6977407) baseStart_6977407 baseEnd_6977407 := by
    simpa [prefixWord, tailWord_6977407, baseEnd_6977407] using wordTrace_append hprefix tailTrace_6977407
  have hstable : (prefixWord ++ tailWord_6977407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6977407).length < 2 ^ (prefixWord ++ tailWord_6977407).sum := by decide
  have hdescent : baseEnd_6977407 < baseStart_6977407 := by decide
  rcases family_descends (prefixWord ++ tailWord_6977407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6977424 : List Nat := [2, 1, 1, 1, 1, 1, 2, 3, 7, 1, 3]
def baseStart_6977424 : Nat := 118140960795 + 6977424 * 2 ^ 59
def prefixEnd_6977424 : Nat := 4983230072969 + 3 ^ 40 * 6977424 * 2
def baseEnd_6977424 : Nat := 3582772242216814030211417

theorem tailTrace_6977424 : CollatzResearch.WordTrace tailWord_6977424 prefixEnd_6977424 3582772242216814030211417 := by
  unfold tailWord_6977424
  simp only [CollatzResearch.WordTrace]
  refine ⟨127243780136995985996137663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169658373515994647994850217 127243780136995985996137663)
  ·
    refine ⟨190865670205493978994206495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127243780136995985996137663 190865670205493978994206495)
    ·
      refine ⟨286298505308240968491309743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190865670205493978994206495 286298505308240968491309743)
      ·
        refine ⟨429447757962361452736964615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286298505308240968491309743 429447757962361452736964615)
        ·
          refine ⟨644171636943542179105446923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 429447757962361452736964615 644171636943542179105446923)
          ·
            refine ⟨966257455415313268658170385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 644171636943542179105446923 966257455415313268658170385)
            ·
              refine ⟨724693091561484951493627789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 966257455415313268658170385 724693091561484951493627789)
              ·
                refine ⟨271759909335556856810110421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 724693091561484951493627789 271759909335556856810110421)
                ·
                  refine ⟨6369372875052113831486963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 271759909335556856810110421 6369372875052113831486963)
                  ·
                    refine ⟨9554059312578170747230445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6369372875052113831486963 9554059312578170747230445)
                    ·
                      refine ⟨3582772242216814030211417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9554059312578170747230445 3582772242216814030211417)
                      ·
                        rfl

theorem cell23_6977424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 7, 1, 3].length) (baseStart_6977424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6977424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6977424 prefixEnd_6977424 := by exact prefixLift 6977424
  have htrace : WordTrace (prefixWord ++ tailWord_6977424) baseStart_6977424 baseEnd_6977424 := by
    simpa [prefixWord, tailWord_6977424, baseEnd_6977424] using wordTrace_append hprefix tailTrace_6977424
  have hstable : (prefixWord ++ tailWord_6977424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6977424).length < 2 ^ (prefixWord ++ tailWord_6977424).sum := by decide
  have hdescent : baseEnd_6977424 < baseStart_6977424 := by decide
  rcases family_descends (prefixWord ++ tailWord_6977424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6977448 : List Nat := [2, 1, 6, 2, 1, 1, 1, 3, 6]
def baseStart_6977448 : Nat := 118140960795 + 6977448 * 2 ^ 59
def prefixEnd_6977448 : Nat := 4983230072969 + 3 ^ 40 * 6977448 * 2
def baseEnd_6977448 : Nat := 398087173972502437367923

theorem tailTrace_6977448 : CollatzResearch.WordTrace tailWord_6977448 prefixEnd_6977448 398087173972502437367923 := by
  unfold tailWord_6977448
  simp only [CollatzResearch.WordTrace]
  refine ⟨127244217812952512045574499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169658957083936682727432665 127244217812952512045574499)
  ·
    refine ⟨190866326719428768068361749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127244217812952512045574499 190866326719428768068361749)
    ·
      refine ⟨8946859064973223503204457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 190866326719428768068361749 8946859064973223503204457)
      ·
        refine ⟨6710144298729917627403343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8946859064973223503204457 6710144298729917627403343)
        ·
          refine ⟨10065216448094876441105015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6710144298729917627403343 10065216448094876441105015)
          ·
            refine ⟨15097824672142314661657523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10065216448094876441105015 15097824672142314661657523)
            ·
              refine ⟨22646737008213471992486285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15097824672142314661657523 22646737008213471992486285)
              ·
                refine ⟨8492526378080051997182357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22646737008213471992486285 8492526378080051997182357)
                ·
                  refine ⟨398087173972502437367923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8492526378080051997182357 398087173972502437367923)
                  ·
                    rfl

theorem cell23_6977448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 3, 6].length) (baseStart_6977448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6977448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6977448 prefixEnd_6977448 := by exact prefixLift 6977448
  have htrace : WordTrace (prefixWord ++ tailWord_6977448) baseStart_6977448 baseEnd_6977448 := by
    simpa [prefixWord, tailWord_6977448, baseEnd_6977448] using wordTrace_append hprefix tailTrace_6977448
  have hstable : (prefixWord ++ tailWord_6977448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6977448).length < 2 ^ (prefixWord ++ tailWord_6977448).sum := by decide
  have hdescent : baseEnd_6977448 < baseStart_6977448 := by decide
  rcases family_descends (prefixWord ++ tailWord_6977448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6977461 : List Nat := [1, 3, 3, 2, 1, 2, 3, 2, 1, 5]
def baseStart_6977461 : Nat := 118140960795 + 6977461 * 2 ^ 59
def prefixEnd_6977461 : Nat := 4983230072969 + 3 ^ 40 * 6977461 * 2
def baseEnd_6977461 : Nat := 1194263747000343461816249

theorem tailTrace_6977461 : CollatzResearch.WordTrace tailWord_6977461 prefixEnd_6977461 1194263747000343461816249 := by
  unfold tailWord_6977461
  simp only [CollatzResearch.WordTrace]
  refine ⟨254488909774857927311372237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169659273183238618207581491 254488909774857927311372237)
  ·
    refine ⟨95433341165571722741764589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 254488909774857927311372237 95433341165571722741764589)
    ·
      refine ⟨35787502937089396028161721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95433341165571722741764589 35787502937089396028161721)
      ·
        refine ⟨26840627202817047021121291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35787502937089396028161721 26840627202817047021121291)
        ·
          refine ⟨40260940804225570531681937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26840627202817047021121291 40260940804225570531681937)
          ·
            refine ⟨30195705603169177898761453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40260940804225570531681937 30195705603169177898761453)
            ·
              refine ⟨11323389601188441712035545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30195705603169177898761453 11323389601188441712035545)
              ·
                refine ⟨8492542200891331284026659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11323389601188441712035545 8492542200891331284026659)
                ·
                  refine ⟨12738813301336996926039989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8492542200891331284026659 12738813301336996926039989)
                  ·
                    refine ⟨1194263747000343461816249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12738813301336996926039989 1194263747000343461816249)
                    ·
                      rfl

theorem cell23_6977461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 3, 2, 1, 5].length) (baseStart_6977461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6977461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6977461 prefixEnd_6977461 := by exact prefixLift 6977461
  have htrace : WordTrace (prefixWord ++ tailWord_6977461) baseStart_6977461 baseEnd_6977461 := by
    simpa [prefixWord, tailWord_6977461, baseEnd_6977461] using wordTrace_append hprefix tailTrace_6977461
  have hstable : (prefixWord ++ tailWord_6977461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6977461).length < 2 ^ (prefixWord ++ tailWord_6977461).sum := by decide
  have hdescent : baseEnd_6977461 < baseStart_6977461 := by decide
  rcases family_descends (prefixWord ++ tailWord_6977461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6977464 : List Nat := [2, 1, 2, 1, 2, 3, 3, 1, 3, 1, 4]
def baseStart_6977464 : Nat := 118140960795 + 6977464 * 2 ^ 59
def prefixEnd_6977464 : Nat := 4983230072969 + 3 ^ 40 * 6977464 * 2
def baseEnd_6977464 : Nat := 3582792781442993873711233

theorem tailTrace_6977464 : CollatzResearch.WordTrace tailWord_6977464 prefixEnd_6977464 3582792781442993873711233 := by
  unfold tailWord_6977464
  simp only [CollatzResearch.WordTrace]
  refine ⟨127244509596923529411865723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169659346129231372549154297 127244509596923529411865723)
  ·
    refine ⟨190866764395385294117798585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127244509596923529411865723 190866764395385294117798585)
    ·
      refine ⟨143150073296538970588348939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190866764395385294117798585 143150073296538970588348939)
      ·
        refine ⟨214725109944808455882523409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143150073296538970588348939 214725109944808455882523409)
        ·
          refine ⟨161043832458606341911892557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 214725109944808455882523409 161043832458606341911892557)
          ·
            refine ⟨60391437171977378216959709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 161043832458606341911892557 60391437171977378216959709)
            ·
              refine ⟨22646788939491516831359891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60391437171977378216959709 22646788939491516831359891)
              ·
                refine ⟨33970183409237275247039837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22646788939491516831359891 33970183409237275247039837)
                ·
                  refine ⟨12738818778463978217639939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33970183409237275247039837 12738818778463978217639939)
                  ·
                    refine ⟨19108228167695967326459909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12738818778463978217639939 19108228167695967326459909)
                    ·
                      refine ⟨3582792781442993873711233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19108228167695967326459909 3582792781442993873711233)
                      ·
                        rfl

theorem cell23_6977464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 1, 3, 1, 4].length) (baseStart_6977464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6977464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6977464 prefixEnd_6977464 := by exact prefixLift 6977464
  have htrace : WordTrace (prefixWord ++ tailWord_6977464) baseStart_6977464 baseEnd_6977464 := by
    simpa [prefixWord, tailWord_6977464, baseEnd_6977464] using wordTrace_append hprefix tailTrace_6977464
  have hstable : (prefixWord ++ tailWord_6977464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6977464).length < 2 ^ (prefixWord ++ tailWord_6977464).sum := by decide
  have hdescent : baseEnd_6977464 < baseStart_6977464 := by decide
  rcases family_descends (prefixWord ++ tailWord_6977464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6977467 : List Nat := [1, 1, 1, 1, 1, 2, 2, 3, 5, 1, 5]
def baseStart_6977467 : Nat := 118140960795 + 6977467 * 2 ^ 59
def prefixEnd_6977467 : Nat := 4983230072969 + 3 ^ 40 * 6977467 * 2
def baseEnd_6977467 : Nat := 3582794321884957361973719

theorem tailTrace_6977467 : CollatzResearch.WordTrace tailWord_6977467 prefixEnd_6977467 3582794321884957361973719 := by
  unfold tailWord_6977467
  simp only [CollatzResearch.WordTrace]
  refine ⟨254489128612836190336090655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169659419075224126890727103 254489128612836190336090655)
  ·
    refine ⟨381733692919254285504135983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254489128612836190336090655 381733692919254285504135983)
    ·
      refine ⟨572600539378881428256203975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 381733692919254285504135983 572600539378881428256203975)
      ·
        refine ⟨858900809068322142384305963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 572600539378881428256203975 858900809068322142384305963)
        ·
          refine ⟨1288351213602483213576458945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 858900809068322142384305963 1288351213602483213576458945)
          ·
            refine ⟨966263410201862410182344209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1288351213602483213576458945 966263410201862410182344209)
            ·
              refine ⟨724697557651396807636758157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 966263410201862410182344209 724697557651396807636758157)
              ·
                refine ⟨271761584119273802863784309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 724697557651396807636758157 271761584119273802863784309)
                ·
                  refine ⟨25477648511181919018479779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 271761584119273802863784309 25477648511181919018479779)
                  ·
                    refine ⟨38216472766772878527719669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25477648511181919018479779 38216472766772878527719669)
                    ·
                      refine ⟨3582794321884957361973719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38216472766772878527719669 3582794321884957361973719)
                      ·
                        rfl

theorem cell23_6977467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5, 1, 5].length) (baseStart_6977467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6977467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6977467 prefixEnd_6977467 := by exact prefixLift 6977467
  have htrace : WordTrace (prefixWord ++ tailWord_6977467) baseStart_6977467 baseEnd_6977467 := by
    simpa [prefixWord, tailWord_6977467, baseEnd_6977467] using wordTrace_append hprefix tailTrace_6977467
  have hstable : (prefixWord ++ tailWord_6977467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6977467).length < 2 ^ (prefixWord ++ tailWord_6977467).sum := by decide
  have hdescent : baseEnd_6977467 < baseStart_6977467 := by decide
  rcases family_descends (prefixWord ++ tailWord_6977467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6977477 : List Nat := [1, 3, 1, 1, 1, 1, 1, 4, 3, 1, 6]
def baseStart_6977477 : Nat := 118140960795 + 6977477 * 2 ^ 59
def prefixEnd_6977477 : Nat := 4983230072969 + 3 ^ 40 * 6977477 * 2
def baseEnd_6977477 : Nat := 3582799456691502322848673

theorem tailTrace_6977477 : CollatzResearch.WordTrace tailWord_6977477 prefixEnd_6977477 3582799456691502322848673 := by
  unfold tailWord_6977477
  simp only [CollatzResearch.WordTrace]
  refine ⟨254489493342799962043954685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169659662228533308029303123 254489493342799962043954685)
  ·
    refine ⟨95433560003549985766483007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 254489493342799962043954685 95433560003549985766483007)
    ·
      refine ⟨143150340005324978649724511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95433560003549985766483007 143150340005324978649724511)
      ·
        refine ⟨214725510007987467974586767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143150340005324978649724511 214725510007987467974586767)
        ·
          refine ⟨322088265011981201961880151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214725510007987467974586767 322088265011981201961880151)
          ·
            refine ⟨483132397517971802942820227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 322088265011981201961880151 483132397517971802942820227)
            ·
              refine ⟨724698596276957704414230341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 483132397517971802942820227 724698596276957704414230341)
              ·
                refine ⟨135880986801929569577668189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 724698596276957704414230341 135880986801929569577668189)
                ·
                  refine ⟨50955370050723588591625571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 135880986801929569577668189 50955370050723588591625571)
                  ·
                    refine ⟨76433055076085382887438357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50955370050723588591625571 76433055076085382887438357)
                    ·
                      refine ⟨3582799456691502322848673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76433055076085382887438357 3582799456691502322848673)
                      ·
                        rfl

theorem cell23_6977477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 3, 1, 6].length) (baseStart_6977477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6977477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6977477 prefixEnd_6977477 := by exact prefixLift 6977477
  have htrace : WordTrace (prefixWord ++ tailWord_6977477) baseStart_6977477 baseEnd_6977477 := by
    simpa [prefixWord, tailWord_6977477, baseEnd_6977477] using wordTrace_append hprefix tailTrace_6977477
  have hstable : (prefixWord ++ tailWord_6977477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6977477).length < 2 ^ (prefixWord ++ tailWord_6977477).sum := by decide
  have hdescent : baseEnd_6977477 < baseStart_6977477 := by decide
  rcases family_descends (prefixWord ++ tailWord_6977477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6977481 : List Nat := [1, 2, 1, 1, 2, 1, 2, 4, 5, 2, 2]
def baseStart_6977481 : Nat := 118140960795 + 6977481 * 2 ^ 59
def prefixEnd_6977481 : Nat := 4983230072969 + 3 ^ 40 * 6977481 * 2
def baseEnd_6977481 : Nat := 3582801510614120307198655

theorem tailTrace_6977481 : CollatzResearch.WordTrace tailWord_6977481 prefixEnd_6977481 3582801510614120307198655 := by
  unfold tailWord_6977481
  simp only [CollatzResearch.WordTrace]
  refine ⟨254489639234785470727100297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169659759489856980484733531 254489639234785470727100297)
  ·
    refine ⟨190867229426089103045325223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254489639234785470727100297 190867229426089103045325223)
    ·
      refine ⟨286300844139133654567987835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190867229426089103045325223 286300844139133654567987835)
      ·
        refine ⟨429451266208700481851981753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286300844139133654567987835 429451266208700481851981753)
        ·
          refine ⟨322088449656525361388986315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 429451266208700481851981753 322088449656525361388986315)
          ·
            refine ⟨483132674484788042083479473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 322088449656525361388986315 483132674484788042083479473)
            ·
              refine ⟨362349505863591031562609605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 483132674484788042083479473 362349505863591031562609605)
              ·
                refine ⟨67940532349423318417989301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 362349505863591031562609605 67940532349423318417989301)
                ·
                  refine ⟨6369424907758436101686497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 67940532349423318417989301 6369424907758436101686497)
                  ·
                    refine ⟨4777068680818827076264873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6369424907758436101686497 4777068680818827076264873)
                    ·
                      refine ⟨3582801510614120307198655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4777068680818827076264873 3582801510614120307198655)
                      ·
                        rfl

theorem cell23_6977481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 4, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 4, 5, 2, 2].length) (baseStart_6977481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6977481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6977481 prefixEnd_6977481 := by exact prefixLift 6977481
  have htrace : WordTrace (prefixWord ++ tailWord_6977481) baseStart_6977481 baseEnd_6977481 := by
    simpa [prefixWord, tailWord_6977481, baseEnd_6977481] using wordTrace_append hprefix tailTrace_6977481
  have hstable : (prefixWord ++ tailWord_6977481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6977481).length < 2 ^ (prefixWord ++ tailWord_6977481).sum := by decide
  have hdescent : baseEnd_6977481 < baseStart_6977481 := by decide
  rcases family_descends (prefixWord ++ tailWord_6977481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6977521 : List Nat := [1, 2, 2, 2, 5, 1, 3, 7]
def baseStart_6977521 : Nat := 118140960795 + 6977521 * 2 ^ 59
def prefixEnd_6977521 : Nat := 4983230072969 + 3 ^ 40 * 6977521 * 2
def baseEnd_6977521 : Nat := 132697112957048153729573

theorem tailTrace_6977521 : CollatzResearch.WordTrace tailWord_6977521 prefixEnd_6977521 132697112957048153729573 := by
  unfold tailWord_6977521
  simp only [CollatzResearch.WordTrace]
  refine ⟨254491098154640557558556417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169660732103093705039037611 254491098154640557558556417)
  ·
    refine ⟨190868323615980418168917313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254491098154640557558556417 190868323615980418168917313)
    ·
      refine ⟨143151242711985313626687985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190868323615980418168917313 143151242711985313626687985)
      ·
        refine ⟨107363432033988985220015989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143151242711985313626687985 107363432033988985220015989)
        ·
          refine ⟨10065321753186467364376499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 107363432033988985220015989 10065321753186467364376499)
          ·
            refine ⟨15097982629779701046564749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10065321753186467364376499 15097982629779701046564749)
            ·
              refine ⟨5661743486167387892461781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15097982629779701046564749 5661743486167387892461781)
              ·
                refine ⟨132697112957048153729573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5661743486167387892461781 132697112957048153729573)
                ·
                  rfl

theorem cell23_6977521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 3, 7].length) (baseStart_6977521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6977521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6977521 prefixEnd_6977521 := by exact prefixLift 6977521
  have htrace : WordTrace (prefixWord ++ tailWord_6977521) baseStart_6977521 baseEnd_6977521 := by
    simpa [prefixWord, tailWord_6977521, baseEnd_6977521] using wordTrace_append hprefix tailTrace_6977521
  have hstable : (prefixWord ++ tailWord_6977521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6977521).length < 2 ^ (prefixWord ++ tailWord_6977521).sum := by decide
  have hdescent : baseEnd_6977521 < baseStart_6977521 := by decide
  rcases family_descends (prefixWord ++ tailWord_6977521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6977631 : List Nat := [1, 1, 2, 3, 1, 1, 2, 1, 4, 5, 2]
def baseStart_6977631 : Nat := 118140960795 + 6977631 * 2 ^ 59
def prefixEnd_6977631 : Nat := 4983230072969 + 3 ^ 40 * 6977631 * 2
def baseEnd_6977631 : Nat := 3582878532712294720322965

theorem tailTrace_6977631 : CollatzResearch.WordTrace tailWord_6977631 prefixEnd_6977631 3582878532712294720322965 := by
  unfold tailWord_6977631
  simp only [CollatzResearch.WordTrace]
  refine ⟨254495110184242046345060747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169663406789494697563373831 254495110184242046345060747)
  ·
    refine ⟨381742665276363069517591121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254495110184242046345060747 381742665276363069517591121)
    ·
      refine ⟨286306998957272302138193341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 381742665276363069517591121 286306998957272302138193341)
      ·
        refine ⟨107365124608977113301822503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 286306998957272302138193341 107365124608977113301822503)
        ·
          refine ⟨161047686913465669952733755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107365124608977113301822503 161047686913465669952733755)
          ·
            refine ⟨241571530370198504929100633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161047686913465669952733755 241571530370198504929100633)
            ·
              refine ⟨181178647777648878696825475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 241571530370198504929100633 181178647777648878696825475)
              ·
                refine ⟨271767971666473318045238213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 181178647777648878696825475 271767971666473318045238213)
                ·
                  refine ⟨50956494687463747133482165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 271767971666473318045238213 50956494687463747133482165)
                  ·
                    refine ⟨4777171376949726293763953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50956494687463747133482165 4777171376949726293763953)
                    ·
                      refine ⟨3582878532712294720322965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4777171376949726293763953 3582878532712294720322965)
                      ·
                        rfl

theorem cell23_6977631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 4, 5, 2].length) (baseStart_6977631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6977631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6977631 prefixEnd_6977631 := by exact prefixLift 6977631
  have htrace : WordTrace (prefixWord ++ tailWord_6977631) baseStart_6977631 baseEnd_6977631 := by
    simpa [prefixWord, tailWord_6977631, baseEnd_6977631] using wordTrace_append hprefix tailTrace_6977631
  have hstable : (prefixWord ++ tailWord_6977631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6977631).length < 2 ^ (prefixWord ++ tailWord_6977631).sum := by decide
  have hdescent : baseEnd_6977631 < baseStart_6977631 := by decide
  rcases family_descends (prefixWord ++ tailWord_6977631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6977641 : List Nat := [1, 2, 1, 1, 1, 5, 4, 1, 2, 5]
def baseStart_6977641 : Nat := 118140960795 + 6977641 * 2 ^ 59
def prefixEnd_6977641 : Nat := 4983230072969 + 3 ^ 40 * 6977641 * 2
def baseEnd_6977641 : Nat := 1194294555839613227065973

theorem tailTrace_6977641 : CollatzResearch.WordTrace tailWord_6977641 prefixEnd_6977641 1194294555839613227065973 := by
  unfold tailWord_6977641
  simp only [CollatzResearch.WordTrace]
  refine ⟨254495474914205818052924777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169663649942803878701949851 254495474914205818052924777)
  ·
    refine ⟨190871606185654363539693583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254495474914205818052924777 190871606185654363539693583)
    ·
      refine ⟨286307409278481545309540375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190871606185654363539693583 286307409278481545309540375)
      ·
        refine ⟨429461113917722317964310563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286307409278481545309540375 429461113917722317964310563)
        ·
          refine ⟨644191670876583476946465845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 429461113917722317964310563 644191670876583476946465845)
          ·
            refine ⟨60392969144679700963731173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 644191670876583476946465845 60392969144679700963731173)
            ·
              refine ⟨11323681714627443930699595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60392969144679700963731173 11323681714627443930699595)
              ·
                refine ⟨16985522571941165896049393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11323681714627443930699595 16985522571941165896049393)
                ·
                  refine ⟨12739141928955874422037045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16985522571941165896049393 12739141928955874422037045)
                  ·
                    refine ⟨1194294555839613227065973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12739141928955874422037045 1194294555839613227065973)
                    ·
                      rfl

theorem cell23_6977641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 4, 1, 2, 5].length) (baseStart_6977641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6977641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6977641 prefixEnd_6977641 := by exact prefixLift 6977641
  have htrace : WordTrace (prefixWord ++ tailWord_6977641) baseStart_6977641 baseEnd_6977641 := by
    simpa [prefixWord, tailWord_6977641, baseEnd_6977641] using wordTrace_append hprefix tailTrace_6977641
  have hstable : (prefixWord ++ tailWord_6977641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6977641).length < 2 ^ (prefixWord ++ tailWord_6977641).sum := by decide
  have hdescent : baseEnd_6977641 < baseStart_6977641 := by decide
  rcases family_descends (prefixWord ++ tailWord_6977641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6977664 : List Nat := [2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 5]
def baseStart_6977664 : Nat := 118140960795 + 6977664 * 2 ^ 59
def prefixEnd_6977664 : Nat := 4983230072969 + 3 ^ 40 * 6977664 * 2
def baseEnd_6977664 : Nat := 3582895477573893091210313

theorem tailTrace_6977664 : CollatzResearch.WordTrace tailWord_6977664 prefixEnd_6977664 3582895477573893091210313 := by
  unfold tailWord_6977664
  simp only [CollatzResearch.WordTrace]
  refine ⟨127248156896561246490506023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169664209195414995320674697 127248156896561246490506023)
  ·
    refine ⟨190872235344841869735759035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127248156896561246490506023 190872235344841869735759035)
    ·
      refine ⟨286308353017262804603638553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190872235344841869735759035 286308353017262804603638553)
      ·
        refine ⟨214731264762947103452728915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 286308353017262804603638553 214731264762947103452728915)
        ·
          refine ⟨322096897144420655179093373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214731264762947103452728915 322096897144420655179093373)
          ·
            refine ⟨120786336429157745692160015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 322096897144420655179093373 120786336429157745692160015)
            ·
              refine ⟨181179504643736618538240023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120786336429157745692160015 181179504643736618538240023)
              ·
                refine ⟨271769256965604927807360035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 181179504643736618538240023 271769256965604927807360035)
                ·
                  refine ⟨407653885448407391711040053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 271769256965604927807360035 407653885448407391711040053)
                  ·
                    refine ⟨38217551760788192972910005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 407653885448407391711040053 38217551760788192972910005)
                    ·
                      refine ⟨3582895477573893091210313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38217551760788192972910005 3582895477573893091210313)
                      ·
                        rfl

theorem cell23_6977664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 5].length) (baseStart_6977664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6977664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6977664 prefixEnd_6977664 := by exact prefixLift 6977664
  have htrace : WordTrace (prefixWord ++ tailWord_6977664) baseStart_6977664 baseEnd_6977664 := by
    simpa [prefixWord, tailWord_6977664, baseEnd_6977664] using wordTrace_append hprefix tailTrace_6977664
  have hstable : (prefixWord ++ tailWord_6977664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6977664).length < 2 ^ (prefixWord ++ tailWord_6977664).sum := by decide
  have hdescent : baseEnd_6977664 < baseStart_6977664 := by decide
  rcases family_descends (prefixWord ++ tailWord_6977664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6977695 : List Nat := [1, 1, 2, 6, 1, 3, 1, 1, 2, 1, 4]
def baseStart_6977695 : Nat := 118140960795 + 6977695 * 2 ^ 59
def prefixEnd_6977695 : Nat := 4983230072969 + 3 ^ 40 * 6977695 * 2
def baseEnd_6977695 : Nat := 3582911395474182469922671

theorem tailTrace_6977695 : CollatzResearch.WordTrace tailWord_6977695 prefixEnd_6977695 3582911395474182469922671 := by
  unfold tailWord_6977695
  simp only [CollatzResearch.WordTrace]
  refine ⟨254497444456010185275390539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169664962970673456850260359 254497444456010185275390539)
  ·
    refine ⟨381746166684015277913085809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254497444456010185275390539 381746166684015277913085809)
    ·
      refine ⟨286309625013011458434814357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 381746166684015277913085809 286309625013011458434814357)
      ·
        refine ⟨13420763672484912114131923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 286309625013011458434814357 13420763672484912114131923)
        ·
          refine ⟨20131145508727368171197885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13420763672484912114131923 20131145508727368171197885)
          ·
            refine ⟨7549179565772763064199207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20131145508727368171197885 7549179565772763064199207)
            ·
              refine ⟨11323769348659144596298811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7549179565772763064199207 11323769348659144596298811)
              ·
                refine ⟨16985654022988716894448217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11323769348659144596298811 16985654022988716894448217)
                ·
                  refine ⟨12739240517241537670836163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16985654022988716894448217 12739240517241537670836163)
                  ·
                    refine ⟨19108860775862306506254245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12739240517241537670836163 19108860775862306506254245)
                    ·
                      refine ⟨3582911395474182469922671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19108860775862306506254245 3582911395474182469922671)
                      ·
                        rfl

theorem cell23_6977695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_6977695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6977695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6977695 prefixEnd_6977695 := by exact prefixLift 6977695
  have htrace : WordTrace (prefixWord ++ tailWord_6977695) baseStart_6977695 baseEnd_6977695 := by
    simpa [prefixWord, tailWord_6977695, baseEnd_6977695] using wordTrace_append hprefix tailTrace_6977695
  have hstable : (prefixWord ++ tailWord_6977695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6977695).length < 2 ^ (prefixWord ++ tailWord_6977695).sum := by decide
  have hdescent : baseEnd_6977695 < baseStart_6977695 := by decide
  rcases family_descends (prefixWord ++ tailWord_6977695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6977738 : List Nat := [3, 1, 2, 1, 3, 1, 1, 1, 3, 5, 2]
def baseStart_6977738 : Nat := 118140960795 + 6977738 * 2 ^ 59
def prefixEnd_6977738 : Nat := 4983230072969 + 3 ^ 40 * 6977738 * 2
def baseEnd_6977738 : Nat := 3582933475142325801684973

theorem tailTrace_6977738 : CollatzResearch.WordTrace tailWord_6977738 prefixEnd_6977738 3582933475142325801684973 := by
  unfold tailWord_6977738
  simp only [CollatzResearch.WordTrace]
  refine ⟨63624753198713600904801467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169666008529902935746137245 63624753198713600904801467)
  ·
    refine ⟨95437129798070401357202201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63624753198713600904801467 95437129798070401357202201)
    ·
      refine ⟨71577847348552801017901651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95437129798070401357202201 71577847348552801017901651)
      ·
        refine ⟨107366771022829201526852477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71577847348552801017901651 107366771022829201526852477)
        ·
          refine ⟨40262539133560950572569679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107366771022829201526852477 40262539133560950572569679)
          ·
            refine ⟨60393808700341425858854519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40262539133560950572569679 60393808700341425858854519)
            ·
              refine ⟨90590713050512138788281779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60393808700341425858854519 90590713050512138788281779)
              ·
                refine ⟨135886069575768208182422669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90590713050512138788281779 135886069575768208182422669)
                ·
                  refine ⟨50957276090913078068408501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 135886069575768208182422669 50957276090913078068408501)
                  ·
                    refine ⟨4777244633523101068913297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50957276090913078068408501 4777244633523101068913297)
                    ·
                      refine ⟨3582933475142325801684973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4777244633523101068913297 3582933475142325801684973)
                      ·
                        rfl

theorem cell23_6977738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 1, 3, 5, 2].length) (baseStart_6977738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6977738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6977738 prefixEnd_6977738 := by exact prefixLift 6977738
  have htrace : WordTrace (prefixWord ++ tailWord_6977738) baseStart_6977738 baseEnd_6977738 := by
    simpa [prefixWord, tailWord_6977738, baseEnd_6977738] using wordTrace_append hprefix tailTrace_6977738
  have hstable : (prefixWord ++ tailWord_6977738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6977738).length < 2 ^ (prefixWord ++ tailWord_6977738).sum := by decide
  have hdescent : baseEnd_6977738 < baseStart_6977738 := by decide
  rcases family_descends (prefixWord ++ tailWord_6977738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6977756 : List Nat := [2, 2, 5, 2, 1, 2, 1, 3, 1, 4]
def baseStart_6977756 : Nat := 118140960795 + 6977756 * 2 ^ 59
def prefixEnd_6977756 : Nat := 4983230072969 + 3 ^ 40 * 6977756 * 2
def baseEnd_6977756 : Nat := 1194314239264702243753297

theorem tailTrace_6977756 : CollatzResearch.WordTrace tailWord_6977756 prefixEnd_6977756 1194314239264702243753297 := by
  unfold tailWord_6977756
  simp only [CollatzResearch.WordTrace]
  refine ⟨127249834654394596346680561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169666446205859461795574081 127249834654394596346680561)
  ·
    refine ⟨95437375990795947260010421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127249834654394596346680561 95437375990795947260010421)
    ·
      refine ⟨8947253999137120055625977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 95437375990795947260010421 8947253999137120055625977)
      ·
        refine ⟨6710440499352840041719483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8947253999137120055625977 6710440499352840041719483)
        ·
          refine ⟨10065660749029260062579225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6710440499352840041719483 10065660749029260062579225)
          ·
            refine ⟨7549245561771945046934419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10065660749029260062579225 7549245561771945046934419)
            ·
              refine ⟨11323868342657917570401629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7549245561771945046934419 11323868342657917570401629)
              ·
                refine ⟨4246450628496719088900611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11323868342657917570401629 4246450628496719088900611)
                ·
                  refine ⟨6369675942745078633350917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4246450628496719088900611 6369675942745078633350917)
                  ·
                    refine ⟨1194314239264702243753297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6369675942745078633350917 1194314239264702243753297)
                    ·
                      rfl

theorem cell23_6977756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_6977756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6977756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6977756 prefixEnd_6977756 := by exact prefixLift 6977756
  have htrace : WordTrace (prefixWord ++ tailWord_6977756) baseStart_6977756 baseEnd_6977756 := by
    simpa [prefixWord, tailWord_6977756, baseEnd_6977756] using wordTrace_append hprefix tailTrace_6977756
  have hstable : (prefixWord ++ tailWord_6977756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6977756).length < 2 ^ (prefixWord ++ tailWord_6977756).sum := by decide
  have hdescent : baseEnd_6977756 < baseStart_6977756 := by decide
  rcases family_descends (prefixWord ++ tailWord_6977756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6977761 : List Nat := [1, 2, 3, 1, 3, 1, 2, 1, 3, 6]
def baseStart_6977761 : Nat := 118140960795 + 6977761 * 2 ^ 59
def prefixEnd_6977761 : Nat := 4983230072969 + 3 ^ 40 * 6977761 * 2
def baseEnd_6977761 : Nat := 1194315095065793070565789

theorem tailTrace_6977761 : CollatzResearch.WordTrace tailWord_6977761 prefixEnd_6977761 1194315095065793070565789 := by
  unfold tailWord_6977761
  simp only [CollatzResearch.WordTrace]
  refine ⟨254499851673771078547293137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169666567782514052364862091 254499851673771078547293137)
  ·
    refine ⟨190874888755328308910469853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254499851673771078547293137 190874888755328308910469853)
    ·
      refine ⟨71578083283248115841426195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 190874888755328308910469853 71578083283248115841426195)
      ·
        refine ⟨107367124924872173762139293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71578083283248115841426195 107367124924872173762139293)
        ·
          refine ⟨40262671846827065160802235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107367124924872173762139293 40262671846827065160802235)
          ·
            refine ⟨60394007770240597741203353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40262671846827065160802235 60394007770240597741203353)
            ·
              refine ⟨45295505827680448305902515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60394007770240597741203353 45295505827680448305902515)
              ·
                refine ⟨67943258741520672458853773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45295505827680448305902515 67943258741520672458853773)
                ·
                  refine ⟨25478722028070252172070165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67943258741520672458853773 25478722028070252172070165)
                  ·
                    refine ⟨1194315095065793070565789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25478722028070252172070165 1194315095065793070565789)
                    ·
                      rfl

theorem cell23_6977761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 1, 3, 6].length) (baseStart_6977761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6977761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6977761 prefixEnd_6977761 := by exact prefixLift 6977761
  have htrace : WordTrace (prefixWord ++ tailWord_6977761) baseStart_6977761 baseEnd_6977761 := by
    simpa [prefixWord, tailWord_6977761, baseEnd_6977761] using wordTrace_append hprefix tailTrace_6977761
  have hstable : (prefixWord ++ tailWord_6977761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6977761).length < 2 ^ (prefixWord ++ tailWord_6977761).sum := by decide
  have hdescent : baseEnd_6977761 < baseStart_6977761 := by decide
  rcases family_descends (prefixWord ++ tailWord_6977761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6977785 : List Nat := [1, 2, 1, 3, 1, 1, 2, 5, 3, 2, 2]
def baseStart_6977785 : Nat := 118140960795 + 6977785 * 2 ^ 59
def prefixEnd_6977785 : Nat := 4983230072969 + 3 ^ 40 * 6977785 * 2
def baseEnd_6977785 : Nat := 3582957608733087117797257

theorem tailTrace_6977785 : CollatzResearch.WordTrace tailWord_6977785 prefixEnd_6977785 3582957608733087117797257 := by
  unfold tailWord_6977785
  simp only [CollatzResearch.WordTrace]
  refine ⟨254500727025684130646166809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169667151350456087097444539 254500727025684130646166809)
  ·
    refine ⟨190875545269263097984625107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254500727025684130646166809 190875545269263097984625107)
    ·
      refine ⟨286313317903894646976937661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190875545269263097984625107 286313317903894646976937661)
      ·
        refine ⟨107367494213960492616351623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 286313317903894646976937661 107367494213960492616351623)
        ·
          refine ⟨161051241320940738924527435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107367494213960492616351623 161051241320940738924527435)
          ·
            refine ⟨241576861981411108386791153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161051241320940738924527435 241576861981411108386791153)
            ·
              refine ⟨181182646486058331290093365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 241576861981411108386791153 181182646486058331290093365)
              ·
                refine ⟨16985873108067968558446253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 181182646486058331290093365 16985873108067968558446253)
                ·
                  refine ⟨6369702415525488209417345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16985873108067968558446253 6369702415525488209417345)
                  ·
                    refine ⟨4777276811644116157063009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6369702415525488209417345 4777276811644116157063009)
                    ·
                      refine ⟨3582957608733087117797257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4777276811644116157063009 3582957608733087117797257)
                      ·
                        rfl

theorem cell23_6977785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 5, 3, 2, 2].length) (baseStart_6977785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6977785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6977785 prefixEnd_6977785 := by exact prefixLift 6977785
  have htrace : WordTrace (prefixWord ++ tailWord_6977785) baseStart_6977785 baseEnd_6977785 := by
    simpa [prefixWord, tailWord_6977785, baseEnd_6977785] using wordTrace_append hprefix tailTrace_6977785
  have hstable : (prefixWord ++ tailWord_6977785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6977785).length < 2 ^ (prefixWord ++ tailWord_6977785).sum := by decide
  have hdescent : baseEnd_6977785 < baseStart_6977785 := by decide
  rcases family_descends (prefixWord ++ tailWord_6977785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6977788 : List Nat := [2, 2, 2, 1, 4, 1, 2, 2, 1, 1, 5]
def baseStart_6977788 : Nat := 118140960795 + 6977788 * 2 ^ 59
def prefixEnd_6977788 : Nat := 4983230072969 + 3 ^ 40 * 6977788 * 2
def baseEnd_6977788 : Nat := 3582959149175050606059743

theorem tailTrace_6977788 : CollatzResearch.WordTrace tailWord_6977788 prefixEnd_6977788 3582959149175050606059743 := by
  unfold tailWord_6977788
  simp only [CollatzResearch.WordTrace]
  refine ⟨127250418222336631079263009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169667224296448841439017345 127250418222336631079263009)
  ·
    refine ⟨95437813666752473309447257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127250418222336631079263009 95437813666752473309447257)
    ·
      refine ⟨71578360250064354982085443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95437813666752473309447257 71578360250064354982085443)
      ·
        refine ⟨107367540375096532473128165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71578360250064354982085443 107367540375096532473128165)
        ·
          refine ⟨20131413820330599838711531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 107367540375096532473128165 20131413820330599838711531)
          ·
            refine ⟨30197120730495899758067297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20131413820330599838711531 30197120730495899758067297)
            ·
              refine ⟨22647840547871924818550473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30197120730495899758067297 22647840547871924818550473)
              ·
                refine ⟨16985880410903943613912855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22647840547871924818550473 16985880410903943613912855)
                ·
                  refine ⟨25478820616355915420869283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16985880410903943613912855 25478820616355915420869283)
                  ·
                    refine ⟨38218230924533873131303925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25478820616355915420869283 38218230924533873131303925)
                    ·
                      refine ⟨3582959149175050606059743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38218230924533873131303925 3582959149175050606059743)
                      ·
                        rfl

theorem cell23_6977788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 2, 1, 1, 5].length) (baseStart_6977788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6977788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6977788 prefixEnd_6977788 := by exact prefixLift 6977788
  have htrace : WordTrace (prefixWord ++ tailWord_6977788) baseStart_6977788 baseEnd_6977788 := by
    simpa [prefixWord, tailWord_6977788, baseEnd_6977788] using wordTrace_append hprefix tailTrace_6977788
  have hstable : (prefixWord ++ tailWord_6977788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6977788).length < 2 ^ (prefixWord ++ tailWord_6977788).sum := by decide
  have hdescent : baseEnd_6977788 < baseStart_6977788 := by decide
  rcases family_descends (prefixWord ++ tailWord_6977788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6977791 : List Nat := [1, 1, 2, 2, 1, 4, 4, 8]
def baseStart_6977791 : Nat := 118140960795 + 6977791 * 2 ^ 59
def prefixEnd_6977791 : Nat := 4983230072969 + 3 ^ 40 * 6977791 * 2
def baseEnd_6977791 : Nat := 132702247763593114604527

theorem tailTrace_6977791 : CollatzResearch.WordTrace tailWord_6977791 prefixEnd_6977791 132702247763593114604527 := by
  unfold tailWord_6977791
  simp only [CollatzResearch.WordTrace]
  refine ⟨254500945863662393670885227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169667297242441595780590151 254500945863662393670885227)
  ·
    refine ⟨381751418795493590506327841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254500945863662393670885227 381751418795493590506327841)
    ·
      refine ⟨286313564096620192879745881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 381751418795493590506327841 286313564096620192879745881)
      ·
        refine ⟨214735173072465144659809411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 286313564096620192879745881 214735173072465144659809411)
        ·
          refine ⟨322102759608697716989714117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214735173072465144659809411 322102759608697716989714117)
          ·
            refine ⟨60394267426630821935571397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 322102759608697716989714117 60394267426630821935571397)
            ·
              refine ⟨11323925142493279112919637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60394267426630821935571397 11323925142493279112919637)
              ·
                refine ⟨132702247763593114604527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11323925142493279112919637 132702247763593114604527)
                ·
                  rfl

theorem cell23_6977791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 4, 8].length) (baseStart_6977791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6977791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6977791 prefixEnd_6977791 := by exact prefixLift 6977791
  have htrace : WordTrace (prefixWord ++ tailWord_6977791) baseStart_6977791 baseEnd_6977791 := by
    simpa [prefixWord, tailWord_6977791, baseEnd_6977791] using wordTrace_append hprefix tailTrace_6977791
  have hstable : (prefixWord ++ tailWord_6977791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6977791).length < 2 ^ (prefixWord ++ tailWord_6977791).sum := by decide
  have hdescent : baseEnd_6977791 < baseStart_6977791 := by decide
  rcases family_descends (prefixWord ++ tailWord_6977791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6977799 : List Nat := [1, 1, 4, 5, 2, 1, 1, 2, 1, 5]
def baseStart_6977799 : Nat := 118140960795 + 6977799 * 2 ^ 59
def prefixEnd_6977799 : Nat := 4983230072969 + 3 ^ 40 * 6977799 * 2
def baseEnd_6977799 : Nat := 1194321599154083354340731

theorem tailTrace_6977799 : CollatzResearch.WordTrace tailWord_6977799 prefixEnd_6977799 1194321599154083354340731 := by
  unfold tailWord_6977799
  simp only [CollatzResearch.WordTrace]
  refine ⟨254501237647633411037176451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169667491765088940691450967 254501237647633411037176451)
  ·
    refine ⟨381751856471450116555764677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254501237647633411037176451 381751856471450116555764677)
    ·
      refine ⟨71578473088396896854205877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 381751856471450116555764677 71578473088396896854205877)
      ·
        refine ⟨6710481852037209080081801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 71578473088396896854205877 6710481852037209080081801)
        ·
          refine ⟨5032861389027906810061351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6710481852037209080081801 5032861389027906810061351)
          ·
            refine ⟨7549292083541860215092027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5032861389027906810061351 7549292083541860215092027)
            ·
              refine ⟨11323938125312790322638041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7549292083541860215092027 11323938125312790322638041)
              ·
                refine ⟨8492953593984592741978531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11323938125312790322638041 8492953593984592741978531)
                ·
                  refine ⟨12739430390976889112967797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8492953593984592741978531 12739430390976889112967797)
                  ·
                    refine ⟨1194321599154083354340731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12739430390976889112967797 1194321599154083354340731)
                    ·
                      rfl

theorem cell23_6977799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 1, 2, 1, 5].length) (baseStart_6977799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6977799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6977799 prefixEnd_6977799 := by exact prefixLift 6977799
  have htrace : WordTrace (prefixWord ++ tailWord_6977799) baseStart_6977799 baseEnd_6977799 := by
    simpa [prefixWord, tailWord_6977799, baseEnd_6977799] using wordTrace_append hprefix tailTrace_6977799
  have hstable : (prefixWord ++ tailWord_6977799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6977799).length < 2 ^ (prefixWord ++ tailWord_6977799).sum := by decide
  have hdescent : baseEnd_6977799 < baseStart_6977799 := by decide
  rcases family_descends (prefixWord ++ tailWord_6977799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6977822 : List Nat := [4, 3, 2, 1, 1, 1, 3, 1, 1, 1, 5]
def baseStart_6977822 : Nat := 118140960795 + 6977822 * 2 ^ 59
def prefixEnd_6977822 : Nat := 4983230072969 + 3 ^ 40 * 6977822 * 2
def baseEnd_6977822 : Nat := 3582976607517303473034587

theorem tailTrace_6977822 : CollatzResearch.WordTrace tailWord_6977822 prefixEnd_6977822 3582976607517303473034587 := by
  unfold tailWord_6977822
  simp only [CollatzResearch.WordTrace]
  refine ⟨31812759565818760745657965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 169668051017700057310175813 31812759565818760745657965)
  ·
    refine ⟨11929784837182035279621737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31812759565818760745657965 11929784837182035279621737)
    ·
      refine ⟨8947338627886526459716303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11929784837182035279621737 8947338627886526459716303)
      ·
        refine ⟨13421007941829789689574455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8947338627886526459716303 13421007941829789689574455)
        ·
          refine ⟨20131511912744684534361683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13421007941829789689574455 20131511912744684534361683)
          ·
            refine ⟨30197267869117026801542525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20131511912744684534361683 30197267869117026801542525)
            ·
              refine ⟨11323975450918885050578447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30197267869117026801542525 11323975450918885050578447)
              ·
                refine ⟨16985963176378327575867671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11323975450918885050578447 16985963176378327575867671)
                ·
                  refine ⟨25478944764567491363801507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16985963176378327575867671 25478944764567491363801507)
                  ·
                    refine ⟨38218417146851237045702261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25478944764567491363801507 38218417146851237045702261)
                    ·
                      refine ⟨3582976607517303473034587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38218417146851237045702261 3582976607517303473034587)
                      ·
                        rfl

theorem cell23_6977822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_6977822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6977822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6977822 prefixEnd_6977822 := by exact prefixLift 6977822
  have htrace : WordTrace (prefixWord ++ tailWord_6977822) baseStart_6977822 baseEnd_6977822 := by
    simpa [prefixWord, tailWord_6977822, baseEnd_6977822] using wordTrace_append hprefix tailTrace_6977822
  have hstable : (prefixWord ++ tailWord_6977822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6977822).length < 2 ^ (prefixWord ++ tailWord_6977822).sum := by decide
  have hdescent : baseEnd_6977822 < baseStart_6977822 := by decide
  rcases family_descends (prefixWord ++ tailWord_6977822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6977845 : List Nat := [1, 3, 3, 1, 2, 1, 1, 1, 5, 3, 2]
def baseStart_6977845 : Nat := 118140960795 + 6977845 * 2 ^ 59
def prefixEnd_6977845 : Nat := 4983230072969 + 3 ^ 40 * 6977845 * 2
def baseEnd_6977845 : Nat := 3582988417572356883046981

theorem tailTrace_6977845 : CollatzResearch.WordTrace tailWord_6977845 prefixEnd_6977845 3582988417572356883046981 := by
  unfold tailWord_6977845
  simp only [CollatzResearch.WordTrace]
  refine ⟨254502915405466760893350989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169668610270311173928900659 254502915405466760893350989)
  ·
    refine ⟨95438593277050035335006621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 254502915405466760893350989 95438593277050035335006621)
    ·
      refine ⟨35789472478893763250627483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95438593277050035335006621 35789472478893763250627483)
      ·
        refine ⟨53684208718340644875941225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35789472478893763250627483 53684208718340644875941225)
        ·
          refine ⟨40263156538755483656955919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53684208718340644875941225 40263156538755483656955919)
          ·
            refine ⟨60394734808133225485433879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40263156538755483656955919 60394734808133225485433879)
            ·
              refine ⟨90592102212199838228150819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60394734808133225485433879 90592102212199838228150819)
              ·
                refine ⟨135888153318299757342226229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90592102212199838228150819 135888153318299757342226229)
                ·
                  refine ⟨12739514373590602250833709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 135888153318299757342226229 12739514373590602250833709)
                  ·
                    refine ⟨4777317890096475844062641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12739514373590602250833709 4777317890096475844062641)
                    ·
                      refine ⟨3582988417572356883046981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4777317890096475844062641 3582988417572356883046981)
                      ·
                        rfl

theorem cell23_6977845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 1, 5, 3, 2].length) (baseStart_6977845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6977845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6977845 prefixEnd_6977845 := by exact prefixLift 6977845
  have htrace : WordTrace (prefixWord ++ tailWord_6977845) baseStart_6977845 baseEnd_6977845 := by
    simpa [prefixWord, tailWord_6977845, baseEnd_6977845] using wordTrace_append hprefix tailTrace_6977845
  have hstable : (prefixWord ++ tailWord_6977845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6977845).length < 2 ^ (prefixWord ++ tailWord_6977845).sum := by decide
  have hdescent : baseEnd_6977845 < baseStart_6977845 := by decide
  rcases family_descends (prefixWord ++ tailWord_6977845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6977881 : List Nat := [1, 2, 1, 2, 2, 2, 1, 1, 11]
def baseStart_6977881 : Nat := 118140960795 + 6977881 * 2 ^ 59
def prefixEnd_6977881 : Nat := 4983230072969 + 3 ^ 40 * 6977881 * 2
def baseEnd_6977881 : Nat := 398111878097324304688535

theorem tailTrace_6977881 : CollatzResearch.WordTrace tailWord_6977881 prefixEnd_6977881 398111878097324304688535 := by
  unfold tailWord_6977881
  simp only [CollatzResearch.WordTrace]
  refine ⟨254504228433336339041661497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169669485622224226027774331 254504228433336339041661497)
  ·
    refine ⟨190878171325002254281246123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254504228433336339041661497 190878171325002254281246123)
    ·
      refine ⟨286317256987503381421869185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190878171325002254281246123 286317256987503381421869185)
      ·
        refine ⟨214737942740627536066401889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 286317256987503381421869185 214737942740627536066401889)
        ·
          refine ⟨161053457055470652049801417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 214737942740627536066401889 161053457055470652049801417)
          ·
            refine ⟨120790092791602989037351063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161053457055470652049801417 120790092791602989037351063)
            ·
              refine ⟨181185139187404483556026595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120790092791602989037351063 181185139187404483556026595)
              ·
                refine ⟨271777708781106725334039893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 181185139187404483556026595 271777708781106725334039893)
                ·
                  refine ⟨398111878097324304688535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 271777708781106725334039893 398111878097324304688535)
                  ·
                    rfl

theorem cell23_6977881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 11].length) (baseStart_6977881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6977881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6977881 prefixEnd_6977881 := by exact prefixLift 6977881
  have htrace : WordTrace (prefixWord ++ tailWord_6977881) baseStart_6977881 baseEnd_6977881 := by
    simpa [prefixWord, tailWord_6977881, baseEnd_6977881] using wordTrace_append hprefix tailTrace_6977881
  have hstable : (prefixWord ++ tailWord_6977881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6977881).length < 2 ^ (prefixWord ++ tailWord_6977881).sum := by decide
  have hdescent : baseEnd_6977881 < baseStart_6977881 := by decide
  rcases family_descends (prefixWord ++ tailWord_6977881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6977892 : List Nat := [2, 3, 1, 1, 3, 1, 3, 1, 4, 2, 2]
def baseStart_6977892 : Nat := 118140960795 + 6977892 * 2 ^ 59
def prefixEnd_6977892 : Nat := 4983230072969 + 3 ^ 40 * 6977892 * 2
def baseEnd_6977892 : Nat := 3583012551163118199159265

theorem tailTrace_6977892 : CollatzResearch.WordTrace tailWord_6977892 prefixEnd_6977892 3583012551163118199159265 := by
  unfold tailWord_6977892
  simp only [CollatzResearch.WordTrace]
  refine ⟨127252314818148243960155965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169669753090864325280207953 127252314818148243960155965)
  ·
    refine ⟨47719618056805591485058487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127252314818148243960155965 47719618056805591485058487)
    ·
      refine ⟨71579427085208387227587731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47719618056805591485058487 71579427085208387227587731)
      ·
        refine ⟨107369140627812580841381597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71579427085208387227587731 107369140627812580841381597)
        ·
          refine ⟨40263427735429717815518099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107369140627812580841381597 40263427735429717815518099)
          ·
            refine ⟨60395141603144576723277149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40263427735429717815518099 60395141603144576723277149)
            ·
              refine ⟨22648178101179216271228931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60395141603144576723277149 22648178101179216271228931)
              ·
                refine ⟨33972267151768824406843397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22648178101179216271228931 33972267151768824406843397)
                ·
                  refine ⟨6369800090956654576283137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33972267151768824406843397 6369800090956654576283137)
                  ·
                    refine ⟨4777350068217490932212353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6369800090956654576283137 4777350068217490932212353)
                    ·
                      refine ⟨3583012551163118199159265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4777350068217490932212353 3583012551163118199159265)
                      ·
                        rfl

theorem cell23_6977892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 1, 4, 2, 2].length) (baseStart_6977892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6977892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6977892 prefixEnd_6977892 := by exact prefixLift 6977892
  have htrace : WordTrace (prefixWord ++ tailWord_6977892) baseStart_6977892 baseEnd_6977892 := by
    simpa [prefixWord, tailWord_6977892, baseEnd_6977892] using wordTrace_append hprefix tailTrace_6977892
  have hstable : (prefixWord ++ tailWord_6977892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6977892).length < 2 ^ (prefixWord ++ tailWord_6977892).sum := by decide
  have hdescent : baseEnd_6977892 < baseStart_6977892 := by decide
  rcases family_descends (prefixWord ++ tailWord_6977892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6977909 : List Nat := [1, 3, 4, 1, 2, 3, 1, 1, 1, 4, 2]
def baseStart_6977909 : Nat := 118140960795 + 6977909 * 2 ^ 59
def prefixEnd_6977909 : Nat := 4983230072969 + 3 ^ 40 * 6977909 * 2
def baseEnd_6977909 : Nat := 3583021280334244632646687

theorem tailTrace_6977909 : CollatzResearch.WordTrace tailWord_6977909 prefixEnd_6977909 3583021280334244632646687 := by
  unfold tailWord_6977909
  simp only [CollatzResearch.WordTrace]
  refine ⟨254505249677234899823680781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169670166451489933215787187 254505249677234899823680781)
  ·
    refine ⟨95439468628963087433880293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 254505249677234899823680781 95439468628963087433880293)
    ·
      refine ⟨17894900367930578893852555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95439468628963087433880293 17894900367930578893852555)
      ·
        refine ⟨26842350551895868340778833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17894900367930578893852555 26842350551895868340778833)
        ·
          refine ⟨20131762913921901255584125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26842350551895868340778833 20131762913921901255584125)
          ·
            refine ⟨7549411092720712970844047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20131762913921901255584125 7549411092720712970844047)
            ·
              refine ⟨11324116639081069456266071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7549411092720712970844047 11324116639081069456266071)
              ·
                refine ⟨16986174958621604184399107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11324116639081069456266071 16986174958621604184399107)
                ·
                  refine ⟨25479262437932406276598661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16986174958621604184399107 25479262437932406276598661)
                  ·
                    refine ⟨4777361707112326176862249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25479262437932406276598661 4777361707112326176862249)
                    ·
                      refine ⟨3583021280334244632646687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4777361707112326176862249 3583021280334244632646687)
                      ·
                        rfl

theorem cell23_6977909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 1, 1, 1, 4, 2].length) (baseStart_6977909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6977909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6977909 prefixEnd_6977909 := by exact prefixLift 6977909
  have htrace : WordTrace (prefixWord ++ tailWord_6977909) baseStart_6977909 baseEnd_6977909 := by
    simpa [prefixWord, tailWord_6977909, baseEnd_6977909] using wordTrace_append hprefix tailTrace_6977909
  have hstable : (prefixWord ++ tailWord_6977909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6977909).length < 2 ^ (prefixWord ++ tailWord_6977909).sum := by decide
  have hdescent : baseEnd_6977909 < baseStart_6977909 := by decide
  rcases family_descends (prefixWord ++ tailWord_6977909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6977928 : List Nat := [2, 1, 3, 3, 1, 1, 1, 3, 1, 7]
def baseStart_6977928 : Nat := 118140960795 + 6977928 * 2 ^ 59
def prefixEnd_6977928 : Nat := 4983230072969 + 3 ^ 40 * 6977928 * 2
def baseEnd_6977928 : Nat := 1194343678822226686103033

theorem tailTrace_6977928 : CollatzResearch.WordTrace tailWord_6977928 prefixEnd_6977928 1194343678822226686103033 := by
  unfold tailWord_6977928
  simp only [CollatzResearch.WordTrace]
  refine ⟨127252971332083033034311219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169670628442777377379081625 127252971332083033034311219)
  ·
    refine ⟨190879456998124549551466829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127252971332083033034311219 190879456998124549551466829)
    ·
      refine ⟨71579796374296706081800061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 190879456998124549551466829 71579796374296706081800061)
      ·
        refine ⟨26842423640361264780675023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71579796374296706081800061 26842423640361264780675023)
        ·
          refine ⟨40263635460541897171012535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26842423640361264780675023 40263635460541897171012535)
          ·
            refine ⟨60395453190812845756518803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40263635460541897171012535 60395453190812845756518803)
            ·
              refine ⟨90593179786219268634778205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60395453190812845756518803 90593179786219268634778205)
              ·
                refine ⟨33972442419832225738041827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90593179786219268634778205 33972442419832225738041827)
                ·
                  refine ⟨50958663629748338607062741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33972442419832225738041827 50958663629748338607062741)
                  ·
                    refine ⟨1194343678822226686103033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50958663629748338607062741 1194343678822226686103033)
                    ·
                      rfl

theorem cell23_6977928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 3, 1, 7].length) (baseStart_6977928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6977928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6977928 prefixEnd_6977928 := by exact prefixLift 6977928
  have htrace : WordTrace (prefixWord ++ tailWord_6977928) baseStart_6977928 baseEnd_6977928 := by
    simpa [prefixWord, tailWord_6977928, baseEnd_6977928] using wordTrace_append hprefix tailTrace_6977928
  have hstable : (prefixWord ++ tailWord_6977928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6977928).length < 2 ^ (prefixWord ++ tailWord_6977928).sum := by decide
  have hdescent : baseEnd_6977928 < baseStart_6977928 := by decide
  rcases family_descends (prefixWord ++ tailWord_6977928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6977932 : List Nat := [2, 2, 1, 2, 1, 6, 1, 3, 5]
def baseStart_6977932 : Nat := 118140960795 + 6977932 * 2 ^ 59
def prefixEnd_6977932 : Nat := 4983230072969 + 3 ^ 40 * 6977932 * 2
def baseEnd_6977932 : Nat := 398114787821033115851009

theorem tailTrace_6977932 : CollatzResearch.WordTrace tailWord_6977932 prefixEnd_6977932 398114787821033115851009 := by
  unfold tailWord_6977932
  simp only [CollatzResearch.WordTrace]
  refine ⟨127253044278075787375884025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169670725704101049834512033 127253044278075787375884025)
  ·
    refine ⟨95439783208556840531913019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127253044278075787375884025 95439783208556840531913019)
    ·
      refine ⟨143159674812835260797869529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95439783208556840531913019 143159674812835260797869529)
      ·
        refine ⟨107369756109626445598402147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143159674812835260797869529 107369756109626445598402147)
        ·
          refine ⟨161054634164439668397603221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107369756109626445598402147 161054634164439668397603221)
          ·
            refine ⟨7549435976458109456137651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 161054634164439668397603221 7549435976458109456137651)
            ·
              refine ⟨11324153964687164184206477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7549435976458109456137651 11324153964687164184206477)
              ·
                refine ⟨4246557736757686569077429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11324153964687164184206477 4246557736757686569077429)
                ·
                  refine ⟨398114787821033115851009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4246557736757686569077429 398114787821033115851009)
                  ·
                    rfl

theorem cell23_6977932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 1, 3, 5].length) (baseStart_6977932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6977932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6977932 prefixEnd_6977932 := by exact prefixLift 6977932
  have htrace : WordTrace (prefixWord ++ tailWord_6977932) baseStart_6977932 baseEnd_6977932 := by
    simpa [prefixWord, tailWord_6977932, baseEnd_6977932] using wordTrace_append hprefix tailTrace_6977932
  have hstable : (prefixWord ++ tailWord_6977932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6977932).length < 2 ^ (prefixWord ++ tailWord_6977932).sum := by decide
  have hdescent : baseEnd_6977932 < baseStart_6977932 := by decide
  rcases family_descends (prefixWord ++ tailWord_6977932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6977949 : List Nat := [1, 4, 2, 1, 4, 1, 3, 2, 5]
def baseStart_6977949 : Nat := 118140960795 + 6977949 * 2 ^ 59
def prefixEnd_6977949 : Nat := 4983230072969 + 3 ^ 40 * 6977949 * 2
def baseEnd_6977949 : Nat := 398115757728936052905167

theorem tailTrace_6977949 : CollatzResearch.WordTrace tailWord_6977949 prefixEnd_6977949 398115757728936052905167 := by
  unfold tailWord_6977949
  simp only [CollatzResearch.WordTrace]
  refine ⟨254506708597089986655136901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169671139064726657770091267 254506708597089986655136901)
  ·
    refine ⟨47720007861954372497838169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 254506708597089986655136901 47720007861954372497838169)
    ·
      refine ⟨35790005896465779373378627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47720007861954372497838169 35790005896465779373378627)
      ·
        refine ⟨53685008844698669060067941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35790005896465779373378627 53685008844698669060067941)
        ·
          refine ⟨10065939158381000448762739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53685008844698669060067941 10065939158381000448762739)
          ·
            refine ⟨15098908737571500673144109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10065939158381000448762739 15098908737571500673144109)
            ·
              refine ⟨5662090776589312752429041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15098908737571500673144109 5662090776589312752429041)
              ·
                refine ⟨4246568082441984564321781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5662090776589312752429041 4246568082441984564321781)
                ·
                  refine ⟨398115757728936052905167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4246568082441984564321781 398115757728936052905167)
                  ·
                    rfl

theorem cell23_6977949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 3, 2, 5].length) (baseStart_6977949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6977949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6977949 prefixEnd_6977949 := by exact prefixLift 6977949
  have htrace : WordTrace (prefixWord ++ tailWord_6977949) baseStart_6977949 baseEnd_6977949 := by
    simpa [prefixWord, tailWord_6977949, baseEnd_6977949] using wordTrace_append hprefix tailTrace_6977949
  have hstable : (prefixWord ++ tailWord_6977949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6977949).length < 2 ^ (prefixWord ++ tailWord_6977949).sum := by decide
  have hdescent : baseEnd_6977949 < baseStart_6977949 := by decide
  rcases family_descends (prefixWord ++ tailWord_6977949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6977978 : List Nat := [3, 1, 1, 1, 2, 1, 1, 3, 2, 4, 4]
def baseStart_6977978 : Nat := 118140960795 + 6977978 * 2 ^ 59
def prefixEnd_6977978 : Nat := 4983230072969 + 3 ^ 40 * 6977978 * 2
def baseEnd_6977978 : Nat := 3583056710499404862683869

theorem tailTrace_6977978 : CollatzResearch.WordTrace tailWord_6977978 prefixEnd_6977978 3583056710499404862683869 := by
  unfold tailWord_6977978
  simp only [CollatzResearch.WordTrace]
  refine ⟨63626941578496231151985647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169671844209323283071961725 63626941578496231151985647)
  ·
    refine ⟨95440412367744346727978471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63626941578496231151985647 95440412367744346727978471)
    ·
      refine ⟨143160618551616520091967707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95440412367744346727978471 143160618551616520091967707)
      ·
        refine ⟨214740927827424780137951561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143160618551616520091967707 214740927827424780137951561)
        ·
          refine ⟨161055695870568585103463671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 214740927827424780137951561 161055695870568585103463671)
          ·
            refine ⟨241583543805852877655195507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161055695870568585103463671 241583543805852877655195507)
            ·
              refine ⟨362375315708779316482793261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 241583543805852877655195507 362375315708779316482793261)
              ·
                refine ⟨135890743390792243681047473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 362375315708779316482793261 135890743390792243681047473)
                ·
                  refine ⟨101918057543094182760785605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 135890743390792243681047473 101918057543094182760785605)
                  ·
                    refine ⟨19109635789330159267647301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 101918057543094182760785605 19109635789330159267647301)
                    ·
                      refine ⟨3583056710499404862683869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19109635789330159267647301 3583056710499404862683869)
                      ·
                        rfl

theorem cell23_6977978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 3, 2, 4, 4].length) (baseStart_6977978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6977978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6977978 prefixEnd_6977978 := by exact prefixLift 6977978
  have htrace : WordTrace (prefixWord ++ tailWord_6977978) baseStart_6977978 baseEnd_6977978 := by
    simpa [prefixWord, tailWord_6977978, baseEnd_6977978] using wordTrace_append hprefix tailTrace_6977978
  have hstable : (prefixWord ++ tailWord_6977978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6977978).length < 2 ^ (prefixWord ++ tailWord_6977978).sum := by decide
  have hdescent : baseEnd_6977978 < baseStart_6977978 := by decide
  rcases family_descends (prefixWord ++ tailWord_6977978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6978005 : List Nat := [1, 3, 2, 3, 1, 2, 1, 4, 6]
def baseStart_6978005 : Nat := 118140960795 + 6978005 * 2 ^ 59
def prefixEnd_6978005 : Nat := 4983230072969 + 3 ^ 40 * 6978005 * 2
def baseEnd_6978005 : Nat := 398118952719675139671805

theorem tailTrace_6978005 : CollatzResearch.WordTrace tailWord_6978005 prefixEnd_6978005 398118952719675139671805 := by
  unfold tailWord_6978005
  simp only [CollatzResearch.WordTrace]
  refine ⟨254508751084887108219175469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169672500723258072146116979 254508751084887108219175469)
  ·
    refine ⟨95440781656832665582190801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 254508751084887108219175469 95440781656832665582190801)
    ·
      refine ⟨71580586242624499186643101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95440781656832665582190801 71580586242624499186643101)
      ·
        refine ⟨26842719840984187194991163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71580586242624499186643101 26842719840984187194991163)
        ·
          refine ⟨40264079761476280792486745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26842719840984187194991163 40264079761476280792486745)
          ·
            refine ⟨30198059821107210594365059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40264079761476280792486745 30198059821107210594365059)
            ·
              refine ⟨45297089731660815891547589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30198059821107210594365059 45297089731660815891547589)
              ·
                refine ⟨8493204324686402979665173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45297089731660815891547589 8493204324686402979665173)
                ·
                  refine ⟨398118952719675139671805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8493204324686402979665173 398118952719675139671805)
                  ·
                    rfl

theorem cell23_6978005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 4, 6].length) (baseStart_6978005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6978005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6978005 prefixEnd_6978005 := by exact prefixLift 6978005
  have htrace : WordTrace (prefixWord ++ tailWord_6978005) baseStart_6978005 baseEnd_6978005 := by
    simpa [prefixWord, tailWord_6978005, baseEnd_6978005] using wordTrace_append hprefix tailTrace_6978005
  have hstable : (prefixWord ++ tailWord_6978005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6978005).length < 2 ^ (prefixWord ++ tailWord_6978005).sum := by decide
  have hdescent : baseEnd_6978005 < baseStart_6978005 := by decide
  rcases family_descends (prefixWord ++ tailWord_6978005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6978008 : List Nat := [2, 1, 2, 2, 2, 1, 1, 3, 1, 2, 6]
def baseStart_6978008 : Nat := 118140960795 + 6978008 * 2 ^ 59
def prefixEnd_6978008 : Nat := 4983230072969 + 3 ^ 40 * 6978008 * 2
def baseEnd_6978008 : Nat := 3583072114919039745308731

theorem tailTrace_6978008 : CollatzResearch.WordTrace tailWord_6978008 prefixEnd_6978008 3583072114919039745308731 := by
  unfold tailWord_6978008
  simp only [CollatzResearch.WordTrace]
  refine ⟨127254430251938119865767339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169672573669250826487689785 127254430251938119865767339)
  ·
    refine ⟨190881645377907179798651009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127254430251938119865767339 190881645377907179798651009)
    ·
      refine ⟨143161234033430384848988257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190881645377907179798651009 143161234033430384848988257)
      ·
        refine ⟨107370925525072788636741193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143161234033430384848988257 107370925525072788636741193)
        ·
          refine ⟨80528194143804591477555895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107370925525072788636741193 80528194143804591477555895)
          ·
            refine ⟨120792291215706887216333843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80528194143804591477555895 120792291215706887216333843)
            ·
              refine ⟨181188436823560330824500765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120792291215706887216333843 181188436823560330824500765)
              ·
                refine ⟨67945663808835124059187787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 181188436823560330824500765 67945663808835124059187787)
                ·
                  refine ⟨101918495713252686088781681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67945663808835124059187787 101918495713252686088781681)
                  ·
                    refine ⟨76438871784939514566586261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 101918495713252686088781681 76438871784939514566586261)
                    ·
                      refine ⟨3583072114919039745308731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76438871784939514566586261 3583072114919039745308731)
                      ·
                        rfl

theorem cell23_6978008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 3, 1, 2, 6].length) (baseStart_6978008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6978008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6978008 prefixEnd_6978008 := by exact prefixLift 6978008
  have htrace : WordTrace (prefixWord ++ tailWord_6978008) baseStart_6978008 baseEnd_6978008 := by
    simpa [prefixWord, tailWord_6978008, baseEnd_6978008] using wordTrace_append hprefix tailTrace_6978008
  have hstable : (prefixWord ++ tailWord_6978008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6978008).length < 2 ^ (prefixWord ++ tailWord_6978008).sum := by decide
  have hdescent : baseEnd_6978008 < baseStart_6978008 := by decide
  rcases family_descends (prefixWord ++ tailWord_6978008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6978028 : List Nat := [2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 7]
def baseStart_6978028 : Nat := 118140960795 + 6978028 * 2 ^ 59
def prefixEnd_6978028 : Nat := 4983230072969 + 3 ^ 40 * 6978028 * 2
def baseEnd_6978028 : Nat := 3583082384532129667058639

theorem tailTrace_6978028 : CollatzResearch.WordTrace tailWord_6978028 prefixEnd_6978028 3583082384532129667058639 := by
  unfold tailWord_6978028
  simp only [CollatzResearch.WordTrace]
  refine ⟨127254794981901891573631369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169673059975869188764841825 127254794981901891573631369)
  ·
    refine ⟨95441096236426418680223527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127254794981901891573631369 95441096236426418680223527)
    ·
      refine ⟨143161644354639628020335291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95441096236426418680223527 143161644354639628020335291)
      ·
        refine ⟨214742466531959442030502937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143161644354639628020335291 214742466531959442030502937)
        ·
          refine ⟨161056849898969581522877203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 214742466531959442030502937 161056849898969581522877203)
          ·
            refine ⟨241585274848454372284315805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161056849898969581522877203 241585274848454372284315805)
            ·
              refine ⟨90594478068170389606618427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 241585274848454372284315805 90594478068170389606618427)
              ·
                refine ⟨135891717102255584409927641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90594478068170389606618427 135891717102255584409927641)
                ·
                  refine ⟨101918787826691688307445731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 135891717102255584409927641 101918787826691688307445731)
                  ·
                    refine ⟨152878181740037532461168597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 101918787826691688307445731 152878181740037532461168597)
                    ·
                      refine ⟨3583082384532129667058639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 152878181740037532461168597 3583082384532129667058639)
                      ·
                        rfl

theorem cell23_6978028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 7].length) (baseStart_6978028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6978028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6978028 prefixEnd_6978028 := by exact prefixLift 6978028
  have htrace : WordTrace (prefixWord ++ tailWord_6978028) baseStart_6978028 baseEnd_6978028 := by
    simpa [prefixWord, tailWord_6978028, baseEnd_6978028] using wordTrace_append hprefix tailTrace_6978028
  have hstable : (prefixWord ++ tailWord_6978028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6978028).length < 2 ^ (prefixWord ++ tailWord_6978028).sum := by decide
  have hdescent : baseEnd_6978028 < baseStart_6978028 := by decide
  rcases family_descends (prefixWord ++ tailWord_6978028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6978032 : List Nat := [2, 1, 1, 1, 3, 3, 3, 2, 3, 1, 3]
def baseStart_6978032 : Nat := 118140960795 + 6978032 * 2 ^ 59
def prefixEnd_6978032 : Nat := 4983230072969 + 3 ^ 40 * 6978032 * 2
def baseEnd_6978032 : Nat := 3583084438454747651408621

theorem tailTrace_6978032 : CollatzResearch.WordTrace tailWord_6978032 prefixEnd_6978032 3583084438454747651408621 := by
  unfold tailWord_6978032
  simp only [CollatzResearch.WordTrace]
  refine ⟨127254867927894645915204175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169673157237192861220272233 127254867927894645915204175)
  ·
    refine ⟨190882301891841968872806263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127254867927894645915204175 190882301891841968872806263)
    ·
      refine ⟨286323452837762953309209395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190882301891841968872806263 286323452837762953309209395)
      ·
        refine ⟨429485179256644429963814093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286323452837762953309209395 429485179256644429963814093)
        ·
          refine ⟨161056942221241661236430285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 429485179256644429963814093 161056942221241661236430285)
          ·
            refine ⟨60396353332965622963661357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 161056942221241661236430285 60396353332965622963661357)
            ·
              refine ⟨22648632499862108611373009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60396353332965622963661357 22648632499862108611373009)
              ·
                refine ⟨16986474374896581458529757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22648632499862108611373009 16986474374896581458529757)
                ·
                  refine ⟨6369927890586218046948659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16986474374896581458529757 6369927890586218046948659)
                  ·
                    refine ⟨9554891835879327070422989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6369927890586218046948659 9554891835879327070422989)
                    ·
                      refine ⟨3583084438454747651408621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9554891835879327070422989 3583084438454747651408621)
                      ·
                        rfl

theorem cell23_6978032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 2, 3, 1, 3].length) (baseStart_6978032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6978032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6978032 prefixEnd_6978032 := by exact prefixLift 6978032
  have htrace : WordTrace (prefixWord ++ tailWord_6978032) baseStart_6978032 baseEnd_6978032 := by
    simpa [prefixWord, tailWord_6978032, baseEnd_6978032] using wordTrace_append hprefix tailTrace_6978032
  have hstable : (prefixWord ++ tailWord_6978032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6978032).length < 2 ^ (prefixWord ++ tailWord_6978032).sum := by decide
  have hdescent : baseEnd_6978032 < baseStart_6978032 := by decide
  rcases family_descends (prefixWord ++ tailWord_6978032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6978035 : List Nat := [1, 1, 1, 2, 2, 2, 4, 4, 1, 5]
def baseStart_6978035 : Nat := 118140960795 + 6978035 * 2 ^ 59
def prefixEnd_6978035 : Nat := 4983230072969 + 3 ^ 40 * 6978035 * 2
def baseEnd_6978035 : Nat := 1194361992965570379890369

theorem tailTrace_6978035 : CollatzResearch.WordTrace tailWord_6978035 prefixEnd_6978035 1194361992965570379890369 := by
  unfold tailWord_6978035
  simp only [CollatzResearch.WordTrace]
  refine ⟨254509845274778423342767559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169673230183185615561845039 254509845274778423342767559)
  ·
    refine ⟨381764767912167635014151339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254509845274778423342767559 381764767912167635014151339)
    ·
      refine ⟨572647151868251452521227009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 381764767912167635014151339 572647151868251452521227009)
      ·
        refine ⟨429485363901188589390920257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 572647151868251452521227009 429485363901188589390920257)
        ·
          refine ⟨322114022925891442043190193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 429485363901188589390920257 322114022925891442043190193)
          ·
            refine ⟨241585517194418581532392645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 322114022925891442043190193 241585517194418581532392645)
            ·
              refine ⟨45297284473953484037323621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 241585517194418581532392645 45297284473953484037323621)
              ·
                refine ⟨8493240838866278256998179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45297284473953484037323621 8493240838866278256998179)
                ·
                  refine ⟨12739861258299417385497269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8493240838866278256998179 12739861258299417385497269)
                  ·
                    refine ⟨1194361992965570379890369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12739861258299417385497269 1194361992965570379890369)
                    ·
                      rfl

theorem cell23_6978035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 4, 1, 5].length) (baseStart_6978035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6978035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6978035 prefixEnd_6978035 := by exact prefixLift 6978035
  have htrace : WordTrace (prefixWord ++ tailWord_6978035) baseStart_6978035 baseEnd_6978035 := by
    simpa [prefixWord, tailWord_6978035, baseEnd_6978035] using wordTrace_append hprefix tailTrace_6978035
  have hstable : (prefixWord ++ tailWord_6978035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6978035).length < 2 ^ (prefixWord ++ tailWord_6978035).sum := by decide
  have hdescent : baseEnd_6978035 < baseStart_6978035 := by decide
  rcases family_descends (prefixWord ++ tailWord_6978035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6978042 : List Nat := [3, 1, 1, 1, 1, 2, 2, 5, 2, 3, 2]
def baseStart_6978042 : Nat := 118140960795 + 6978042 * 2 ^ 59
def prefixEnd_6978042 : Nat := 4983230072969 + 3 ^ 40 * 6978042 * 2
def baseEnd_6978042 : Nat := 3583089573261292612283575

theorem tailTrace_6978042 : CollatzResearch.WordTrace tailWord_6978042 prefixEnd_6978042 3583089573261292612283575 := by
  unfold tailWord_6978042
  simp only [CollatzResearch.WordTrace]
  refine ⟨63627525146438265884568095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169673400390502042358848253 63627525146438265884568095)
  ·
    refine ⟨95441287719657398826852143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63627525146438265884568095 95441287719657398826852143)
    ·
      refine ⟨143161931579486098240278215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95441287719657398826852143 143161931579486098240278215)
      ·
        refine ⟨214742897369229147360417323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143161931579486098240278215 214742897369229147360417323)
        ·
          refine ⟨322114346053843721040625985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214742897369229147360417323 322114346053843721040625985)
          ·
            refine ⟨241585759540382790780469489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 322114346053843721040625985 241585759540382790780469489)
            ·
              refine ⟨181189319655287093085352117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 241585759540382790780469489 181189319655287093085352117)
              ·
                refine ⟨16986498717683164976751761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 181189319655287093085352117 16986498717683164976751761)
                ·
                  refine ⟨12739874038262373732563821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16986498717683164976751761 12739874038262373732563821)
                  ·
                    refine ⟨4777452764348390149711433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12739874038262373732563821 4777452764348390149711433)
                    ·
                      refine ⟨3583089573261292612283575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4777452764348390149711433 3583089573261292612283575)
                      ·
                        rfl

theorem cell23_6978042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 5, 2, 3, 2].length) (baseStart_6978042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6978042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6978042 prefixEnd_6978042 := by exact prefixLift 6978042
  have htrace : WordTrace (prefixWord ++ tailWord_6978042) baseStart_6978042 baseEnd_6978042 := by
    simpa [prefixWord, tailWord_6978042, baseEnd_6978042] using wordTrace_append hprefix tailTrace_6978042
  have hstable : (prefixWord ++ tailWord_6978042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6978042).length < 2 ^ (prefixWord ++ tailWord_6978042).sum := by decide
  have hdescent : baseEnd_6978042 < baseStart_6978042 := by decide
  rcases family_descends (prefixWord ++ tailWord_6978042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6978109 : List Nat := [1, 4, 1, 3, 2, 1, 2, 3, 1, 2, 3]
def baseStart_6978109 : Nat := 118140960795 + 6978109 * 2 ^ 59
def prefixEnd_6978109 : Nat := 4983230072969 + 3 ^ 40 * 6978109 * 2
def baseEnd_6978109 : Nat := 3583123976465143850145767

theorem tailTrace_6978109 : CollatzResearch.WordTrace tailWord_6978109 prefixEnd_6978109 3583123976465143850145767 := by
  unfold tailWord_6978109
  simp only [CollatzResearch.WordTrace]
  refine ⟨254512544276510333980961381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169675029517673555987307587 254512544276510333980961381)
  ·
    refine ⟨47721102051845687621430259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 254512544276510333980961381 47721102051845687621430259)
    ·
      refine ⟨71581653077768531432145389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47721102051845687621430259 71581653077768531432145389)
      ·
        refine ⟨26843119904163199287054521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71581653077768531432145389 26843119904163199287054521)
        ·
          refine ⟨20132339928122399465290891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26843119904163199287054521 20132339928122399465290891)
          ·
            refine ⟨30198509892183599197936337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20132339928122399465290891 30198509892183599197936337)
            ·
              refine ⟨22648882419137699398452253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30198509892183599197936337 22648882419137699398452253)
              ·
                refine ⟨8493330907176637274419595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22648882419137699398452253 8493330907176637274419595)
                ·
                  refine ⟨12739996360764955911629393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8493330907176637274419595 12739996360764955911629393)
                  ·
                    refine ⟨9554997270573716933722045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12739996360764955911629393 9554997270573716933722045)
                    ·
                      refine ⟨3583123976465143850145767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9554997270573716933722045 3583123976465143850145767)
                      ·
                        rfl

theorem cell23_6978109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 3, 1, 2, 3].length) (baseStart_6978109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6978109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6978109 prefixEnd_6978109 := by exact prefixLift 6978109
  have htrace : WordTrace (prefixWord ++ tailWord_6978109) baseStart_6978109 baseEnd_6978109 := by
    simpa [prefixWord, tailWord_6978109, baseEnd_6978109] using wordTrace_append hprefix tailTrace_6978109
  have hstable : (prefixWord ++ tailWord_6978109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6978109).length < 2 ^ (prefixWord ++ tailWord_6978109).sum := by decide
  have hdescent : baseEnd_6978109 < baseStart_6978109 := by decide
  rcases family_descends (prefixWord ++ tailWord_6978109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6978179 : List Nat := [1, 1, 1, 3, 3, 1, 2, 3, 4, 2, 2]
def baseStart_6978179 : Nat := 118140960795 + 6978179 * 2 ^ 59
def prefixEnd_6978179 : Nat := 4983230072969 + 3 ^ 40 * 6978179 * 2
def baseEnd_6978179 : Nat := 3583159920110958576270445

theorem tailTrace_6978179 : CollatzResearch.WordTrace tailWord_6978179 prefixEnd_6978179 3583159920110958576270445 := by
  unfold tailWord_6978179
  simp only [CollatzResearch.WordTrace]
  refine ⟨254515097386256735936009591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169676731590837823957339727 254515097386256735936009591)
  ·
    refine ⟨381772646079385103904014387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254515097386256735936009591 381772646079385103904014387)
    ·
      refine ⟨572658969119077655856021581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 381772646079385103904014387 572658969119077655856021581)
      ·
        refine ⟨214747113419654120946008093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 572658969119077655856021581 214747113419654120946008093)
        ·
          refine ⟨80530167532370295354753035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 214747113419654120946008093 80530167532370295354753035)
          ·
            refine ⟨120795251298555443032129553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80530167532370295354753035 120795251298555443032129553)
            ·
              refine ⟨90596438473916582274097165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120795251298555443032129553 90596438473916582274097165)
              ·
                refine ⟨33973664427718718352786437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90596438473916582274097165 33973664427718718352786437)
                ·
                  refine ⟨6370062080197259691147457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33973664427718718352786437 6370062080197259691147457)
                  ·
                    refine ⟨4777546560147944768360593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6370062080197259691147457 4777546560147944768360593)
                    ·
                      refine ⟨3583159920110958576270445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4777546560147944768360593 3583159920110958576270445)
                      ·
                        rfl

theorem cell23_6978179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 3, 4, 2, 2].length) (baseStart_6978179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6978179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6978179 prefixEnd_6978179 := by exact prefixLift 6978179
  have htrace : WordTrace (prefixWord ++ tailWord_6978179) baseStart_6978179 baseEnd_6978179 := by
    simpa [prefixWord, tailWord_6978179, baseEnd_6978179] using wordTrace_append hprefix tailTrace_6978179
  have hstable : (prefixWord ++ tailWord_6978179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6978179).length < 2 ^ (prefixWord ++ tailWord_6978179).sum := by decide
  have hdescent : baseEnd_6978179 < baseStart_6978179 := by decide
  rcases family_descends (prefixWord ++ tailWord_6978179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6978185 : List Nat := [1, 2, 1, 1, 4, 1, 1, 5, 7]
def baseStart_6978185 : Nat := 118140960795 + 6978185 * 2 ^ 59
def prefixEnd_6978185 : Nat := 4983230072969 + 3 ^ 40 * 6978185 * 2
def baseEnd_6978185 : Nat := 398129222332765061421713

theorem tailTrace_6978185 : CollatzResearch.WordTrace tailWord_6978185 prefixEnd_6978185 398129222332765061421713 := by
  unfold tailWord_6978185
  simp only [CollatzResearch.WordTrace]
  refine ⟨254515316224234998960728009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169676877482823332640485339 254515316224234998960728009)
  ·
    refine ⟨190886487168176249220546007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254515316224234998960728009 190886487168176249220546007)
    ·
      refine ⟨286329730752264373830819011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190886487168176249220546007 286329730752264373830819011)
      ·
        refine ⟨429494596128396560746228517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286329730752264373830819011 429494596128396560746228517)
        ·
          refine ⟨80530236774074355139917847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 429494596128396560746228517 80530236774074355139917847)
          ·
            refine ⟨120795355161111532709876771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80530236774074355139917847 120795355161111532709876771)
            ·
              refine ⟨181193032741667299064815157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120795355161111532709876771 181193032741667299064815157)
              ·
                refine ⟨16986846819531309287326421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 181193032741667299064815157 16986846819531309287326421)
                ·
                  refine ⟨398129222332765061421713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16986846819531309287326421 398129222332765061421713)
                  ·
                    rfl

theorem cell23_6978185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 5, 7].length) (baseStart_6978185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6978185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6978185 prefixEnd_6978185 := by exact prefixLift 6978185
  have htrace : WordTrace (prefixWord ++ tailWord_6978185) baseStart_6978185 baseEnd_6978185 := by
    simpa [prefixWord, tailWord_6978185, baseEnd_6978185] using wordTrace_append hprefix tailTrace_6978185
  have hstable : (prefixWord ++ tailWord_6978185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6978185).length < 2 ^ (prefixWord ++ tailWord_6978185).sum := by decide
  have hdescent : baseEnd_6978185 < baseStart_6978185 := by decide
  rcases family_descends (prefixWord ++ tailWord_6978185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6978196 : List Nat := [2, 4, 2, 2, 1, 1, 1, 3, 1, 4, 2]
def baseStart_6978196 : Nat := 118140960795 + 6978196 * 2 ^ 59
def prefixEnd_6978196 : Nat := 4983230072969 + 3 ^ 40 * 6978196 * 2
def baseEnd_6978196 : Nat := 3583168649282085009757867

theorem tailTrace_6978196 : CollatzResearch.WordTrace tailWord_6978196 prefixEnd_6978196 3583168649282085009757867 := by
  unfold tailWord_6978196
  simp only [CollatzResearch.WordTrace]
  refine ⟨127257858713597573919689221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169677144951463431892918961 127257858713597573919689221)
  ·
    refine ⟨23860848508799545109941729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 127257858713597573919689221 23860848508799545109941729)
    ·
      refine ⟨17895636381599658832456297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23860848508799545109941729 17895636381599658832456297)
      ·
        refine ⟨13421727286199744124342223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17895636381599658832456297 13421727286199744124342223)
        ·
          refine ⟨20132590929299616186513335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13421727286199744124342223 20132590929299616186513335)
          ·
            refine ⟨30198886393949424279770003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20132590929299616186513335 30198886393949424279770003)
            ·
              refine ⟨45298329590924136419655005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30198886393949424279770003 45298329590924136419655005)
              ·
                refine ⟨16986873596596551157370627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45298329590924136419655005 16986873596596551157370627)
                ·
                  refine ⟨25480310394894826736055941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16986873596596551157370627 25480310394894826736055941)
                  ·
                    refine ⟨4777558199042780013010489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25480310394894826736055941 4777558199042780013010489)
                    ·
                      refine ⟨3583168649282085009757867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4777558199042780013010489 3583168649282085009757867)
                      ·
                        rfl

theorem cell23_6978196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 3, 1, 4, 2].length) (baseStart_6978196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6978196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6978196 prefixEnd_6978196 := by exact prefixLift 6978196
  have htrace : WordTrace (prefixWord ++ tailWord_6978196) baseStart_6978196 baseEnd_6978196 := by
    simpa [prefixWord, tailWord_6978196, baseEnd_6978196] using wordTrace_append hprefix tailTrace_6978196
  have hstable : (prefixWord ++ tailWord_6978196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6978196).length < 2 ^ (prefixWord ++ tailWord_6978196).sum := by decide
  have hdescent : baseEnd_6978196 < baseStart_6978196 := by decide
  rcases family_descends (prefixWord ++ tailWord_6978196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6978212 : List Nat := [2, 3, 1, 2, 2, 1, 1, 2, 1, 5, 3]
def baseStart_6978212 : Nat := 118140960795 + 6978212 * 2 ^ 59
def prefixEnd_6978212 : Nat := 4983230072969 + 3 ^ 40 * 6978212 * 2
def baseEnd_6978212 : Nat := 3583176864972556947157793

theorem tailTrace_6978212 : CollatzResearch.WordTrace tailWord_6978212 prefixEnd_6978212 3583176864972556947157793 := by
  unfold tailWord_6978212
  simp only [CollatzResearch.WordTrace]
  refine ⟨127258150497568591285980445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169677533996758121714640593 127258150497568591285980445)
  ·
    refine ⟨47721806436588221732242667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127258150497568591285980445 47721806436588221732242667)
    ·
      refine ⟨71582709654882332598364001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47721806436588221732242667 71582709654882332598364001)
      ·
        refine ⟨53687032241161749448773001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71582709654882332598364001 53687032241161749448773001)
        ·
          refine ⟨40265274180871312086579751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53687032241161749448773001 40265274180871312086579751)
          ·
            refine ⟨60397911271306968129869627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40265274180871312086579751 60397911271306968129869627)
            ·
              refine ⟨90596866906960452194804441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60397911271306968129869627 90596866906960452194804441)
              ·
                refine ⟨67947650180220339146103331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90596866906960452194804441 67947650180220339146103331)
                ·
                  refine ⟨101921475270330508719154997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67947650180220339146103331 101921475270330508719154997)
                  ·
                    refine ⟨9555138306593485192420781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 101921475270330508719154997 9555138306593485192420781)
                    ·
                      refine ⟨3583176864972556947157793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9555138306593485192420781 3583176864972556947157793)
                      ·
                        rfl

theorem cell23_6978212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 2, 1, 5, 3].length) (baseStart_6978212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6978212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6978212 prefixEnd_6978212 := by exact prefixLift 6978212
  have htrace : WordTrace (prefixWord ++ tailWord_6978212) baseStart_6978212 baseEnd_6978212 := by
    simpa [prefixWord, tailWord_6978212, baseEnd_6978212] using wordTrace_append hprefix tailTrace_6978212
  have hstable : (prefixWord ++ tailWord_6978212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6978212).length < 2 ^ (prefixWord ++ tailWord_6978212).sum := by decide
  have hdescent : baseEnd_6978212 < baseStart_6978212 := by decide
  rcases family_descends (prefixWord ++ tailWord_6978212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6978229 : List Nat := [1, 3, 3, 3, 1, 1, 1, 2, 2, 3, 3]
def baseStart_6978229 : Nat := 118140960795 + 6978229 * 2 ^ 59
def prefixEnd_6978229 : Nat := 4983230072969 + 3 ^ 40 * 6978229 * 2
def baseEnd_6978229 : Nat := 3583185594143683380645215

theorem tailTrace_6978229 : CollatzResearch.WordTrace tailWord_6978229 prefixEnd_6978229 3583185594143683380645215 := by
  unfold tailWord_6978229
  simp only [CollatzResearch.WordTrace]
  refine ⟨254516921036075594475329741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169677947357383729650219827 254516921036075594475329741)
  ·
    refine ⟨95443845388528347928248653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 254516921036075594475329741 95443845388528347928248653)
    ·
      refine ⟨35791442020698130473093245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95443845388528347928248653 35791442020698130473093245)
      ·
        refine ⟨13421790757761798927409967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35791442020698130473093245 13421790757761798927409967)
        ·
          refine ⟨20132686136642698391114951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13421790757761798927409967 20132686136642698391114951)
          ·
            refine ⟨30199029204964047586672427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20132686136642698391114951 30199029204964047586672427)
            ·
              refine ⟨45298543807446071380008641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30199029204964047586672427 45298543807446071380008641)
              ·
                refine ⟨33973907855584553535006481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45298543807446071380008641 33973907855584553535006481)
                ·
                  refine ⟨25480430891688415151254861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33973907855584553535006481 25480430891688415151254861)
                  ·
                    refine ⟨9555161584383155681720573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25480430891688415151254861 9555161584383155681720573)
                    ·
                      refine ⟨3583185594143683380645215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9555161584383155681720573 3583185594143683380645215)
                      ·
                        rfl

theorem cell23_6978229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_6978229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6978229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6978229 prefixEnd_6978229 := by exact prefixLift 6978229
  have htrace : WordTrace (prefixWord ++ tailWord_6978229) baseStart_6978229 baseEnd_6978229 := by
    simpa [prefixWord, tailWord_6978229, baseEnd_6978229] using wordTrace_append hprefix tailTrace_6978229
  have hstable : (prefixWord ++ tailWord_6978229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6978229).length < 2 ^ (prefixWord ++ tailWord_6978229).sum := by decide
  have hdescent : baseEnd_6978229 < baseStart_6978229 := by decide
  rcases family_descends (prefixWord ++ tailWord_6978229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6978230 : List Nat := [5, 1, 3, 1, 2, 1, 1, 1, 4, 2, 2]
def baseStart_6978230 : Nat := 118140960795 + 6978230 * 2 ^ 59
def prefixEnd_6978230 : Nat := 4983230072969 + 3 ^ 40 * 6978230 * 2
def baseEnd_6978230 : Nat := 3583186107624337876732711

theorem tailTrace_6978230 : CollatzResearch.WordTrace tailWord_6978230 prefixEnd_6978230 3583186107624337876732711 := by
  unfold tailWord_6978230
  simp only [CollatzResearch.WordTrace]
  refine ⟨15907309844316998227882259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 169677971672714647764077429 15907309844316998227882259)
  ·
    refine ⟨23860964766475497341823389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15907309844316998227882259 23860964766475497341823389)
    ·
      refine ⟨8947861787428311503183771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23860964766475497341823389 8947861787428311503183771)
      ·
        refine ⟨13421792681142467254775657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8947861787428311503183771 13421792681142467254775657)
        ·
          refine ⟨10066344510856850441081743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13421792681142467254775657 10066344510856850441081743)
          ·
            refine ⟨15099516766285275661622615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10066344510856850441081743 15099516766285275661622615)
            ·
              refine ⟨22649275149427913492433923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15099516766285275661622615 22649275149427913492433923)
              ·
                refine ⟨33973912724141870238650885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22649275149427913492433923 33973912724141870238650885)
                ·
                  refine ⟨6370108635776600669747041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33973912724141870238650885 6370108635776600669747041)
                  ·
                    refine ⟨4777581476832450502310281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6370108635776600669747041 4777581476832450502310281)
                    ·
                      refine ⟨3583186107624337876732711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4777581476832450502310281 3583186107624337876732711)
                      ·
                        rfl

theorem cell23_6978230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 1, 4, 2, 2].length) (baseStart_6978230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6978230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6978230 prefixEnd_6978230 := by exact prefixLift 6978230
  have htrace : WordTrace (prefixWord ++ tailWord_6978230) baseStart_6978230 baseEnd_6978230 := by
    simpa [prefixWord, tailWord_6978230, baseEnd_6978230] using wordTrace_append hprefix tailTrace_6978230
  have hstable : (prefixWord ++ tailWord_6978230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6978230).length < 2 ^ (prefixWord ++ tailWord_6978230).sum := by decide
  have hdescent : baseEnd_6978230 < baseStart_6978230 := by decide
  rcases family_descends (prefixWord ++ tailWord_6978230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6978245 : List Nat := [1, 3, 1, 1, 1, 1, 2, 1, 4, 8]
def baseStart_6978245 : Nat := 118140960795 + 6978245 * 2 ^ 59
def prefixEnd_6978245 : Nat := 4983230072969 + 3 ^ 40 * 6978245 * 2
def baseEnd_6978245 : Nat := 1194397936611385106015047

theorem tailTrace_6978245 : CollatzResearch.WordTrace tailWord_6978245 prefixEnd_6978245 1194397936611385106015047 := by
  unfold tailWord_6978245
  simp only [CollatzResearch.WordTrace]
  refine ⟨254517504604017629207912189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169678336402678419471941459 254517504604017629207912189)
  ·
    refine ⟨95444064226506610952967071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 254517504604017629207912189 95444064226506610952967071)
    ·
      refine ⟨143166096339759916429450607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95444064226506610952967071 143166096339759916429450607)
      ·
        refine ⟨214749144509639874644175911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143166096339759916429450607 214749144509639874644175911)
        ·
          refine ⟨322123716764459811966263867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214749144509639874644175911 322123716764459811966263867)
          ·
            refine ⟨483185575146689717949395801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 322123716764459811966263867 483185575146689717949395801)
            ·
              refine ⟨362389181360017288462046851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 483185575146689717949395801 362389181360017288462046851)
              ·
                refine ⟨543583772040025932693070277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 362389181360017288462046851 543583772040025932693070277)
                ·
                  refine ⟨101921957257504862379950677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 543583772040025932693070277 101921957257504862379950677)
                  ·
                    refine ⟨1194397936611385106015047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 101921957257504862379950677 1194397936611385106015047)
                    ·
                      rfl

theorem cell23_6978245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 4, 8].length) (baseStart_6978245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6978245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6978245 prefixEnd_6978245 := by exact prefixLift 6978245
  have htrace : WordTrace (prefixWord ++ tailWord_6978245) baseStart_6978245 baseEnd_6978245 := by
    simpa [prefixWord, tailWord_6978245, baseEnd_6978245] using wordTrace_append hprefix tailTrace_6978245
  have hstable : (prefixWord ++ tailWord_6978245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6978245).length < 2 ^ (prefixWord ++ tailWord_6978245).sum := by decide
  have hdescent : baseEnd_6978245 < baseStart_6978245 := by decide
  rcases family_descends (prefixWord ++ tailWord_6978245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6978289 : List Nat := [1, 2, 2, 2, 2, 2, 3, 2, 2, 2, 3]
def baseStart_6978289 : Nat := 118140960795 + 6978289 * 2 ^ 59
def prefixEnd_6978289 : Nat := 4983230072969 + 3 ^ 40 * 6978289 * 2
def baseEnd_6978289 : Nat := 3583216402982953145894939

theorem tailTrace_6978289 : CollatzResearch.WordTrace tailWord_6978289 prefixEnd_6978289 3583216402982953145894939 := by
  unfold tailWord_6978289
  simp only [CollatzResearch.WordTrace]
  refine ⟨254519109415858224722513921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169679406277238816481675947 254519109415858224722513921)
  ·
    refine ⟨190889332061893668541885441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254519109415858224722513921 190889332061893668541885441)
    ·
      refine ⟨143166999046420251406414081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190889332061893668541885441 143166999046420251406414081)
      ·
        refine ⟨107375249284815188554810561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143166999046420251406414081 107375249284815188554810561)
        ·
          refine ⟨80531436963611391416107921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107375249284815188554810561 80531436963611391416107921)
          ·
            refine ⟨60398577722708543562080941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80531436963611391416107921 60398577722708543562080941)
            ·
              refine ⟨22649466646015703835780353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60398577722708543562080941 22649466646015703835780353)
              ·
                refine ⟨16987099984511777876835265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22649466646015703835780353 16987099984511777876835265)
                ·
                  refine ⟨12740324988383833407626449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16987099984511777876835265 12740324988383833407626449)
                  ·
                    refine ⟨9555243741287875055719837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12740324988383833407626449 9555243741287875055719837)
                    ·
                      refine ⟨3583216402982953145894939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9555243741287875055719837 3583216402982953145894939)
                      ·
                        rfl

theorem cell23_6978289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 2, 2, 2, 3].length) (baseStart_6978289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6978289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6978289 prefixEnd_6978289 := by exact prefixLift 6978289
  have htrace : WordTrace (prefixWord ++ tailWord_6978289) baseStart_6978289 baseEnd_6978289 := by
    simpa [prefixWord, tailWord_6978289, baseEnd_6978289] using wordTrace_append hprefix tailTrace_6978289
  have hstable : (prefixWord ++ tailWord_6978289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6978289).length < 2 ^ (prefixWord ++ tailWord_6978289).sum := by decide
  have hdescent : baseEnd_6978289 < baseStart_6978289 := by decide
  rcases family_descends (prefixWord ++ tailWord_6978289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6978293 : List Nat := [1, 3, 6, 1, 1, 1, 1, 1, 1, 2, 5]
def baseStart_6978293 : Nat := 118140960795 + 6978293 * 2 ^ 59
def prefixEnd_6978293 : Nat := 4983230072969 + 3 ^ 40 * 6978293 * 2
def baseEnd_6978293 : Nat := 3583218456905571130244921

theorem tailTrace_6978293 : CollatzResearch.WordTrace tailWord_6978293 prefixEnd_6978293 3583218456905571130244921 := by
  unfold tailWord_6978293
  simp only [CollatzResearch.WordTrace]
  refine ⟨254519255307843733405659533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169679503538562488937106355 254519255307843733405659533)
  ·
    refine ⟨95444720740441400027122325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 254519255307843733405659533 95444720740441400027122325)
    ·
      refine ⟨4473971284708190626271359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 95444720740441400027122325 4473971284708190626271359)
      ·
        refine ⟨6710956927062285939407039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4473971284708190626271359 6710956927062285939407039)
        ·
          refine ⟨10066435390593428909110559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6710956927062285939407039 10066435390593428909110559)
          ·
            refine ⟨15099653085890143363665839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10066435390593428909110559 15099653085890143363665839)
            ·
              refine ⟨22649479628835215045498759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15099653085890143363665839 22649479628835215045498759)
              ·
                refine ⟨33974219443252822568248139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22649479628835215045498759 33974219443252822568248139)
                ·
                  refine ⟨50961329164879233852372209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33974219443252822568248139 50961329164879233852372209)
                  ·
                    refine ⟨38220996873659425389279157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50961329164879233852372209 38220996873659425389279157)
                    ·
                      refine ⟨3583218456905571130244921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38220996873659425389279157 3583218456905571130244921)
                      ·
                        rfl

theorem cell23_6978293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_6978293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6978293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6978293 prefixEnd_6978293 := by exact prefixLift 6978293
  have htrace : WordTrace (prefixWord ++ tailWord_6978293) baseStart_6978293 baseEnd_6978293 := by
    simpa [prefixWord, tailWord_6978293, baseEnd_6978293] using wordTrace_append hprefix tailTrace_6978293
  have hstable : (prefixWord ++ tailWord_6978293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6978293).length < 2 ^ (prefixWord ++ tailWord_6978293).sum := by decide
  have hdescent : baseEnd_6978293 < baseStart_6978293 := by decide
  rcases family_descends (prefixWord ++ tailWord_6978293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6978319 : List Nat := [1, 1, 2, 1, 1, 1, 6, 1, 5, 1, 3]
def baseStart_6978319 : Nat := 118140960795 + 6978319 * 2 ^ 59
def prefixEnd_6978319 : Nat := 4983230072969 + 3 ^ 40 * 6978319 * 2
def baseEnd_6978319 : Nat := 3583231807402588028519801

theorem tailTrace_6978319 : CollatzResearch.WordTrace tailWord_6978319 prefixEnd_6978319 3583231807402588028519801 := by
  unfold tailWord_6978319
  simp only [CollatzResearch.WordTrace]
  refine ⟨254520203605749539846106011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169680135737166359897404007 254520203605749539846106011)
  ·
    refine ⟨381780305408624309769159017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254520203605749539846106011 381780305408624309769159017)
    ·
      refine ⟨286335229056468232326869263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 381780305408624309769159017 286335229056468232326869263)
      ·
        refine ⟨429502843584702348490303895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286335229056468232326869263 429502843584702348490303895)
        ·
          refine ⟨644254265377053522735455843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 429502843584702348490303895 644254265377053522735455843)
          ·
            refine ⟨966381398065580284103183765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 644254265377053522735455843 966381398065580284103183765)
            ·
              refine ⟨45299128034324075817336739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 966381398065580284103183765 45299128034324075817336739)
              ·
                refine ⟨67948692051486113726005109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45299128034324075817336739 67948692051486113726005109)
                ·
                  refine ⟨6370189879826823161812979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 67948692051486113726005109 6370189879826823161812979)
                  ·
                    refine ⟨9555284819740234742719469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6370189879826823161812979 9555284819740234742719469)
                    ·
                      refine ⟨3583231807402588028519801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9555284819740234742719469 3583231807402588028519801)
                      ·
                        rfl

theorem cell23_6978319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 1, 5, 1, 3].length) (baseStart_6978319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6978319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6978319 prefixEnd_6978319 := by exact prefixLift 6978319
  have htrace : WordTrace (prefixWord ++ tailWord_6978319) baseStart_6978319 baseEnd_6978319 := by
    simpa [prefixWord, tailWord_6978319, baseEnd_6978319] using wordTrace_append hprefix tailTrace_6978319
  have hstable : (prefixWord ++ tailWord_6978319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6978319).length < 2 ^ (prefixWord ++ tailWord_6978319).sum := by decide
  have hdescent : baseEnd_6978319 < baseStart_6978319 := by decide
  rcases family_descends (prefixWord ++ tailWord_6978319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6978353 : List Nat := [1, 2, 2, 3, 2, 1, 3, 4, 1, 1, 3]
def baseStart_6978353 : Nat := 118140960795 + 6978353 * 2 ^ 59
def prefixEnd_6978353 : Nat := 4983230072969 + 3 ^ 40 * 6978353 * 2
def baseEnd_6978353 : Nat := 3583249265744840895494645

theorem tailTrace_6978353 : CollatzResearch.WordTrace tailWord_6978353 prefixEnd_6978353 3583249265744840895494645 := by
  unfold tailWord_6978353
  simp only [CollatzResearch.WordTrace]
  refine ⟨254521443687626363652843713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169680962458417575768562475 254521443687626363652843713)
  ·
    refine ⟨190891082765719772739632785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254521443687626363652843713 190891082765719772739632785)
    ·
      refine ⟨143168312074289829554724589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190891082765719772739632785 143168312074289829554724589)
      ·
        refine ⟨53688117027858686083021721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143168312074289829554724589 53688117027858686083021721)
        ·
          refine ⟨40266087770894014562266291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53688117027858686083021721 40266087770894014562266291)
          ·
            refine ⟨60399131656341021843399437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40266087770894014562266291 60399131656341021843399437)
            ·
              refine ⟨22649674371127883191274789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60399131656341021843399437 22649674371127883191274789)
              ·
                refine ⟨4246813944586478098364023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22649674371127883191274789 4246813944586478098364023)
                ·
                  refine ⟨6370220916879717147546035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4246813944586478098364023 6370220916879717147546035)
                  ·
                    refine ⟨9555331375319575721319053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6370220916879717147546035 9555331375319575721319053)
                    ·
                      refine ⟨3583249265744840895494645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9555331375319575721319053 3583249265744840895494645)
                      ·
                        rfl

theorem cell23_6978353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 4, 1, 1, 3].length) (baseStart_6978353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6978353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6978353 prefixEnd_6978353 := by exact prefixLift 6978353
  have htrace : WordTrace (prefixWord ++ tailWord_6978353) baseStart_6978353 baseEnd_6978353 := by
    simpa [prefixWord, tailWord_6978353, baseEnd_6978353] using wordTrace_append hprefix tailTrace_6978353
  have hstable : (prefixWord ++ tailWord_6978353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6978353).length < 2 ^ (prefixWord ++ tailWord_6978353).sum := by decide
  have hdescent : baseEnd_6978353 < baseStart_6978353 := by decide
  rcases family_descends (prefixWord ++ tailWord_6978353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6978382 : List Nat := [4, 1, 1, 1, 1, 1, 1, 13]
def baseStart_6978382 : Nat := 118140960795 + 6978382 * 2 ^ 59
def prefixEnd_6978382 : Nat := 4983230072969 + 3 ^ 40 * 6978382 * 2
def baseEnd_6978382 : Nat := 132713487284585973408593

theorem tailTrace_6978382 : CollatzResearch.WordTrace tailWord_6978382 prefixEnd_6978382 132713487284585973408593 := by
  unfold tailWord_6978382
  simp only [CollatzResearch.WordTrace]
  refine ⟨31815312675565162700706175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 169681667603014201070432933 31815312675565162700706175)
  ·
    refine ⟨47722969013347744051059263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31815312675565162700706175 47722969013347744051059263)
    ·
      refine ⟨71584453520021616076588895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47722969013347744051059263 71584453520021616076588895)
      ·
        refine ⟨107376680280032424114883343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71584453520021616076588895 107376680280032424114883343)
        ·
          refine ⟨161065020420048636172325015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107376680280032424114883343 161065020420048636172325015)
          ·
            refine ⟨241597530630072954258487523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161065020420048636172325015 241597530630072954258487523)
            ·
              refine ⟨362396295945109431387731285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 241597530630072954258487523 362396295945109431387731285)
              ·
                refine ⟨132713487284585973408593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 362396295945109431387731285 132713487284585973408593)
                ·
                  rfl

theorem cell23_6978382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 13].length) (baseStart_6978382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6978382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6978382 prefixEnd_6978382 := by exact prefixLift 6978382
  have htrace : WordTrace (prefixWord ++ tailWord_6978382) baseStart_6978382 baseEnd_6978382 := by
    simpa [prefixWord, tailWord_6978382, baseEnd_6978382] using wordTrace_append hprefix tailTrace_6978382
  have hstable : (prefixWord ++ tailWord_6978382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6978382).length < 2 ^ (prefixWord ++ tailWord_6978382).sum := by decide
  have hdescent : baseEnd_6978382 < baseStart_6978382 := by decide
  rcases family_descends (prefixWord ++ tailWord_6978382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6978389 : List Nat := [1, 3, 2, 2, 2, 1, 1, 4, 1, 2, 4]
def baseStart_6978389 : Nat := 118140960795 + 6978389 * 2 ^ 59
def prefixEnd_6978389 : Nat := 4983230072969 + 3 ^ 40 * 6978389 * 2
def baseEnd_6978389 : Nat := 3583267751048402754644479

theorem tailTrace_6978389 : CollatzResearch.WordTrace tailWord_6978389 prefixEnd_6978389 3583267751048402754644479 := by
  unfold tailWord_6978389
  simp only [CollatzResearch.WordTrace]
  refine ⟨254522756715495941801154221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169681837810330627867436147 254522756715495941801154221)
  ·
    refine ⟨95446033768310978175432833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 254522756715495941801154221 95446033768310978175432833)
    ·
      refine ⟨71584525326233233631574625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95446033768310978175432833 71584525326233233631574625)
      ·
        refine ⟨53688393994674925223680969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71584525326233233631574625 53688393994674925223680969)
        ·
          refine ⟨40266295496006193917760727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53688393994674925223680969 40266295496006193917760727)
          ·
            refine ⟨60399443244009290876641091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40266295496006193917760727 60399443244009290876641091)
            ·
              refine ⟨90599164866013936314961637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60399443244009290876641091 90599164866013936314961637)
              ·
                refine ⟨16987343412377613059055307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 90599164866013936314961637 16987343412377613059055307)
                ·
                  refine ⟨25481015118566419588582961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16987343412377613059055307 25481015118566419588582961)
                  ·
                    refine ⟨19110761338924814691437221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25481015118566419588582961 19110761338924814691437221)
                    ·
                      refine ⟨3583267751048402754644479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19110761338924814691437221 3583267751048402754644479)
                      ·
                        rfl

theorem cell23_6978389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 4, 1, 2, 4].length) (baseStart_6978389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6978389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6978389 prefixEnd_6978389 := by exact prefixLift 6978389
  have htrace : WordTrace (prefixWord ++ tailWord_6978389) baseStart_6978389 baseEnd_6978389 := by
    simpa [prefixWord, tailWord_6978389, baseEnd_6978389] using wordTrace_append hprefix tailTrace_6978389
  have hstable : (prefixWord ++ tailWord_6978389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6978389).length < 2 ^ (prefixWord ++ tailWord_6978389).sum := by decide
  have hdescent : baseEnd_6978389 < baseStart_6978389 := by decide
  rcases family_descends (prefixWord ++ tailWord_6978389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6978393 : List Nat := [1, 2, 1, 2, 2, 6, 2, 1, 1, 1, 4]
def baseStart_6978393 : Nat := 118140960795 + 6978393 * 2 ^ 59
def prefixEnd_6978393 : Nat := 4983230072969 + 3 ^ 40 * 6978393 * 2
def baseEnd_6978393 : Nat := 3583269804971020738994461

theorem tailTrace_6978393 : CollatzResearch.WordTrace tailWord_6978393 prefixEnd_6978393 3583269804971020738994461 := by
  unfold tailWord_6978393
  simp only [CollatzResearch.WordTrace]
  refine ⟨254522902607481450484299833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169681935071654300322866555 254522902607481450484299833)
  ·
    refine ⟨190892176955611087863224875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254522902607481450484299833 190892176955611087863224875)
    ·
      refine ⟨286338265433416631794837313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190892176955611087863224875 286338265433416631794837313)
      ·
        refine ⟨214753699075062473846127985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 286338265433416631794837313 214753699075062473846127985)
        ·
          refine ⟨161065274306296855384595989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 214753699075062473846127985 161065274306296855384595989)
          ·
            refine ⟨7549934733107665096152937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 161065274306296855384595989 7549934733107665096152937)
            ·
              refine ⟨5662451049830748822114703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7549934733107665096152937 5662451049830748822114703)
              ·
                refine ⟨8493676574746123233172055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5662451049830748822114703 8493676574746123233172055)
                ·
                  refine ⟨12740514862119184849758083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8493676574746123233172055 12740514862119184849758083)
                  ·
                    refine ⟨19110772293178777274637125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12740514862119184849758083 19110772293178777274637125)
                    ·
                      refine ⟨3583269804971020738994461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19110772293178777274637125 3583269804971020738994461)
                      ·
                        rfl

theorem cell23_6978393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 2, 1, 1, 1, 4].length) (baseStart_6978393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6978393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6978393 prefixEnd_6978393 := by exact prefixLift 6978393
  have htrace : WordTrace (prefixWord ++ tailWord_6978393) baseStart_6978393 baseEnd_6978393 := by
    simpa [prefixWord, tailWord_6978393, baseEnd_6978393] using wordTrace_append hprefix tailTrace_6978393
  have hstable : (prefixWord ++ tailWord_6978393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6978393).length < 2 ^ (prefixWord ++ tailWord_6978393).sum := by decide
  have hdescent : baseEnd_6978393 < baseStart_6978393 := by decide
  rcases family_descends (prefixWord ++ tailWord_6978393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6978403 : List Nat := [1, 1, 1, 5, 3, 3, 1, 2, 2, 4]
def baseStart_6978403 : Nat := 118140960795 + 6978403 * 2 ^ 59
def prefixEnd_6978403 : Nat := 4983230072969 + 3 ^ 40 * 6978403 * 2
def baseEnd_6978403 : Nat := 1194424979925855233289805

theorem tailTrace_6978403 : CollatzResearch.WordTrace tailWord_6978403 prefixEnd_6978403 1194424979925855233289805 := by
  unfold tailWord_6978403
  simp only [CollatzResearch.WordTrace]
  refine ⟨254523267337445222192163863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169682178224963481461442575 254523267337445222192163863)
  ·
    refine ⟨381784901006167833288245795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254523267337445222192163863 381784901006167833288245795)
    ·
      refine ⟨572677351509251749932368693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 381784901006167833288245795 572677351509251749932368693)
      ·
        refine ⟨53688501703992351556159565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 572677351509251749932368693 53688501703992351556159565)
        ·
          refine ⟨20133188138997131833559837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53688501703992351556159565 20133188138997131833559837)
          ·
            refine ⟨7549945552123924437584939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20133188138997131833559837 7549945552123924437584939)
            ·
              refine ⟨11324918328185886656377409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7549945552123924437584939 11324918328185886656377409)
              ·
                refine ⟨8493688746139414992283057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11324918328185886656377409 8493688746139414992283057)
                ·
                  refine ⟨6370266559604561244212293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8493688746139414992283057 6370266559604561244212293)
                  ·
                    refine ⟨1194424979925855233289805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6370266559604561244212293 1194424979925855233289805)
                    ·
                      rfl

theorem cell23_6978403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 1, 2, 2, 4].length) (baseStart_6978403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6978403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6978403 prefixEnd_6978403 := by exact prefixLift 6978403
  have htrace : WordTrace (prefixWord ++ tailWord_6978403) baseStart_6978403 baseEnd_6978403 := by
    simpa [prefixWord, tailWord_6978403, baseEnd_6978403] using wordTrace_append hprefix tailTrace_6978403
  have hstable : (prefixWord ++ tailWord_6978403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6978403).length < 2 ^ (prefixWord ++ tailWord_6978403).sum := by decide
  have hdescent : baseEnd_6978403 < baseStart_6978403 := by decide
  rcases family_descends (prefixWord ++ tailWord_6978403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6978432 : List Nat := [2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 8]
def baseStart_6978432 : Nat := 118140960795 + 6978432 * 2 ^ 59
def prefixEnd_6978432 : Nat := 4983230072969 + 3 ^ 40 * 6978432 * 2
def baseEnd_6978432 : Nat := 3583289830716546086406781

theorem tailTrace_6978432 : CollatzResearch.WordTrace tailWord_6978432 prefixEnd_6978432 3583289830716546086406781 := by
  unfold tailWord_6978432
  simp only [CollatzResearch.WordTrace]
  refine ⟨127262162527170080072484775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169682883369560106763313033 127262162527170080072484775)
  ·
    refine ⟨190893243790755120108727163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127262162527170080072484775 190893243790755120108727163)
    ·
      refine ⟨286339865686132680163090745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190893243790755120108727163 286339865686132680163090745)
      ·
        refine ⟨214754899264599510122318059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 286339865686132680163090745 214754899264599510122318059)
        ·
          refine ⟨322132348896899265183477089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214754899264599510122318059 322132348896899265183477089)
          ·
            refine ⟨241599261672674448887607817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 322132348896899265183477089 241599261672674448887607817)
            ·
              refine ⟨181199446254505836665705863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 241599261672674448887607817 181199446254505836665705863)
              ·
                refine ⟨271799169381758754998558795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 181199446254505836665705863 271799169381758754998558795)
                ·
                  refine ⟨407698754072638132497838193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 271799169381758754998558795 407698754072638132497838193)
                  ·
                    refine ⟨305774065554478599373378645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 407698754072638132497838193 305774065554478599373378645)
                    ·
                      refine ⟨3583289830716546086406781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 305774065554478599373378645 3583289830716546086406781)
                      ·
                        rfl

theorem cell23_6978432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 8].length) (baseStart_6978432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6978432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6978432 prefixEnd_6978432 := by exact prefixLift 6978432
  have htrace : WordTrace (prefixWord ++ tailWord_6978432) baseStart_6978432 baseEnd_6978432 := by
    simpa [prefixWord, tailWord_6978432, baseEnd_6978432] using wordTrace_append hprefix tailTrace_6978432
  have hstable : (prefixWord ++ tailWord_6978432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6978432).length < 2 ^ (prefixWord ++ tailWord_6978432).sum := by decide
  have hdescent : baseEnd_6978432 < baseStart_6978432 := by decide
  rcases family_descends (prefixWord ++ tailWord_6978432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6978439 : List Nat := [1, 1, 4, 2, 3, 1, 1, 1, 2, 2, 5]
def baseStart_6978439 : Nat := 118140960795 + 6978439 * 2 ^ 59
def prefixEnd_6978439 : Nat := 4983230072969 + 3 ^ 40 * 6978439 * 2
def baseEnd_6978439 : Nat := 3583293425081127559019249

theorem tailTrace_6978439 : CollatzResearch.WordTrace tailWord_6978439 prefixEnd_6978439 3583293425081127559019249 := by
  unfold tailWord_6978439
  simp only [CollatzResearch.WordTrace]
  refine ⟨254524580365314800340474371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169683053576876533560316247 254524580365314800340474371)
  ·
    refine ⟨381786870547972200510711557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254524580365314800340474371 381786870547972200510711557)
    ·
      refine ⟨71585038227744787595758417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 381786870547972200510711557 71585038227744787595758417)
      ·
        refine ⟨53688778670808590696818813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71585038227744787595758417 53688778670808590696818813)
        ·
          refine ⟨20133292001553221511307055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53688778670808590696818813 20133292001553221511307055)
          ·
            refine ⟨30199938002329832266960583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20133292001553221511307055 30199938002329832266960583)
            ·
              refine ⟨45299907003494748400440875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30199938002329832266960583 45299907003494748400440875)
              ·
                refine ⟨67949860505242122600661313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45299907003494748400440875 67949860505242122600661313)
                ·
                  refine ⟨50962395378931591950495985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67949860505242122600661313 50962395378931591950495985)
                  ·
                    refine ⟨38221796534198693962871989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50962395378931591950495985 38221796534198693962871989)
                    ·
                      refine ⟨3583293425081127559019249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38221796534198693962871989 3583293425081127559019249)
                      ·
                        rfl

theorem cell23_6978439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 1, 2, 2, 5].length) (baseStart_6978439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6978439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6978439 prefixEnd_6978439 := by exact prefixLift 6978439
  have htrace : WordTrace (prefixWord ++ tailWord_6978439) baseStart_6978439 baseEnd_6978439 := by
    simpa [prefixWord, tailWord_6978439, baseEnd_6978439] using wordTrace_append hprefix tailTrace_6978439
  have hstable : (prefixWord ++ tailWord_6978439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6978439).length < 2 ^ (prefixWord ++ tailWord_6978439).sum := by decide
  have hdescent : baseEnd_6978439 < baseStart_6978439 := by decide
  rcases family_descends (prefixWord ++ tailWord_6978439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6978453 : List Nat := [1, 3, 2, 1, 1, 4, 2, 3, 1, 3, 2]
def baseStart_6978453 : Nat := 118140960795 + 6978453 * 2 ^ 59
def prefixEnd_6978453 : Nat := 4983230072969 + 3 ^ 40 * 6978453 * 2
def baseEnd_6978453 : Nat := 3583300613810290504244185

theorem tailTrace_6978453 : CollatzResearch.WordTrace tailWord_6978453 prefixEnd_6978453 3583300613810290504244185 := by
  unfold tailWord_6978453
  simp only [CollatzResearch.WordTrace]
  refine ⟨254525090987264080731484013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169683393991509387154322675 254525090987264080731484013)
  ·
    refine ⟨95446909120224030274306505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 254525090987264080731484013 95446909120224030274306505)
    ·
      refine ⟨71585181840168022705729879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95446909120224030274306505 71585181840168022705729879)
      ·
        refine ⟨107377772760252034058594819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71585181840168022705729879 107377772760252034058594819)
        ·
          refine ⟨161066659140378051087892229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107377772760252034058594819 161066659140378051087892229)
          ·
            refine ⟨30199998588820884578979793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 161066659140378051087892229 30199998588820884578979793)
            ·
              refine ⟨22649998941615663434234845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30199998588820884578979793 22649998941615663434234845)
              ·
                refine ⟨8493749603105873787838067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22649998941615663434234845 8493749603105873787838067)
                ·
                  refine ⟨12740624404658810681757101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8493749603105873787838067 12740624404658810681757101)
                  ·
                    refine ⟨4777734151747054005658913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12740624404658810681757101 4777734151747054005658913)
                    ·
                      refine ⟨3583300613810290504244185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4777734151747054005658913 3583300613810290504244185)
                      ·
                        rfl

theorem cell23_6978453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 3, 1, 3, 2].length) (baseStart_6978453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6978453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6978453 prefixEnd_6978453 := by exact prefixLift 6978453
  have htrace : WordTrace (prefixWord ++ tailWord_6978453) baseStart_6978453 baseEnd_6978453 := by
    simpa [prefixWord, tailWord_6978453, baseEnd_6978453] using wordTrace_append hprefix tailTrace_6978453
  have hstable : (prefixWord ++ tailWord_6978453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6978453).length < 2 ^ (prefixWord ++ tailWord_6978453).sum := by decide
  have hdescent : baseEnd_6978453 < baseStart_6978453 := by decide
  rcases family_descends (prefixWord ++ tailWord_6978453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6978477 : List Nat := [1, 5, 2, 3, 1, 1, 1, 3, 2, 1, 3]
def baseStart_6978477 : Nat := 118140960795 + 6978477 * 2 ^ 59
def prefixEnd_6978477 : Nat := 4983230072969 + 3 ^ 40 * 6978477 * 2
def baseEnd_6978477 : Nat := 3583312937345998410344075

theorem tailTrace_6978477 : CollatzResearch.WordTrace tailWord_6978477 prefixEnd_6978477 3583312937345998410344075 := by
  unfold tailWord_6978477
  simp only [CollatzResearch.WordTrace]
  refine ⟨254525966339177132830357685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169683977559451421886905123 254525966339177132830357685)
  ·
    refine ⟨23861809344297856202846033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 254525966339177132830357685 23861809344297856202846033)
    ·
      refine ⟨17896357008223392152134525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23861809344297856202846033 17896357008223392152134525)
      ·
        refine ⟨6711133878083772057050447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17896357008223392152134525 6711133878083772057050447)
        ·
          refine ⟨10066700817125658085575671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6711133878083772057050447 10066700817125658085575671)
          ·
            refine ⟨15100051225688487128363507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10066700817125658085575671 15100051225688487128363507)
            ·
              refine ⟨22650076838532730692545261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15100051225688487128363507 22650076838532730692545261)
              ·
                refine ⟨8493778814449774009704473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22650076838532730692545261 8493778814449774009704473)
                ·
                  refine ⟨6370334110837330507278355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8493778814449774009704473 6370334110837330507278355)
                  ·
                    refine ⟨9555501166255995760917533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6370334110837330507278355 9555501166255995760917533)
                    ·
                      refine ⟨3583312937345998410344075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9555501166255995760917533 3583312937345998410344075)
                      ·
                        rfl

theorem cell23_6978477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_6978477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6978477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6978477 prefixEnd_6978477 := by exact prefixLift 6978477
  have htrace : WordTrace (prefixWord ++ tailWord_6978477) baseStart_6978477 baseEnd_6978477 := by
    simpa [prefixWord, tailWord_6978477, baseEnd_6978477] using wordTrace_append hprefix tailTrace_6978477
  have hstable : (prefixWord ++ tailWord_6978477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6978477).length < 2 ^ (prefixWord ++ tailWord_6978477).sum := by decide
  have hdescent : baseEnd_6978477 < baseStart_6978477 := by decide
  rcases family_descends (prefixWord ++ tailWord_6978477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6978499 : List Nat := [1, 1, 1, 3, 1, 1, 2, 4, 1, 5, 3]
def baseStart_6978499 : Nat := 118140960795 + 6978499 * 2 ^ 59
def prefixEnd_6978499 : Nat := 4983230072969 + 3 ^ 40 * 6978499 * 2
def baseEnd_6978499 : Nat := 3583324233920397324268973

theorem tailTrace_6978499 : CollatzResearch.WordTrace tailWord_6978499 prefixEnd_6978499 3583324233920397324268973 := by
  unfold tailWord_6978499
  simp only [CollatzResearch.WordTrace]
  refine ⟨254526768745097430587658551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169684512496731620391772367 254526768745097430587658551)
  ·
    refine ⟨381790153117646145881487827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254526768745097430587658551 381790153117646145881487827)
    ·
      refine ⟨572685229676469218822231741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 381790153117646145881487827 572685229676469218822231741)
      ·
        refine ⟨214756961128675957058336903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 572685229676469218822231741 214756961128675957058336903)
        ·
          refine ⟨322135441693013935587505355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214756961128675957058336903 322135441693013935587505355)
          ·
            refine ⟨483203162539520903381258033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 322135441693013935587505355 483203162539520903381258033)
            ·
              refine ⟨362402371904640677535943525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 483203162539520903381258033 362402371904640677535943525)
              ·
                refine ⟨67950444732120127037989411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 362402371904640677535943525 67950444732120127037989411)
                ·
                  refine ⟨101925667098180190556984117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67950444732120127037989411 101925667098180190556984117)
                  ·
                    refine ⟨9555531290454392864717261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 101925667098180190556984117 9555531290454392864717261)
                    ·
                      refine ⟨3583324233920397324268973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9555531290454392864717261 3583324233920397324268973)
                      ·
                        rfl

theorem cell23_6978499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 1, 5, 3].length) (baseStart_6978499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6978499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6978499 prefixEnd_6978499 := by exact prefixLift 6978499
  have htrace : WordTrace (prefixWord ++ tailWord_6978499) baseStart_6978499 baseEnd_6978499 := by
    simpa [prefixWord, tailWord_6978499, baseEnd_6978499] using wordTrace_append hprefix tailTrace_6978499
  have hstable : (prefixWord ++ tailWord_6978499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6978499).length < 2 ^ (prefixWord ++ tailWord_6978499).sum := by decide
  have hdescent : baseEnd_6978499 < baseStart_6978499 := by decide
  rcases family_descends (prefixWord ++ tailWord_6978499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6978506 : List Nat := [3, 1, 2, 1, 2, 1, 1, 7, 5]
def baseStart_6978506 : Nat := 118140960795 + 6978506 * 2 ^ 59
def prefixEnd_6978506 : Nat := 4983230072969 + 3 ^ 40 * 6978506 * 2
def baseEnd_6978506 : Nat := 398147536476108755209049

theorem tailTrace_6978506 : CollatzResearch.WordTrace tailWord_6978506 prefixEnd_6978506 398147536476108755209049 := by
  unfold tailWord_6978506
  simp only [CollatzResearch.WordTrace]
  refine ⟨63631756014018017695790843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169684682704048047188775581 63631756014018017695790843)
  ·
    refine ⟨95447634021027026543686265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63631756014018017695790843 95447634021027026543686265)
    ·
      refine ⟨71585725515770269907764699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95447634021027026543686265 71585725515770269907764699)
      ·
        refine ⟨107378588273655404861647049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71585725515770269907764699 107378588273655404861647049)
        ·
          refine ⟨80533941205241553646235287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107378588273655404861647049 80533941205241553646235287)
          ·
            refine ⟨120800911807862330469352931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80533941205241553646235287 120800911807862330469352931)
            ·
              refine ⟨181201367711793495704029397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120800911807862330469352931 181201367711793495704029397)
              ·
                refine ⟨4246907055745160055563189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 181201367711793495704029397 4246907055745160055563189)
                ·
                  refine ⟨398147536476108755209049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4246907055745160055563189 398147536476108755209049)
                  ·
                    rfl

theorem cell23_6978506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 7, 5].length) (baseStart_6978506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6978506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6978506 prefixEnd_6978506 := by exact prefixLift 6978506
  have htrace : WordTrace (prefixWord ++ tailWord_6978506) baseStart_6978506 baseEnd_6978506 := by
    simpa [prefixWord, tailWord_6978506, baseEnd_6978506] using wordTrace_append hprefix tailTrace_6978506
  have hstable : (prefixWord ++ tailWord_6978506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6978506).length < 2 ^ (prefixWord ++ tailWord_6978506).sum := by decide
  have hdescent : baseEnd_6978506 < baseStart_6978506 := by decide
  rcases family_descends (prefixWord ++ tailWord_6978506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6978517 : List Nat := [1, 3, 2, 3, 3, 1, 2, 2, 2, 2, 2]
def baseStart_6978517 : Nat := 118140960795 + 6978517 * 2 ^ 59
def prefixEnd_6978517 : Nat := 4983230072969 + 3 ^ 40 * 6978517 * 2
def baseEnd_6978517 : Nat := 3583333476572178253843891

theorem tailTrace_6978517 : CollatzResearch.WordTrace tailWord_6978517 prefixEnd_6978517 3583333476572178253843891 := by
  unfold tailWord_6978517
  simp only [CollatzResearch.WordTrace]
  refine ⟨254527425259032219661813805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169684950172688146441209203 254527425259032219661813805)
  ·
    refine ⟨95447784472137082373180177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 254527425259032219661813805 95447784472137082373180177)
    ·
      refine ⟨71585838354102811779885133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95447784472137082373180177 71585838354102811779885133)
      ·
        refine ⟨26844689382788554417456925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71585838354102811779885133 26844689382788554417456925)
        ·
          refine ⟨10066758518545707906546347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26844689382788554417456925 10066758518545707906546347)
          ·
            refine ⟨15100137777818561859819521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10066758518545707906546347 15100137777818561859819521)
            ·
              refine ⟨11325103333363921394864641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15100137777818561859819521 11325103333363921394864641)
              ·
                refine ⟨8493827500022941046148481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11325103333363921394864641 8493827500022941046148481)
                ·
                  refine ⟨6370370625017205784611361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8493827500022941046148481 6370370625017205784611361)
                  ·
                    refine ⟨4777777968762904338458521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6370370625017205784611361 4777777968762904338458521)
                    ·
                      refine ⟨3583333476572178253843891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4777777968762904338458521 3583333476572178253843891)
                      ·
                        rfl

theorem cell23_6978517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 2, 2, 2, 2, 2].length) (baseStart_6978517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6978517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6978517 prefixEnd_6978517 := by exact prefixLift 6978517
  have htrace : WordTrace (prefixWord ++ tailWord_6978517) baseStart_6978517 baseEnd_6978517 := by
    simpa [prefixWord, tailWord_6978517, baseEnd_6978517] using wordTrace_append hprefix tailTrace_6978517
  have hstable : (prefixWord ++ tailWord_6978517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6978517).length < 2 ^ (prefixWord ++ tailWord_6978517).sum := by decide
  have hdescent : baseEnd_6978517 < baseStart_6978517 := by decide
  rcases family_descends (prefixWord ++ tailWord_6978517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6978519 : List Nat := [1, 1, 3, 2, 1, 1, 2, 3, 4, 5]
def baseStart_6978519 : Nat := 118140960795 + 6978519 * 2 ^ 59
def prefixEnd_6978519 : Nat := 4983230072969 + 3 ^ 40 * 6978519 * 2
def baseEnd_6978519 : Nat := 1194444834511162415339627

theorem tailTrace_6978519 : CollatzResearch.WordTrace tailWord_6978519 prefixEnd_6978519 1194444834511162415339627 := by
  unfold tailWord_6978519
  simp only [CollatzResearch.WordTrace]
  refine ⟨254527498205024974003386611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169684998803349982668924407 254527498205024974003386611)
  ·
    refine ⟨381791247307537461005079917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254527498205024974003386611 381791247307537461005079917)
    ·
      refine ⟨143171717740326547876904969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 381791247307537461005079917 143171717740326547876904969)
      ·
        refine ⟨107378788305244910907678727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143171717740326547876904969 107378788305244910907678727)
        ·
          refine ⟨161068182457867366361518091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107378788305244910907678727 161068182457867366361518091)
          ·
            refine ⟨241602273686801049542277137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161068182457867366361518091 241602273686801049542277137)
            ·
              refine ⟨181201705265100787156707853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 241602273686801049542277137 181201705265100787156707853)
              ·
                refine ⟨67950639474412795183765445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 181201705265100787156707853 67950639474412795183765445)
                ·
                  refine ⟨12740744901452399096956021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67950639474412795183765445 12740744901452399096956021)
                  ·
                    refine ⟨1194444834511162415339627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12740744901452399096956021 1194444834511162415339627)
                    ·
                      rfl

theorem cell23_6978519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 3, 4, 5].length) (baseStart_6978519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6978519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6978519 prefixEnd_6978519 := by exact prefixLift 6978519
  have htrace : WordTrace (prefixWord ++ tailWord_6978519) baseStart_6978519 baseEnd_6978519 := by
    simpa [prefixWord, tailWord_6978519, baseEnd_6978519] using wordTrace_append hprefix tailTrace_6978519
  have hstable : (prefixWord ++ tailWord_6978519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6978519).length < 2 ^ (prefixWord ++ tailWord_6978519).sum := by decide
  have hdescent : baseEnd_6978519 < baseStart_6978519 := by decide
  rcases family_descends (prefixWord ++ tailWord_6978519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6978556 : List Nat := [2, 2, 2, 1, 2, 4, 1, 1, 1, 3, 4]
def baseStart_6978556 : Nat := 118140960795 + 6978556 * 2 ^ 59
def prefixEnd_6978556 : Nat := 4983230072969 + 3 ^ 40 * 6978556 * 2
def baseEnd_6978556 : Nat := 3583353502317703601256211

theorem tailTrace_6978556 : CollatzResearch.WordTrace tailWord_6978556 prefixEnd_6978556 3583353502317703601256211 := by
  unfold tailWord_6978556
  simp only [CollatzResearch.WordTrace]
  refine ⟨127264423852945464661241761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169685898470593952881655681 127264423852945464661241761)
  ·
    refine ⟨95448317889709098495931321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127264423852945464661241761 95448317889709098495931321)
    ·
      refine ⟨71586238417281823871948491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95448317889709098495931321 71586238417281823871948491)
      ·
        refine ⟨107379357625922735807922737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71586238417281823871948491 107379357625922735807922737)
        ·
          refine ⟨80534518219442051855942053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107379357625922735807922737 80534518219442051855942053)
          ·
            refine ⟨15100222166145384722989135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80534518219442051855942053 15100222166145384722989135)
            ·
              refine ⟨22650333249218077084483703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15100222166145384722989135 22650333249218077084483703)
              ·
                refine ⟨33975499873827115626725555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22650333249218077084483703 33975499873827115626725555)
                ·
                  refine ⟨50963249810740673440088333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33975499873827115626725555 50963249810740673440088333)
                  ·
                    refine ⟨19111218679027752540033125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50963249810740673440088333 19111218679027752540033125)
                    ·
                      refine ⟨3583353502317703601256211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19111218679027752540033125 3583353502317703601256211)
                      ·
                        rfl

theorem cell23_6978556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 1, 1, 3, 4].length) (baseStart_6978556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6978556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6978556 prefixEnd_6978556 := by exact prefixLift 6978556
  have htrace : WordTrace (prefixWord ++ tailWord_6978556) baseStart_6978556 baseEnd_6978556 := by
    simpa [prefixWord, tailWord_6978556, baseEnd_6978556] using wordTrace_append hprefix tailTrace_6978556
  have hstable : (prefixWord ++ tailWord_6978556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6978556).length < 2 ^ (prefixWord ++ tailWord_6978556).sum := by decide
  have hdescent : baseEnd_6978556 < baseStart_6978556 := by decide
  rcases family_descends (prefixWord ++ tailWord_6978556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6978569 : List Nat := [1, 2, 1, 1, 3, 1, 1, 2, 1, 6, 4]
def baseStart_6978569 : Nat := 118140960795 + 6978569 * 2 ^ 59
def prefixEnd_6978569 : Nat := 4983230072969 + 3 ^ 40 * 6978569 * 2
def baseEnd_6978569 : Nat := 3583360177566212050393651

theorem tailTrace_6978569 : CollatzResearch.WordTrace tailWord_6978569 prefixEnd_6978569 3583360177566212050393651 := by
  unfold tailWord_6978569
  simp only [CollatzResearch.WordTrace]
  refine ⟨254529321854843832542706761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169686214569895888361804507 254529321854843832542706761)
  ·
    refine ⟨190896991391132874407030071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254529321854843832542706761 190896991391132874407030071)
    ·
      refine ⟨286345487086699311610545107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190896991391132874407030071 286345487086699311610545107)
      ·
        refine ⟨429518230630048967415817661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286345487086699311610545107 429518230630048967415817661)
        ·
          refine ⟨161069336486268362780931623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 429518230630048967415817661 161069336486268362780931623)
          ·
            refine ⟨241604004729402544171397435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161069336486268362780931623 241604004729402544171397435)
            ·
              refine ⟨362406007094103816257096153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 241604004729402544171397435 362406007094103816257096153)
              ·
                refine ⟨271804505320577862192822115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 362406007094103816257096153 271804505320577862192822115)
                ·
                  refine ⟨407706757980866793289233173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 271804505320577862192822115 407706757980866793289233173)
                  ·
                    refine ⟨19111254280353130935432805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 407706757980866793289233173 19111254280353130935432805)
                    ·
                      refine ⟨3583360177566212050393651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19111254280353130935432805 3583360177566212050393651)
                      ·
                        rfl

theorem cell23_6978569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 6, 4].length) (baseStart_6978569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6978569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6978569 prefixEnd_6978569 := by exact prefixLift 6978569
  have htrace : WordTrace (prefixWord ++ tailWord_6978569) baseStart_6978569 baseEnd_6978569 := by
    simpa [prefixWord, tailWord_6978569, baseEnd_6978569] using wordTrace_append hprefix tailTrace_6978569
  have hstable : (prefixWord ++ tailWord_6978569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6978569).length < 2 ^ (prefixWord ++ tailWord_6978569).sum := by decide
  have hdescent : baseEnd_6978569 < baseStart_6978569 := by decide
  rcases family_descends (prefixWord ++ tailWord_6978569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6978583 : List Nat := [1, 1, 3, 5, 1, 1, 1, 3, 3, 4]
def baseStart_6978583 : Nat := 118140960795 + 6978583 * 2 ^ 59
def prefixEnd_6978583 : Nat := 4983230072969 + 3 ^ 40 * 6978583 * 2
def baseEnd_6978583 : Nat := 1194455788765124998539529

theorem tailTrace_6978583 : CollatzResearch.WordTrace tailWord_6978583 prefixEnd_6978583 1194455788765124998539529 := by
  unfold tailWord_6978583
  simp only [CollatzResearch.WordTrace]
  refine ⟨254529832476793112933716403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169686554984528741955810935 254529832476793112933716403)
  ·
    refine ⟨381794748715189669400574605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254529832476793112933716403 381794748715189669400574605)
    ·
      refine ⟨143173030768196126025215477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 381794748715189669400574605 143173030768196126025215477)
      ·
        refine ⟨13422471634518386814863951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 143173030768196126025215477 13422471634518386814863951)
        ·
          refine ⟨20133707451777580222295927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13422471634518386814863951 20133707451777580222295927)
          ·
            refine ⟨30200561177666370333443891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20133707451777580222295927 30200561177666370333443891)
            ·
              refine ⟨45300841766499555500165837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30200561177666370333443891 45300841766499555500165837)
              ·
                refine ⟨16987815662437333312562189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45300841766499555500165837 16987815662437333312562189)
                ·
                  refine ⟨6370430873413999992210821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16987815662437333312562189 6370430873413999992210821)
                  ·
                    refine ⟨1194455788765124998539529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6370430873413999992210821 1194455788765124998539529)
                    ·
                      rfl

theorem cell23_6978583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 3, 3, 4].length) (baseStart_6978583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6978583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6978583 prefixEnd_6978583 := by exact prefixLift 6978583
  have htrace : WordTrace (prefixWord ++ tailWord_6978583) baseStart_6978583 baseEnd_6978583 := by
    simpa [prefixWord, tailWord_6978583, baseEnd_6978583] using wordTrace_append hprefix tailTrace_6978583
  have hstable : (prefixWord ++ tailWord_6978583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6978583).length < 2 ^ (prefixWord ++ tailWord_6978583).sum := by decide
  have hdescent : baseEnd_6978583 < baseStart_6978583 := by decide
  rcases family_descends (prefixWord ++ tailWord_6978583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6978617 : List Nat := [1, 2, 1, 5, 2, 3, 1, 3, 1, 4]
def baseStart_6978617 : Nat := 118140960795 + 6978617 * 2 ^ 59
def prefixEnd_6978617 : Nat := 4983230072969 + 3 ^ 40 * 6978617 * 2
def baseEnd_6978617 : Nat := 1194461608212542620864477

theorem tailTrace_6978617 : CollatzResearch.WordTrace tailWord_6978617 prefixEnd_6978617 1194461608212542620864477 := by
  unfold tailWord_6978617
  simp only [CollatzResearch.WordTrace]
  refine ⟨254531072558669936740454105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169687381705779957826969403 254531072558669936740454105)
  ·
    refine ⟨190898304419002452555340579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254531072558669936740454105 190898304419002452555340579)
    ·
      refine ⟨286347456628503678833010869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190898304419002452555340579 286347456628503678833010869)
      ·
        refine ⟨26845074058922219890594769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 286347456628503678833010869 26845074058922219890594769)
        ·
          refine ⟨20133805544191664917946077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26845074058922219890594769 20133805544191664917946077)
          ·
            refine ⟨7550177079071874344229779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20133805544191664917946077 7550177079071874344229779)
            ·
              refine ⟨11325265618607811516344669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7550177079071874344229779 11325265618607811516344669)
              ·
                refine ⟨4246974606977929318629251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11325265618607811516344669 4246974606977929318629251)
                ·
                  refine ⟨6370461910466893977943877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4246974606977929318629251 6370461910466893977943877)
                  ·
                    refine ⟨1194461608212542620864477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6370461910466893977943877 1194461608212542620864477)
                    ·
                      rfl

theorem cell23_6978617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 1, 3, 1, 4].length) (baseStart_6978617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6978617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6978617 prefixEnd_6978617 := by exact prefixLift 6978617
  have htrace : WordTrace (prefixWord ++ tailWord_6978617) baseStart_6978617 baseEnd_6978617 := by
    simpa [prefixWord, tailWord_6978617, baseEnd_6978617] using wordTrace_append hprefix tailTrace_6978617
  have hstable : (prefixWord ++ tailWord_6978617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6978617).length < 2 ^ (prefixWord ++ tailWord_6978617).sum := by decide
  have hdescent : baseEnd_6978617 < baseStart_6978617 := by decide
  rcases family_descends (prefixWord ++ tailWord_6978617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6978619 : List Nat := [1, 1, 1, 1, 1, 2, 1, 3, 1, 6, 5]
def baseStart_6978619 : Nat := 118140960795 + 6978619 * 2 ^ 59
def prefixEnd_6978619 : Nat := 4983230072969 + 3 ^ 40 * 6978619 * 2
def baseEnd_6978619 : Nat := 3583385851598936854768421

theorem tailTrace_6978619 : CollatzResearch.WordTrace tailWord_6978619 prefixEnd_6978619 3583385851598936854768421 := by
  unfold tailWord_6978619
  simp only [CollatzResearch.WordTrace]
  refine ⟨254531145504662691082026911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169687430336441794054684607 254531145504662691082026911)
  ·
    refine ⟨381796718256994036623040367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254531145504662691082026911 381796718256994036623040367)
    ·
      refine ⟨572695077385491054934560551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 381796718256994036623040367 572695077385491054934560551)
      ·
        refine ⟨859042616078236582401840827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 572695077385491054934560551 859042616078236582401840827)
        ·
          refine ⟨1288563924117354873602761241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 859042616078236582401840827 1288563924117354873602761241)
          ·
            refine ⟨966422943088016155202070931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1288563924117354873602761241 966422943088016155202070931)
            ·
              refine ⟨1449634414632024232803106397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 966422943088016155202070931 1449634414632024232803106397)
              ·
                refine ⟨543612905487009087301164899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1449634414632024232803106397 543612905487009087301164899)
                ·
                  refine ⟨815419358230513630951747349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 543612905487009087301164899 815419358230513630951747349)
                  ·
                    refine ⟨38222782417055326450863157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 815419358230513630951747349 38222782417055326450863157)
                    ·
                      refine ⟨3583385851598936854768421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38222782417055326450863157 3583385851598936854768421)
                      ·
                        rfl

theorem cell23_6978619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 6, 5].length) (baseStart_6978619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6978619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6978619 prefixEnd_6978619 := by exact prefixLift 6978619
  have htrace : WordTrace (prefixWord ++ tailWord_6978619) baseStart_6978619 baseEnd_6978619 := by
    simpa [prefixWord, tailWord_6978619, baseEnd_6978619] using wordTrace_append hprefix tailTrace_6978619
  have hstable : (prefixWord ++ tailWord_6978619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6978619).length < 2 ^ (prefixWord ++ tailWord_6978619).sum := by decide
  have hdescent : baseEnd_6978619 < baseStart_6978619 := by decide
  rcases family_descends (prefixWord ++ tailWord_6978619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6978639 : List Nat := [1, 1, 2, 1, 1, 2, 2, 1, 2, 10]
def baseStart_6978639 : Nat := 118140960795 + 6978639 * 2 ^ 59
def prefixEnd_6978639 : Nat := 4983230072969 + 3 ^ 40 * 6978639 * 2
def baseEnd_6978639 : Nat := 1194465373737342258839443

theorem tailTrace_6978639 : CollatzResearch.WordTrace tailWord_6978639 prefixEnd_6978639 1194465373737342258839443 := by
  unfold tailWord_6978639
  simp only [CollatzResearch.WordTrace]
  refine ⟨254531874964590234497754971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169687916643060156331836647 254531874964590234497754971)
  ·
    refine ⟨381797812446885351746632457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254531874964590234497754971 381797812446885351746632457)
    ·
      refine ⟨286348359335164013809974343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 381797812446885351746632457 286348359335164013809974343)
      ·
        refine ⟨429522539002746020714961515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286348359335164013809974343 429522539002746020714961515)
        ·
          refine ⟨644283808504119031072442273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 429522539002746020714961515 644283808504119031072442273)
          ·
            refine ⟨483212856378089273304331705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 644283808504119031072442273 483212856378089273304331705)
            ·
              refine ⟨362409642283566954978248779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 483212856378089273304331705 362409642283566954978248779)
              ·
                refine ⟨543614463425350432467373169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 362409642283566954978248779 543614463425350432467373169)
                ·
                  refine ⟨407710847569012824350529877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 543614463425350432467373169 407710847569012824350529877)
                  ·
                    refine ⟨1194465373737342258839443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 407710847569012824350529877 1194465373737342258839443)
                    ·
                      rfl

theorem cell23_6978639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 10].length) (baseStart_6978639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6978639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6978639 prefixEnd_6978639 := by exact prefixLift 6978639
  have htrace : WordTrace (prefixWord ++ tailWord_6978639) baseStart_6978639 baseEnd_6978639 := by
    simpa [prefixWord, tailWord_6978639, baseEnd_6978639] using wordTrace_append hprefix tailTrace_6978639
  have hstable : (prefixWord ++ tailWord_6978639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6978639).length < 2 ^ (prefixWord ++ tailWord_6978639).sum := by decide
  have hdescent : baseEnd_6978639 < baseStart_6978639 := by decide
  rcases family_descends (prefixWord ++ tailWord_6978639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6978640 : List Nat := [2, 1, 1, 1, 1, 3, 1, 8, 1, 1, 3]
def baseStart_6978640 : Nat := 118140960795 + 6978640 * 2 ^ 59
def prefixEnd_6978640 : Nat := 4983230072969 + 3 ^ 40 * 6978640 * 2
def baseEnd_6978640 : Nat := 3583396634692681272605825

theorem tailTrace_6978640 : CollatzResearch.WordTrace tailWord_6978640 prefixEnd_6978640 3583396634692681272605825 := by
  unfold tailWord_6978640
  simp only [CollatzResearch.WordTrace]
  refine ⟨127265955718793305834270687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169687940958391074445694249 127265955718793305834270687)
  ·
    refine ⟨190898933578189958751406031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127265955718793305834270687 190898933578189958751406031)
    ·
      refine ⟨286348400367284938127109047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190898933578189958751406031 286348400367284938127109047)
      ·
        refine ⟨429522600550927407190663571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286348400367284938127109047 429522600550927407190663571)
        ·
          refine ⟨644283900826391110785995357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 429522600550927407190663571 644283900826391110785995357)
          ·
            refine ⟨241606462809896666544748259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 644283900826391110785995357 241606462809896666544748259)
            ·
              refine ⟨362409694214844999817122389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 241606462809896666544748259 362409694214844999817122389)
              ·
                refine ⟨4246988604080214841606903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 362409694214844999817122389 4246988604080214841606903)
                ·
                  refine ⟨6370482906120322262410355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4246988604080214841606903 6370482906120322262410355)
                  ·
                    refine ⟨9555724359180483393615533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6370482906120322262410355 9555724359180483393615533)
                    ·
                      refine ⟨3583396634692681272605825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9555724359180483393615533 3583396634692681272605825)
                      ·
                        rfl

theorem cell23_6978640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 8, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 8, 1, 1, 3].length) (baseStart_6978640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6978640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6978640 prefixEnd_6978640 := by exact prefixLift 6978640
  have htrace : WordTrace (prefixWord ++ tailWord_6978640) baseStart_6978640 baseEnd_6978640 := by
    simpa [prefixWord, tailWord_6978640, baseEnd_6978640] using wordTrace_append hprefix tailTrace_6978640
  have hstable : (prefixWord ++ tailWord_6978640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6978640).length < 2 ^ (prefixWord ++ tailWord_6978640).sum := by decide
  have hdescent : baseEnd_6978640 < baseStart_6978640 := by decide
  rcases family_descends (prefixWord ++ tailWord_6978640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6978656 : List Nat := [2, 1, 1, 3, 2, 2, 2, 3, 1, 6]
def baseStart_6978656 : Nat := 118140960795 + 6978656 * 2 ^ 59
def prefixEnd_6978656 : Nat := 4983230072969 + 3 ^ 40 * 6978656 * 2
def baseEnd_6978656 : Nat := 1194468283461051070001917

theorem tailTrace_6978656 : CollatzResearch.WordTrace tailWord_6978656 prefixEnd_6978656 1194468283461051070001917 := by
  unfold tailWord_6978656
  simp only [CollatzResearch.WordTrace]
  refine ⟨127266247502764323200561911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169688330003685764267415881 127266247502764323200561911)
  ·
    refine ⟨190899371254146484800842867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127266247502764323200561911 190899371254146484800842867)
    ·
      refine ⟨286349056881219727201264301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190899371254146484800842867 286349056881219727201264301)
      ·
        refine ⟨107380896330457397700474113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 286349056881219727201264301 107380896330457397700474113)
        ·
          refine ⟨80535672247843048275355585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107380896330457397700474113 80535672247843048275355585)
          ·
            refine ⟨60401754185882286206516689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80535672247843048275355585 60401754185882286206516689)
            ·
              refine ⟨45301315639411714654887517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60401754185882286206516689 45301315639411714654887517)
              ·
                refine ⟨16987993364779392995582819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45301315639411714654887517 16987993364779392995582819)
                ·
                  refine ⟨25481990047169089493374229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16987993364779392995582819 25481990047169089493374229)
                  ·
                    refine ⟨1194468283461051070001917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25481990047169089493374229 1194468283461051070001917)
                    ·
                      rfl

theorem cell23_6978656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 3, 1, 6].length) (baseStart_6978656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6978656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6978656 prefixEnd_6978656 := by exact prefixLift 6978656
  have htrace : WordTrace (prefixWord ++ tailWord_6978656) baseStart_6978656 baseEnd_6978656 := by
    simpa [prefixWord, tailWord_6978656, baseEnd_6978656] using wordTrace_append hprefix tailTrace_6978656
  have hstable : (prefixWord ++ tailWord_6978656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6978656).length < 2 ^ (prefixWord ++ tailWord_6978656).sum := by decide
  have hdescent : baseEnd_6978656 < baseStart_6978656 := by decide
  rcases family_descends (prefixWord ++ tailWord_6978656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6978663 : List Nat := [1, 1, 5, 1, 1, 4, 1, 1, 3, 1, 4]
def baseStart_6978663 : Nat := 118140960795 + 6978663 * 2 ^ 59
def prefixEnd_6978663 : Nat := 4983230072969 + 3 ^ 40 * 6978663 * 2
def baseEnd_6978663 : Nat := 3583408444747734682618219

theorem tailTrace_6978663 : CollatzResearch.WordTrace tailWord_6978663 prefixEnd_6978663 3583408444747734682618219 := by
  unfold tailWord_6978663
  simp only [CollatzResearch.WordTrace]
  refine ⟨254532750316503286596628643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169688500211002191064419095 254532750316503286596628643)
  ·
    refine ⟨381799125474754929894942965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254532750316503286596628643 381799125474754929894942965)
    ·
      refine ⟨35793668013258274677650903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 381799125474754929894942965 35793668013258274677650903)
      ·
        refine ⟨53690502019887412016476355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35793668013258274677650903 53690502019887412016476355)
        ·
          refine ⟨80535753029831118024714533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53690502019887412016476355 80535753029831118024714533)
          ·
            refine ⟨15100453693093334629633975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80535753029831118024714533 15100453693093334629633975)
            ·
              refine ⟨22650680539640001944450963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15100453693093334629633975 22650680539640001944450963)
              ·
                refine ⟨33976020809460002916676445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22650680539640001944450963 33976020809460002916676445)
                ·
                  refine ⟨12741007803547501093753667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33976020809460002916676445 12741007803547501093753667)
                  ·
                    refine ⟨19111511705321251640630501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12741007803547501093753667 19111511705321251640630501)
                    ·
                      refine ⟨3583408444747734682618219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19111511705321251640630501 3583408444747734682618219)
                      ·
                        rfl

theorem cell23_6978663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 1, 3, 1, 4].length) (baseStart_6978663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6978663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6978663 prefixEnd_6978663 := by exact prefixLift 6978663
  have htrace : WordTrace (prefixWord ++ tailWord_6978663) baseStart_6978663 baseEnd_6978663 := by
    simpa [prefixWord, tailWord_6978663, baseEnd_6978663] using wordTrace_append hprefix tailTrace_6978663
  have hstable : (prefixWord ++ tailWord_6978663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6978663).length < 2 ^ (prefixWord ++ tailWord_6978663).sum := by decide
  have hdescent : baseEnd_6978663 < baseStart_6978663 := by decide
  rcases family_descends (prefixWord ++ tailWord_6978663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6978683 : List Nat := [1, 1, 1, 1, 1, 4, 1, 7, 1, 2, 3]
def baseStart_6978683 : Nat := 118140960795 + 6978683 * 2 ^ 59
def prefixEnd_6978683 : Nat := 4983230072969 + 3 ^ 40 * 6978683 * 2
def baseEnd_6978683 : Nat := 3583418714360824604368127

theorem tailTrace_6978683 : CollatzResearch.WordTrace tailWord_6978683 prefixEnd_6978683 3583418714360824604368127 := by
  unfold tailWord_6978683
  simp only [CollatzResearch.WordTrace]
  refine ⟨254533479776430830012356703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169688986517620553341571135 254533479776430830012356703)
  ·
    refine ⟨381800219664646245018535055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254533479776430830012356703 381800219664646245018535055)
    ·
      refine ⟨572700329496969367527802583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 381800219664646245018535055 572700329496969367527802583)
      ·
        refine ⟨859050494245454051291703875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 572700329496969367527802583 859050494245454051291703875)
        ·
          refine ⟨1288575741368181076937555813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 859050494245454051291703875 1288575741368181076937555813)
          ·
            refine ⟨241607951506533951925791715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1288575741368181076937555813 241607951506533951925791715)
            ·
              refine ⟨362411927259800927888687573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 241607951506533951925791715 362411927259800927888687573)
              ·
                refine ⟨8494029545151584247391115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 362411927259800927888687573 8494029545151584247391115)
                ·
                  refine ⟨12741044317727376371086673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8494029545151584247391115 12741044317727376371086673)
                  ·
                    refine ⟨9555783238295532278315005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12741044317727376371086673 9555783238295532278315005)
                    ·
                      refine ⟨3583418714360824604368127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9555783238295532278315005 3583418714360824604368127)
                      ·
                        rfl

theorem cell23_6978683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 7, 1, 2, 3].length) (baseStart_6978683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6978683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6978683 prefixEnd_6978683 := by exact prefixLift 6978683
  have htrace : WordTrace (prefixWord ++ tailWord_6978683) baseStart_6978683 baseEnd_6978683 := by
    simpa [prefixWord, tailWord_6978683, baseEnd_6978683] using wordTrace_append hprefix tailTrace_6978683
  have hstable : (prefixWord ++ tailWord_6978683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6978683).length < 2 ^ (prefixWord ++ tailWord_6978683).sum := by decide
  have hdescent : baseEnd_6978683 < baseStart_6978683 := by decide
  rcases family_descends (prefixWord ++ tailWord_6978683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6978713 : List Nat := [1, 2, 1, 2, 1, 2, 1, 1, 8, 1, 3]
def baseStart_6978713 : Nat := 118140960795 + 6978713 * 2 ^ 59
def prefixEnd_6978713 : Nat := 4983230072969 + 3 ^ 40 * 6978713 * 2
def baseEnd_6978713 : Nat := 3583434118780459486992989

theorem tailTrace_6978713 : CollatzResearch.WordTrace tailWord_6978713 prefixEnd_6978713 3583434118780459486992989 := by
  unfold tailWord_6978713
  simp only [CollatzResearch.WordTrace]
  refine ⟨254534573966322145135948793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169689715977548096757299195 254534573966322145135948793)
  ·
    refine ⟨190900930474741608851961595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254534573966322145135948793 190900930474741608851961595)
    ·
      refine ⟨286351395712112413277942393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190900930474741608851961595 286351395712112413277942393)
      ·
        refine ⟨214763546784084309958456795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 286351395712112413277942393 214763546784084309958456795)
        ·
          refine ⟨322145320176126464937685193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214763546784084309958456795 322145320176126464937685193)
          ·
            refine ⟨241608990132094848703263895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 322145320176126464937685193 241608990132094848703263895)
            ·
              refine ⟨362413485198142273054895843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 241608990132094848703263895 362413485198142273054895843)
              ·
                refine ⟨543620227797213409582343765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 362413485198142273054895843 543620227797213409582343765)
                ·
                  refine ⟨6370549544498594643543091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 543620227797213409582343765 6370549544498594643543091)
                  ·
                    refine ⟨9555824316747891965314637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6370549544498594643543091 9555824316747891965314637)
                    ·
                      refine ⟨3583434118780459486992989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9555824316747891965314637 3583434118780459486992989)
                      ·
                        rfl

theorem cell23_6978713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 8, 1, 3].length) (baseStart_6978713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6978713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6978713 prefixEnd_6978713 := by exact prefixLift 6978713
  have htrace : WordTrace (prefixWord ++ tailWord_6978713) baseStart_6978713 baseEnd_6978713 := by
    simpa [prefixWord, tailWord_6978713, baseEnd_6978713] using wordTrace_append hprefix tailTrace_6978713
  have hstable : (prefixWord ++ tailWord_6978713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6978713).length < 2 ^ (prefixWord ++ tailWord_6978713).sum := by decide
  have hdescent : baseEnd_6978713 < baseStart_6978713 := by decide
  rcases family_descends (prefixWord ++ tailWord_6978713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6978736 : List Nat := [2, 1, 1, 1, 2, 1, 2, 2, 4, 3, 4]
def baseStart_6978736 : Nat := 118140960795 + 6978736 * 2 ^ 59
def prefixEnd_6978736 : Nat := 4983230072969 + 3 ^ 40 * 6978736 * 2
def baseEnd_6978736 : Nat := 3583445928835512897005383

theorem tailTrace_6978736 : CollatzResearch.WordTrace tailWord_6978736 prefixEnd_6978736 3583445928835512897005383 := by
  unfold tailWord_6978736
  simp only [CollatzResearch.WordTrace]
  refine ⟨127267706422619410032018031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169690275230159213376024041 127267706422619410032018031)
  ·
    refine ⟨190901559633929115048027047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127267706422619410032018031 190901559633929115048027047)
    ·
      refine ⟨286352339450893672572040571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190901559633929115048027047 286352339450893672572040571)
      ·
        refine ⟨429528509176340508858060857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286352339450893672572040571 429528509176340508858060857)
        ·
          refine ⟨322146381882255381643545643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 429528509176340508858060857 322146381882255381643545643)
          ·
            refine ⟨483219572823383072465318465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 322146381882255381643545643 483219572823383072465318465)
            ·
              refine ⟨362414679617537304348988849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 483219572823383072465318465 362414679617537304348988849)
              ·
                refine ⟨271811009713152978261741637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 362414679617537304348988849 271811009713152978261741637)
                ·
                  refine ⟨50964564321216183424076557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 271811009713152978261741637 50964564321216183424076557)
                  ·
                    refine ⟨19111711620456068784028709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50964564321216183424076557 19111711620456068784028709)
                    ·
                      refine ⟨3583445928835512897005383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19111711620456068784028709 3583445928835512897005383)
                      ·
                        rfl

theorem cell23_6978736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 4, 3, 4].length) (baseStart_6978736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6978736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6978736 prefixEnd_6978736 := by exact prefixLift 6978736
  have htrace : WordTrace (prefixWord ++ tailWord_6978736) baseStart_6978736 baseEnd_6978736 := by
    simpa [prefixWord, tailWord_6978736, baseEnd_6978736] using wordTrace_append hprefix tailTrace_6978736
  have hstable : (prefixWord ++ tailWord_6978736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6978736).length < 2 ^ (prefixWord ++ tailWord_6978736).sum := by decide
  have hdescent : baseEnd_6978736 < baseStart_6978736 := by decide
  rcases family_descends (prefixWord ++ tailWord_6978736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6978758 : List Nat := [6, 1, 2, 2, 1, 1, 3, 1, 2, 4]
def baseStart_6978758 : Nat := 118140960795 + 6978758 * 2 ^ 59
def prefixEnd_6978758 : Nat := 4983230072969 + 3 ^ 40 * 6978758 * 2
def baseEnd_6978758 : Nat := 1194485741803303936976761

theorem tailTrace_6978758 : CollatzResearch.WordTrace tailWord_6978758 prefixEnd_6978758 1194485741803303936976761 := by
  unfold tailWord_6978758
  simp only [CollatzResearch.WordTrace]
  refine ⟨7954256726598722431916779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 169690810167439411880891285 7954256726598722431916779)
  ·
    refine ⟨11931385089898083647875169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7954256726598722431916779 11931385089898083647875169)
    ·
      refine ⟨8948538817423562735906377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11931385089898083647875169 8948538817423562735906377)
      ·
        refine ⟨6711404113067672051929783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8948538817423562735906377 6711404113067672051929783)
        ·
          refine ⟨10067106169601508077894675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6711404113067672051929783 10067106169601508077894675)
          ·
            refine ⟨15100659254402262116842013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10067106169601508077894675 15100659254402262116842013)
            ·
              refine ⟨5662747220400848293815755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15100659254402262116842013 5662747220400848293815755)
              ·
                refine ⟨8494120830601272440723633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5662747220400848293815755 8494120830601272440723633)
                ·
                  refine ⟨6370590622950954330542725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8494120830601272440723633 6370590622950954330542725)
                  ·
                    refine ⟨1194485741803303936976761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6370590622950954330542725 1194485741803303936976761)
                    ·
                      rfl

theorem cell23_6978758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_6978758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6978758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6978758 prefixEnd_6978758 := by exact prefixLift 6978758
  have htrace : WordTrace (prefixWord ++ tailWord_6978758) baseStart_6978758 baseEnd_6978758 := by
    simpa [prefixWord, tailWord_6978758, baseEnd_6978758] using wordTrace_append hprefix tailTrace_6978758
  have hstable : (prefixWord ++ tailWord_6978758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6978758).length < 2 ^ (prefixWord ++ tailWord_6978758).sum := by decide
  have hdescent : baseEnd_6978758 < baseStart_6978758 := by decide
  rcases family_descends (prefixWord ++ tailWord_6978758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6978840 : List Nat := [2, 1, 2, 3, 1, 4, 2, 1, 2, 5]
def baseStart_6978840 : Nat := 118140960795 + 6978840 * 2 ^ 59
def prefixEnd_6978840 : Nat := 4983230072969 + 3 ^ 40 * 6978840 * 2
def baseEnd_6978840 : Nat := 1194499776941193496701635

theorem tailTrace_6978840 : CollatzResearch.WordTrace tailWord_6978840 prefixEnd_6978840 1194499776941193496701635 := by
  unfold tailWord_6978840
  simp only [CollatzResearch.WordTrace]
  refine ⟨127269603018431022912910987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169692804024574697217214649 127269603018431022912910987)
  ·
    refine ⟨190904404527646534369366481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127269603018431022912910987 190904404527646534369366481)
    ·
      refine ⟨143178303395734900777024861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190904404527646534369366481 143178303395734900777024861)
      ·
        refine ⟨53691863773400587791384323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143178303395734900777024861 53691863773400587791384323)
        ·
          refine ⟨80537795660100881687076485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53691863773400587791384323 80537795660100881687076485)
          ·
            refine ⟨15100836686268915316326841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80537795660100881687076485 15100836686268915316326841)
            ·
              refine ⟨11325627514701686487245131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15100836686268915316326841 11325627514701686487245131)
              ·
                refine ⟨16988441272052529730867697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11325627514701686487245131 16988441272052529730867697)
                ·
                  refine ⟨12741330954039397298150773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16988441272052529730867697 12741330954039397298150773)
                  ·
                    refine ⟨1194499776941193496701635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12741330954039397298150773 1194499776941193496701635)
                    ·
                      rfl

theorem cell23_6978840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 2, 1, 2, 5].length) (baseStart_6978840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6978840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6978840 prefixEnd_6978840 := by exact prefixLift 6978840
  have htrace : WordTrace (prefixWord ++ tailWord_6978840) baseStart_6978840 baseEnd_6978840 := by
    simpa [prefixWord, tailWord_6978840, baseEnd_6978840] using wordTrace_append hprefix tailTrace_6978840
  have hstable : (prefixWord ++ tailWord_6978840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6978840).length < 2 ^ (prefixWord ++ tailWord_6978840).sum := by decide
  have hdescent : baseEnd_6978840 < baseStart_6978840 := by decide
  rcases family_descends (prefixWord ++ tailWord_6978840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6978860 : List Nat := [2, 2, 1, 1, 1, 3, 1, 4, 2, 4, 2]
def baseStart_6978860 : Nat := 118140960795 + 6978860 * 2 ^ 59
def prefixEnd_6978860 : Nat := 4983230072969 + 3 ^ 40 * 6978860 * 2
def baseEnd_6978860 : Nat := 3583509600436670411854813

theorem tailTrace_6978860 : CollatzResearch.WordTrace tailWord_6978860 prefixEnd_6978860 3583509600436670411854813 := by
  unfold tailWord_6978860
  simp only [CollatzResearch.WordTrace]
  refine ⟨127269967748394794620775017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169693290331193059494366689 127269967748394794620775017)
  ·
    refine ⟨95452475811296095965581263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127269967748394794620775017 95452475811296095965581263)
    ·
      refine ⟨143178713716944143948371895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95452475811296095965581263 143178713716944143948371895)
      ·
        refine ⟨214768070575416215922557843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143178713716944143948371895 214768070575416215922557843)
        ·
          refine ⟨322152105863124323883836765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214768070575416215922557843 322152105863124323883836765)
          ·
            refine ⟨120807039698671621456438787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 322152105863124323883836765 120807039698671621456438787)
            ·
              refine ⟨181210559548007432184658181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120807039698671621456438787 181210559548007432184658181)
              ·
                refine ⟨33976979915251393534623409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 181210559548007432184658181 33976979915251393534623409)
                ·
                  refine ⟨25482734936438545150967557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33976979915251393534623409 25482734936438545150967557)
                  ·
                    refine ⟨4778012800582227215806417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25482734936438545150967557 4778012800582227215806417)
                    ·
                      refine ⟨3583509600436670411854813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4778012800582227215806417 3583509600436670411854813)
                      ·
                        rfl

theorem cell23_6978860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 4, 2].length) (baseStart_6978860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6978860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6978860 prefixEnd_6978860 := by exact prefixLift 6978860
  have htrace : WordTrace (prefixWord ++ tailWord_6978860) baseStart_6978860 baseEnd_6978860 := by
    simpa [prefixWord, tailWord_6978860, baseEnd_6978860] using wordTrace_append hprefix tailTrace_6978860
  have hstable : (prefixWord ++ tailWord_6978860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6978860).length < 2 ^ (prefixWord ++ tailWord_6978860).sum := by decide
  have hdescent : baseEnd_6978860 < baseStart_6978860 := by decide
  rcases family_descends (prefixWord ++ tailWord_6978860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6978861 : List Nat := [1, 5, 3, 1, 1, 3, 2, 2, 5]
def baseStart_6978861 : Nat := 118140960795 + 6978861 * 2 ^ 59
def prefixEnd_6978861 : Nat := 4983230072969 + 3 ^ 40 * 6978861 * 2
def baseEnd_6978861 : Nat := 398167790435258323104701

theorem tailTrace_6978861 : CollatzResearch.WordTrace tailWord_6978861 prefixEnd_6978861 398167790435258323104701 := by
  unfold tailWord_6978861
  simp only [CollatzResearch.WordTrace]
  refine ⟨254539971969785966412336437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169693314646523977608224291 254539971969785966412336437)
  ·
    refine ⟨23863122372167434351156541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 254539971969785966412336437 23863122372167434351156541)
    ·
      refine ⟨8948670889562787881683703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23863122372167434351156541 8948670889562787881683703)
      ·
        refine ⟨13423006334344181822525555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8948670889562787881683703 13423006334344181822525555)
        ·
          refine ⟨20134509501516272733788333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13423006334344181822525555 20134509501516272733788333)
          ·
            refine ⟨7550441063068602275170625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20134509501516272733788333 7550441063068602275170625)
            ·
              refine ⟨5662830797301451706377969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7550441063068602275170625 5662830797301451706377969)
              ·
                refine ⟨4247123097976088779783477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5662830797301451706377969 4247123097976088779783477)
                ·
                  refine ⟨398167790435258323104701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4247123097976088779783477 398167790435258323104701)
                  ·
                    rfl

theorem cell23_6978861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 2, 2, 5].length) (baseStart_6978861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6978861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6978861 prefixEnd_6978861 := by exact prefixLift 6978861
  have htrace : WordTrace (prefixWord ++ tailWord_6978861) baseStart_6978861 baseEnd_6978861 := by
    simpa [prefixWord, tailWord_6978861, baseEnd_6978861] using wordTrace_append hprefix tailTrace_6978861
  have hstable : (prefixWord ++ tailWord_6978861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6978861).length < 2 ^ (prefixWord ++ tailWord_6978861).sum := by decide
  have hdescent : baseEnd_6978861 < baseStart_6978861 := by decide
  rcases family_descends (prefixWord ++ tailWord_6978861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6978863 : List Nat := [1, 1, 2, 1, 2, 1, 3, 2, 3, 4, 3]
def baseStart_6978863 : Nat := 118140960795 + 6978863 * 2 ^ 59
def prefixEnd_6978863 : Nat := 4983230072969 + 3 ^ 40 * 6978863 * 2
def baseEnd_6978863 : Nat := 3583511140878633900117299

theorem tailTrace_6978863 : CollatzResearch.WordTrace tailWord_6978863 prefixEnd_6978863 3583511140878633900117299 := by
  unfold tailWord_6978863
  simp only [CollatzResearch.WordTrace]
  refine ⟨254540044915778720753909243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169693363277185813835939495 254540044915778720753909243)
  ·
    refine ⟨381810067373668081130863865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254540044915778720753909243 381810067373668081130863865)
    ·
      refine ⟨286357550530251060848147899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 381810067373668081130863865 286357550530251060848147899)
      ·
        refine ⟨429536325795376591272221849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286357550530251060848147899 429536325795376591272221849)
        ·
          refine ⟨322152244346532443454166387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 429536325795376591272221849 322152244346532443454166387)
          ·
            refine ⟨483228366519798665181249581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 322152244346532443454166387 483228366519798665181249581)
            ·
              refine ⟨181210637444924499442968593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 483228366519798665181249581 181210637444924499442968593)
              ·
                refine ⟨135907978083693374582226445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 181210637444924499442968593 135907978083693374582226445)
                ·
                  refine ⟨50965491781385015468334917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 135907978083693374582226445 50965491781385015468334917)
                  ·
                    refine ⟨9556029709009690400312797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50965491781385015468334917 9556029709009690400312797)
                    ·
                      refine ⟨3583511140878633900117299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9556029709009690400312797 3583511140878633900117299)
                      ·
                        rfl

theorem cell23_6978863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 2, 3, 4, 3].length) (baseStart_6978863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6978863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6978863 prefixEnd_6978863 := by exact prefixLift 6978863
  have htrace : WordTrace (prefixWord ++ tailWord_6978863) baseStart_6978863 baseEnd_6978863 := by
    simpa [prefixWord, tailWord_6978863, baseEnd_6978863] using wordTrace_append hprefix tailTrace_6978863
  have hstable : (prefixWord ++ tailWord_6978863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6978863).length < 2 ^ (prefixWord ++ tailWord_6978863).sum := by decide
  have hdescent : baseEnd_6978863 < baseStart_6978863 := by decide
  rcases family_descends (prefixWord ++ tailWord_6978863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6978927 : List Nat := [1, 1, 2, 1, 3, 1, 6, 1, 3, 1, 3]
def baseStart_6978927 : Nat := 118140960795 + 6978927 * 2 ^ 59
def prefixEnd_6978927 : Nat := 4983230072969 + 3 ^ 40 * 6978927 * 2
def baseEnd_6978927 : Nat := 3583544003640521649717005

theorem tailTrace_6978927 : CollatzResearch.WordTrace tailWord_6978927 prefixEnd_6978927 3583544003640521649717005 := by
  unfold tailWord_6978927
  simp only [CollatzResearch.WordTrace]
  refine ⟨254542379187546859684239035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169694919458364573122826023 254542379187546859684239035)
  ·
    refine ⟨381813568781320289526358553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254542379187546859684239035 381813568781320289526358553)
    ·
      refine ⟨286360176585990217144768915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 381813568781320289526358553 286360176585990217144768915)
      ·
        refine ⟨429540264878985325717153373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286360176585990217144768915 429540264878985325717153373)
        ·
          refine ⟨161077599329619497143932515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 429540264878985325717153373 161077599329619497143932515)
          ·
            refine ⟨241616398994429245715898773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161077599329619497143932515 241616398994429245715898773)
            ·
              refine ⟨11325768702863870892932755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 241616398994429245715898773 11325768702863870892932755)
              ·
                refine ⟨16988653054295806339399133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11325768702863870892932755 16988653054295806339399133)
                ·
                  refine ⟨6370744895360927377274675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16988653054295806339399133 6370744895360927377274675)
                  ·
                    refine ⟨9556117343041391065912013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6370744895360927377274675 9556117343041391065912013)
                    ·
                      refine ⟨3583544003640521649717005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9556117343041391065912013 3583544003640521649717005)
                      ·
                        rfl

theorem cell23_6978927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 6, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 6, 1, 3, 1, 3].length) (baseStart_6978927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6978927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6978927 prefixEnd_6978927 := by exact prefixLift 6978927
  have htrace : WordTrace (prefixWord ++ tailWord_6978927) baseStart_6978927 baseEnd_6978927 := by
    simpa [prefixWord, tailWord_6978927, baseEnd_6978927] using wordTrace_append hprefix tailTrace_6978927
  have hstable : (prefixWord ++ tailWord_6978927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6978927).length < 2 ^ (prefixWord ++ tailWord_6978927).sum := by decide
  have hdescent : baseEnd_6978927 < baseStart_6978927 := by decide
  rcases family_descends (prefixWord ++ tailWord_6978927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6978947 : List Nat := [1, 1, 1, 3, 5, 2, 2, 2, 1, 5]
def baseStart_6978947 : Nat := 118140960795 + 6978947 * 2 ^ 59
def prefixEnd_6978947 : Nat := 4983230072969 + 3 ^ 40 * 6978947 * 2
def baseEnd_6978947 : Nat := 1194518091084537190488971

theorem tailTrace_6978947 : CollatzResearch.WordTrace tailWord_6978947 prefixEnd_6978947 1194518091084537190488971 := by
  unfold tailWord_6978947
  simp only [CollatzResearch.WordTrace]
  refine ⟨254543108647474403099967095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169695405764982935399978063 254543108647474403099967095)
  ·
    refine ⟨381814662971211604649950643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254543108647474403099967095 381814662971211604649950643)
    ·
      refine ⟨572721994456817406974925965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 381814662971211604649950643 572721994456817406974925965)
      ·
        refine ⟨214770747921306527615597237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 572721994456817406974925965 214770747921306527615597237)
        ·
          refine ⟨20134757617622486963962241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 214770747921306527615597237 20134757617622486963962241)
          ·
            refine ⟨15101068213216865222971681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20134757617622486963962241 15101068213216865222971681)
            ·
              refine ⟨11325801159912648917228761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15101068213216865222971681 11325801159912648917228761)
              ·
                refine ⟨8494350869934486687921571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11325801159912648917228761 8494350869934486687921571)
                ·
                  refine ⟨12741526304901730031882357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8494350869934486687921571 12741526304901730031882357)
                  ·
                    refine ⟨1194518091084537190488971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12741526304901730031882357 1194518091084537190488971)
                    ·
                      rfl

theorem cell23_6978947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 2, 2, 1, 5].length) (baseStart_6978947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6978947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6978947 prefixEnd_6978947 := by exact prefixLift 6978947
  have htrace : WordTrace (prefixWord ++ tailWord_6978947) baseStart_6978947 baseEnd_6978947 := by
    simpa [prefixWord, tailWord_6978947, baseEnd_6978947] using wordTrace_append hprefix tailTrace_6978947
  have hstable : (prefixWord ++ tailWord_6978947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6978947).length < 2 ^ (prefixWord ++ tailWord_6978947).sum := by decide
  have hdescent : baseEnd_6978947 < baseStart_6978947 := by decide
  rcases family_descends (prefixWord ++ tailWord_6978947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
