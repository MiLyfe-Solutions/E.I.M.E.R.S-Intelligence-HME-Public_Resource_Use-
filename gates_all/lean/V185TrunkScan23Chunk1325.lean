import V185TrunkScan23Chunk1324

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7847937 : List Nat := [1, 2, 4, 1, 2, 1, 3, 4, 1, 1, 3]
def baseStart_7847937 : Nat := 118140960795 + 7847937 * 2 ^ 59
def prefixEnd_7847937 : Nat := 4983230072969 + 3 ^ 40 * 7847937 * 2
def baseEnd_7847937 : Nat := 4029763827204166644095501

theorem tailTrace_7847937 : CollatzResearch.WordTrace tailWord_7847937 prefixEnd_7847937 4029763827204166644095501 := by
  unfold tailWord_7847937
  simp only [CollatzResearch.WordTrace]
  refine ⟨286237777769272044776310065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190825185179514696517540043 286237777769272044776310065)
  ·
    refine ⟨214678333326954033582232549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286237777769272044776310065 214678333326954033582232549)
    ·
      refine ⟨40252187498803881296668603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 214678333326954033582232549 40252187498803881296668603)
      ·
        refine ⟨60378281248205821945002905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40252187498803881296668603 60378281248205821945002905)
        ·
          refine ⟨45283710936154366458752179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60378281248205821945002905 45283710936154366458752179)
          ·
            refine ⟨67925566404231549688128269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45283710936154366458752179 67925566404231549688128269)
            ·
              refine ⟨25472087401586831133048101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67925566404231549688128269 25472087401586831133048101)
              ·
                refine ⟨4776016387797530837446519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25472087401586831133048101 4776016387797530837446519)
                ·
                  refine ⟨7164024581696296256169779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4776016387797530837446519 7164024581696296256169779)
                  ·
                    refine ⟨10746036872544444384254669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7164024581696296256169779 10746036872544444384254669)
                    ·
                      refine ⟨4029763827204166644095501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10746036872544444384254669 4029763827204166644095501)
                      ·
                        rfl

theorem cell23_7847937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 4, 1, 1, 3].length) (baseStart_7847937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7847937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7847937 prefixEnd_7847937 := by exact prefixLift 7847937
  have htrace : WordTrace (prefixWord ++ tailWord_7847937) baseStart_7847937 baseEnd_7847937 := by
    simpa [prefixWord, tailWord_7847937, baseEnd_7847937] using wordTrace_append hprefix tailTrace_7847937
  have hstable : (prefixWord ++ tailWord_7847937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7847937).length < 2 ^ (prefixWord ++ tailWord_7847937).sum := by decide
  have hdescent : baseEnd_7847937 < baseStart_7847937 := by decide
  rcases family_descends (prefixWord ++ tailWord_7847937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7847943 : List Nat := [1, 1, 4, 3, 1, 2, 1, 2, 3, 1, 4]
def baseStart_7847943 : Nat := 118140960795 + 7847943 * 2 ^ 59
def prefixEnd_7847943 : Nat := 4983230072969 + 3 ^ 40 * 7847943 * 2
def baseEnd_7847943 : Nat := 4029766908088093620620473

theorem tailTrace_7847943 : CollatzResearch.WordTrace tailWord_7847943 prefixEnd_7847943 4029766908088093620620473 := by
  unfold tailWord_7847943
  simp only [CollatzResearch.WordTrace]
  refine ⟨286237996607250307801028483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190825331071500205200685655 286237996607250307801028483)
  ·
    refine ⟨429356994910875461701542725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286237996607250307801028483 429356994910875461701542725)
    ·
      refine ⟨80504436545789149069039261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 429356994910875461701542725 80504436545789149069039261)
      ·
        refine ⟨30189163704670930900889723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80504436545789149069039261 30189163704670930900889723)
        ·
          refine ⟨45283745557006396351334585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30189163704670930900889723 45283745557006396351334585)
          ·
            refine ⟨33962809167754797263500939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45283745557006396351334585 33962809167754797263500939)
            ·
              refine ⟨50944213751632195895251409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33962809167754797263500939 50944213751632195895251409)
              ·
                refine ⟨38208160313724146921438557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50944213751632195895251409 38208160313724146921438557)
                ·
                  refine ⟨14328060117646555095539459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38208160313724146921438557 14328060117646555095539459)
                  ·
                    refine ⟨21492090176469832643309189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14328060117646555095539459 21492090176469832643309189)
                    ·
                      refine ⟨4029766908088093620620473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21492090176469832643309189 4029766908088093620620473)
                      ·
                        rfl

theorem cell23_7847943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_7847943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7847943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7847943 prefixEnd_7847943 := by exact prefixLift 7847943
  have htrace : WordTrace (prefixWord ++ tailWord_7847943) baseStart_7847943 baseEnd_7847943 := by
    simpa [prefixWord, tailWord_7847943, baseEnd_7847943] using wordTrace_append hprefix tailTrace_7847943
  have hstable : (prefixWord ++ tailWord_7847943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7847943).length < 2 ^ (prefixWord ++ tailWord_7847943).sum := by decide
  have hdescent : baseEnd_7847943 < baseStart_7847943 := by decide
  rcases family_descends (prefixWord ++ tailWord_7847943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7847973 : List Nat := [1, 3, 1, 2, 2, 3, 2, 2, 1, 2, 4]
def baseStart_7847973 : Nat := 118140960795 + 7847973 * 2 ^ 59
def prefixEnd_7847973 : Nat := 4983230072969 + 3 ^ 40 * 7847973 * 2
def baseEnd_7847973 : Nat := 4029782312507728503245335

theorem tailTrace_7847973 : CollatzResearch.WordTrace tailWord_7847973 prefixEnd_7847973 4029782312507728503245335 := by
  unfold tailWord_7847973
  simp only [CollatzResearch.WordTrace]
  refine ⟨286239090797141622924620573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190826060531427748616413715 286239090797141622924620573)
  ·
    refine ⟨107339659048928108596732715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 286239090797141622924620573 107339659048928108596732715)
    ·
      refine ⟨161009488573392162895099073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107339659048928108596732715 161009488573392162895099073)
      ·
        refine ⟨120757116430044122171324305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161009488573392162895099073 120757116430044122171324305)
        ·
          refine ⟨90567837322533091628493229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120757116430044122171324305 90567837322533091628493229)
          ·
            refine ⟨33962938995949909360684961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90567837322533091628493229 33962938995949909360684961)
            ·
              refine ⟨25472204246962432020513721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33962938995949909360684961 25472204246962432020513721)
              ·
                refine ⟨19104153185221824015385291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25472204246962432020513721 19104153185221824015385291)
                ·
                  refine ⟨28656229777832736023077937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19104153185221824015385291 28656229777832736023077937)
                  ·
                    refine ⟨21492172333374552017308453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28656229777832736023077937 21492172333374552017308453)
                    ·
                      refine ⟨4029782312507728503245335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21492172333374552017308453 4029782312507728503245335)
                      ·
                        rfl

theorem cell23_7847973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 2, 1, 2, 4].length) (baseStart_7847973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7847973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7847973 prefixEnd_7847973 := by exact prefixLift 7847973
  have htrace : WordTrace (prefixWord ++ tailWord_7847973) baseStart_7847973 baseEnd_7847973 := by
    simpa [prefixWord, tailWord_7847973, baseEnd_7847973] using wordTrace_append hprefix tailTrace_7847973
  have hstable : (prefixWord ++ tailWord_7847973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7847973).length < 2 ^ (prefixWord ++ tailWord_7847973).sum := by decide
  have hdescent : baseEnd_7847973 < baseStart_7847973 := by decide
  rcases family_descends (prefixWord ++ tailWord_7847973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7848003 : List Nat := [1, 1, 1, 3, 1, 2, 2, 1, 2, 7, 2]
def baseStart_7848003 : Nat := 118140960795 + 7848003 * 2 ^ 59
def prefixEnd_7848003 : Nat := 4983230072969 + 3 ^ 40 * 7848003 * 2
def baseEnd_7848003 : Nat := 4029797716927363385870197

theorem tailTrace_7848003 : CollatzResearch.WordTrace tailWord_7848003 prefixEnd_7848003 4029797716927363385870197 := by
  unfold tailWord_7848003
  simp only [CollatzResearch.WordTrace]
  refine ⟨286240184987032938048212663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190826789991355292032141775 286240184987032938048212663)
  ·
    refine ⟨429360277480549407072318995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286240184987032938048212663 429360277480549407072318995)
    ·
      refine ⟨644040416220824110608478493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 429360277480549407072318995 644040416220824110608478493)
      ·
        refine ⟨241515156082809041478179435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 644040416220824110608478493 241515156082809041478179435)
        ·
          refine ⟨362272734124213562217269153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241515156082809041478179435 362272734124213562217269153)
          ·
            refine ⟨271704550593160171662951865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 362272734124213562217269153 271704550593160171662951865)
            ·
              refine ⟨203778412944870128747213899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 271704550593160171662951865 203778412944870128747213899)
              ·
                refine ⟨305667619417305193120820849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 203778412944870128747213899 305667619417305193120820849)
                ·
                  refine ⟨229250714562978894840615637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 305667619417305193120820849 229250714562978894840615637)
                  ·
                    refine ⟨5373063622569817847826929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 229250714562978894840615637 5373063622569817847826929)
                    ·
                      refine ⟨4029797716927363385870197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5373063622569817847826929 4029797716927363385870197)
                      ·
                        rfl

theorem cell23_7848003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 7, 2].length) (baseStart_7848003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7848003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7848003 prefixEnd_7848003 := by exact prefixLift 7848003
  have htrace : WordTrace (prefixWord ++ tailWord_7848003) baseStart_7848003 baseEnd_7848003 := by
    simpa [prefixWord, tailWord_7848003, baseEnd_7848003] using wordTrace_append hprefix tailTrace_7848003
  have hstable : (prefixWord ++ tailWord_7848003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7848003).length < 2 ^ (prefixWord ++ tailWord_7848003).sum := by decide
  have hdescent : baseEnd_7848003 < baseStart_7848003 := by decide
  rcases family_descends (prefixWord ++ tailWord_7848003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7848037 : List Nat := [1, 3, 1, 3, 2, 2, 2, 3, 1, 3, 2]
def baseStart_7848037 : Nat := 118140960795 + 7848037 * 2 ^ 59
def prefixEnd_7848037 : Nat := 4983230072969 + 3 ^ 40 * 7848037 * 2
def baseEnd_7848037 : Nat := 4029815175269616252845041

theorem tailTrace_7848037 : CollatzResearch.WordTrace tailWord_7848037 prefixEnd_7848037 4029815175269616252845041 := by
  unfold tailWord_7848037
  simp only [CollatzResearch.WordTrace]
  refine ⟨286241425068909761854950365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190827616712606507903300243 286241425068909761854950365)
  ·
    refine ⟨107340534400841160695606387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 286241425068909761854950365 107340534400841160695606387)
    ·
      refine ⟨161010801601261741043409581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107340534400841160695606387 161010801601261741043409581)
      ·
        refine ⟨60379050600473152891278593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161010801601261741043409581 60379050600473152891278593)
        ·
          refine ⟨45284287950354864668458945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60379050600473152891278593 45284287950354864668458945)
          ·
            refine ⟨33963215962766148501344209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45284287950354864668458945 33963215962766148501344209)
            ·
              refine ⟨25472411972074611376008157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33963215962766148501344209 25472411972074611376008157)
              ·
                refine ⟨9552154489527979266003059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25472411972074611376008157 9552154489527979266003059)
                ·
                  refine ⟨14328231734291968899004589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9552154489527979266003059 14328231734291968899004589)
                  ·
                    refine ⟨5373086900359488337126721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14328231734291968899004589 5373086900359488337126721)
                    ·
                      refine ⟨4029815175269616252845041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5373086900359488337126721 4029815175269616252845041)
                      ·
                        rfl

theorem cell23_7848037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 3, 1, 3, 2].length) (baseStart_7848037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7848037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7848037 prefixEnd_7848037 := by exact prefixLift 7848037
  have htrace : WordTrace (prefixWord ++ tailWord_7848037) baseStart_7848037 baseEnd_7848037 := by
    simpa [prefixWord, tailWord_7848037, baseEnd_7848037] using wordTrace_append hprefix tailTrace_7848037
  have hstable : (prefixWord ++ tailWord_7848037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7848037).length < 2 ^ (prefixWord ++ tailWord_7848037).sum := by decide
  have hdescent : baseEnd_7848037 < baseStart_7848037 := by decide
  rcases family_descends (prefixWord ++ tailWord_7848037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7848083 : List Nat := [1, 1, 1, 2, 1, 2, 3, 2, 4, 3, 3]
def baseStart_7848083 : Nat := 118140960795 + 7848083 * 2 ^ 59
def prefixEnd_7848083 : Nat := 4983230072969 + 3 ^ 40 * 7848083 * 2
def baseEnd_7848083 : Nat := 4029838795379723072869829

theorem tailTrace_7848083 : CollatzResearch.WordTrace tailWord_7848083 prefixEnd_7848083 4029838795379723072869829 := by
  unfold tailWord_7848083
  simp only [CollatzResearch.WordTrace]
  refine ⟨286243102826743111711124903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190828735217828741140749935 286243102826743111711124903)
  ·
    refine ⟨429364654240114667566687355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286243102826743111711124903 429364654240114667566687355)
    ·
      refine ⟨644046981360172001350031033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 429364654240114667566687355 644046981360172001350031033)
      ·
        refine ⟨483035236020129001012523275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 644046981360172001350031033 483035236020129001012523275)
        ·
          refine ⟨724552854030193501518784913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 483035236020129001012523275 724552854030193501518784913)
          ·
            refine ⟨543414640522645126139088685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 724552854030193501518784913 543414640522645126139088685)
            ·
              refine ⟨203780490195991922302158257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 543414640522645126139088685 203780490195991922302158257)
              ·
                refine ⟨152835367646993941726618693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 203780490195991922302158257 152835367646993941726618693)
                ·
                  refine ⟨28656631433811364073741005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 152835367646993941726618693 28656631433811364073741005)
                  ·
                    refine ⟨10746236787679261527652877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28656631433811364073741005 10746236787679261527652877)
                    ·
                      refine ⟨4029838795379723072869829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10746236787679261527652877 4029838795379723072869829)
                      ·
                        rfl

theorem cell23_7848083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 2, 4, 3, 3].length) (baseStart_7848083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7848083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7848083 prefixEnd_7848083 := by exact prefixLift 7848083
  have htrace : WordTrace (prefixWord ++ tailWord_7848083) baseStart_7848083 baseEnd_7848083 := by
    simpa [prefixWord, tailWord_7848083, baseEnd_7848083] using wordTrace_append hprefix tailTrace_7848083
  have hstable : (prefixWord ++ tailWord_7848083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7848083).length < 2 ^ (prefixWord ++ tailWord_7848083).sum := by decide
  have hdescent : baseEnd_7848083 < baseStart_7848083 := by decide
  rcases family_descends (prefixWord ++ tailWord_7848083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7848123 : List Nat := [1, 1, 1, 1, 1, 2, 6, 2, 1, 3, 4]
def baseStart_7848123 : Nat := 118140960795 + 7848123 * 2 ^ 59
def prefixEnd_7848123 : Nat := 4983230072969 + 3 ^ 40 * 7848123 * 2
def baseEnd_7848123 : Nat := 4029859334605902916369645

theorem tailTrace_7848123 : CollatzResearch.WordTrace tailWord_7848123 prefixEnd_7848123 4029859334605902916369645 := by
  unfold tailWord_7848123
  simp only [CollatzResearch.WordTrace]
  refine ⟨286244561746598198542581023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190829707831065465695054015 286244561746598198542581023)
  ·
    refine ⟨429366842619897297813871535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286244561746598198542581023 429366842619897297813871535)
    ·
      refine ⟨644050263929845946720807303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 429366842619897297813871535 644050263929845946720807303)
      ·
        refine ⟨966075395894768920081210955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 644050263929845946720807303 966075395894768920081210955)
        ·
          refine ⟨1449113093842153380121816433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 966075395894768920081210955 1449113093842153380121816433)
          ·
            refine ⟨1086834820381615035091362325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1449113093842153380121816433 1086834820381615035091362325)
            ·
              refine ⟨50945382205388204769907609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1086834820381615035091362325 50945382205388204769907609)
              ·
                refine ⟨38209036654041153577430707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50945382205388204769907609 38209036654041153577430707)
                ·
                  refine ⟨57313554981061730366146061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38209036654041153577430707 57313554981061730366146061)
                  ·
                    refine ⟨21492583117898148887304773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57313554981061730366146061 21492583117898148887304773)
                    ·
                      refine ⟨4029859334605902916369645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21492583117898148887304773 4029859334605902916369645)
                      ·
                        rfl

theorem cell23_7848123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 2, 1, 3, 4].length) (baseStart_7848123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7848123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7848123 prefixEnd_7848123 := by exact prefixLift 7848123
  have htrace : WordTrace (prefixWord ++ tailWord_7848123) baseStart_7848123 baseEnd_7848123 := by
    simpa [prefixWord, tailWord_7848123, baseEnd_7848123] using wordTrace_append hprefix tailTrace_7848123
  have hstable : (prefixWord ++ tailWord_7848123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7848123).length < 2 ^ (prefixWord ++ tailWord_7848123).sum := by decide
  have hdescent : baseEnd_7848123 < baseStart_7848123 := by decide
  rcases family_descends (prefixWord ++ tailWord_7848123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7848153 : List Nat := [1, 2, 1, 2, 3, 1, 3, 1, 2, 1, 6]
def baseStart_7848153 : Nat := 118140960795 + 7848153 * 2 ^ 59
def prefixEnd_7848153 : Nat := 4983230072969 + 3 ^ 40 * 7848153 * 2
def baseEnd_7848153 : Nat := 4029874739025537798994507

theorem tailTrace_7848153 : CollatzResearch.WordTrace tailWord_7848153 prefixEnd_7848153 4029874739025537798994507 := by
  unfold tailWord_7848153
  simp only [CollatzResearch.WordTrace]
  refine ⟨286245655936489513666173113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190830437290993009110782075 286245655936489513666173113)
  ·
    refine ⟨214684241952367135249629835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286245655936489513666173113 214684241952367135249629835)
    ·
      refine ⟨322026362928550702874444753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214684241952367135249629835 322026362928550702874444753)
      ·
        refine ⟨241519772196413027155833565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 322026362928550702874444753 241519772196413027155833565)
        ·
          refine ⟨90569914573654885183437587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 241519772196413027155833565 90569914573654885183437587)
          ·
            refine ⟨135854871860482327775156381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90569914573654885183437587 135854871860482327775156381)
            ·
              refine ⟨50945576947680872915683643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135854871860482327775156381 50945576947680872915683643)
              ·
                refine ⟨76418365421521309373525465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50945576947680872915683643 76418365421521309373525465)
                ·
                  refine ⟨57313774066140982030144099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76418365421521309373525465 57313774066140982030144099)
                  ·
                    refine ⟨85970661099211473045216149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57313774066140982030144099 85970661099211473045216149)
                    ·
                      refine ⟨4029874739025537798994507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85970661099211473045216149 4029874739025537798994507)
                      ·
                        rfl

theorem cell23_7848153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 1, 2, 1, 6].length) (baseStart_7848153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7848153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7848153 prefixEnd_7848153 := by exact prefixLift 7848153
  have htrace : WordTrace (prefixWord ++ tailWord_7848153) baseStart_7848153 baseEnd_7848153 := by
    simpa [prefixWord, tailWord_7848153, baseEnd_7848153] using wordTrace_append hprefix tailTrace_7848153
  have hstable : (prefixWord ++ tailWord_7848153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7848153).length < 2 ^ (prefixWord ++ tailWord_7848153).sum := by decide
  have hdescent : baseEnd_7848153 < baseStart_7848153 := by decide
  rcases family_descends (prefixWord ++ tailWord_7848153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7848160 : List Nat := [2, 1, 1, 3, 1, 3, 2, 1, 4, 2, 3]
def baseStart_7848160 : Nat := 118140960795 + 7848160 * 2 ^ 59
def prefixEnd_7848160 : Nat := 4983230072969 + 3 ^ 40 * 7848160 * 2
def baseEnd_7848160 : Nat := 4029878333390119271606975

theorem tailTrace_7848160 : CollatzResearch.WordTrace tailWord_7848160 prefixEnd_7848160 4029878333390119271606975 := by
  unfold tailWord_7848160
  simp only [CollatzResearch.WordTrace]
  refine ⟨143122955623732076930838967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190830607498309435907785289 143122955623732076930838967)
  ·
    refine ⟨214684433435598115396258451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143122955623732076930838967 214684433435598115396258451)
    ·
      refine ⟨322026650153397173094387677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214684433435598115396258451 322026650153397173094387677)
      ·
        refine ⟨120759993807523939910395379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 322026650153397173094387677 120759993807523939910395379)
        ·
          refine ⟨181139990711285909865593069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120759993807523939910395379 181139990711285909865593069)
          ·
            refine ⟨67927496516732216199597401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 181139990711285909865593069 67927496516732216199597401)
            ·
              refine ⟨50945622387549162149698051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67927496516732216199597401 50945622387549162149698051)
              ·
                refine ⟨76418433581323743224547077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50945622387549162149698051 76418433581323743224547077)
                ·
                  refine ⟨14328456296498201854602577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76418433581323743224547077 14328456296498201854602577)
                  ·
                    refine ⟨10746342222373651390951933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14328456296498201854602577 10746342222373651390951933)
                    ·
                      refine ⟨4029878333390119271606975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10746342222373651390951933 4029878333390119271606975)
                      ·
                        rfl

theorem cell23_7848160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 1, 4, 2, 3].length) (baseStart_7848160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7848160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7848160 prefixEnd_7848160 := by exact prefixLift 7848160
  have htrace : WordTrace (prefixWord ++ tailWord_7848160) baseStart_7848160 baseEnd_7848160 := by
    simpa [prefixWord, tailWord_7848160, baseEnd_7848160] using wordTrace_append hprefix tailTrace_7848160
  have hstable : (prefixWord ++ tailWord_7848160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7848160).length < 2 ^ (prefixWord ++ tailWord_7848160).sum := by decide
  have hdescent : baseEnd_7848160 < baseStart_7848160 := by decide
  rcases family_descends (prefixWord ++ tailWord_7848160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7848167 : List Nat := [1, 1, 5, 3, 1, 1, 1, 3, 3, 4]
def baseStart_7848167 : Nat := 118140960795 + 7848167 * 2 ^ 59
def prefixEnd_7848167 : Nat := 4983230072969 + 3 ^ 40 * 7848167 * 2
def baseEnd_7848167 : Nat := 1343293975918233581406481

theorem tailTrace_7848167 : CollatzResearch.WordTrace tailWord_7848167 prefixEnd_7848167 1343293975918233581406481 := by
  unfold tailWord_7848167
  simp only [CollatzResearch.WordTrace]
  refine ⟨286246166558438794057182755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190830777705625862704788503 286246166558438794057182755)
  ·
    refine ⟨429369249837658191085774133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286246166558438794057182755 429369249837658191085774133)
    ·
      refine ⟨40253367172280455414291325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 429369249837658191085774133 40253367172280455414291325)
      ·
        refine ⟨15095012689605170780359247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40253367172280455414291325 15095012689605170780359247)
        ·
          refine ⟨22642519034407756170538871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15095012689605170780359247 22642519034407756170538871)
          ·
            refine ⟨33963778551611634255808307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22642519034407756170538871 33963778551611634255808307)
            ·
              refine ⟨50945667827417451383712461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33963778551611634255808307 50945667827417451383712461)
              ·
                refine ⟨19104625435281544268892173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50945667827417451383712461 19104625435281544268892173)
                ·
                  refine ⟨7164234538230579100834565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19104625435281544268892173 7164234538230579100834565)
                  ·
                    refine ⟨1343293975918233581406481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7164234538230579100834565 1343293975918233581406481)
                    ·
                      rfl

theorem cell23_7848167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 3, 3, 4].length) (baseStart_7848167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7848167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7848167 prefixEnd_7848167 := by exact prefixLift 7848167
  have htrace : WordTrace (prefixWord ++ tailWord_7848167) baseStart_7848167 baseEnd_7848167 := by
    simpa [prefixWord, tailWord_7848167, baseEnd_7848167] using wordTrace_append hprefix tailTrace_7848167
  have hstable : (prefixWord ++ tailWord_7848167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7848167).length < 2 ^ (prefixWord ++ tailWord_7848167).sum := by decide
  have hdescent : baseEnd_7848167 < baseStart_7848167 := by decide
  rcases family_descends (prefixWord ++ tailWord_7848167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7848224 : List Nat := [2, 1, 1, 5, 2, 1, 3, 1, 3, 1, 3]
def baseStart_7848224 : Nat := 118140960795 + 7848224 * 2 ^ 59
def prefixEnd_7848224 : Nat := 4983230072969 + 3 ^ 40 * 7848224 * 2
def baseEnd_7848224 : Nat := 4029911196152007021206681

theorem tailTrace_7848224 : CollatzResearch.WordTrace tailWord_7848224 prefixEnd_7848224 4029911196152007021206681 := by
  unfold tailWord_7848224
  simp only [CollatzResearch.WordTrace]
  refine ⟨143124122759616146396003863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190832163679488195194671817 143124122759616146396003863)
  ·
    refine ⟨214686184139424219594005795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143124122759616146396003863 214686184139424219594005795)
    ·
      refine ⟨322029276209136329391008693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214686184139424219594005795 322029276209136329391008693)
      ·
        refine ⟨30190244644606530880407065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 322029276209136329391008693 30190244644606530880407065)
        ·
          refine ⟨22642683483454898160305299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30190244644606530880407065 22642683483454898160305299)
          ·
            refine ⟨33964025225182347240457949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22642683483454898160305299 33964025225182347240457949)
            ·
              refine ⟨12736509459443380215171731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33964025225182347240457949 12736509459443380215171731)
              ·
                refine ⟨19104764189165070322757597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12736509459443380215171731 19104764189165070322757597)
                ·
                  refine ⟨7164286570936901371034099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19104764189165070322757597 7164286570936901371034099)
                  ·
                    refine ⟨10746429856405352056551149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7164286570936901371034099 10746429856405352056551149)
                    ·
                      refine ⟨4029911196152007021206681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10746429856405352056551149 4029911196152007021206681)
                      ·
                        rfl

theorem cell23_7848224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 3, 1, 3, 1, 3].length) (baseStart_7848224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7848224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7848224 prefixEnd_7848224 := by exact prefixLift 7848224
  have htrace : WordTrace (prefixWord ++ tailWord_7848224) baseStart_7848224 baseEnd_7848224 := by
    simpa [prefixWord, tailWord_7848224, baseEnd_7848224] using wordTrace_append hprefix tailTrace_7848224
  have hstable : (prefixWord ++ tailWord_7848224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7848224).length < 2 ^ (prefixWord ++ tailWord_7848224).sum := by decide
  have hdescent : baseEnd_7848224 < baseStart_7848224 := by decide
  rcases family_descends (prefixWord ++ tailWord_7848224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7848231 : List Nat := [1, 1, 8, 1, 1, 1, 1, 3, 6]
def baseStart_7848231 : Nat := 118140960795 + 7848231 * 2 ^ 59
def prefixEnd_7848231 : Nat := 4983230072969 + 3 ^ 40 * 7848231 * 2
def baseEnd_7848231 : Nat := 447768310057398721535461

theorem tailTrace_7848231 : CollatzResearch.WordTrace tailWord_7848231 prefixEnd_7848231 447768310057398721535461 := by
  unfold tailWord_7848231
  simp only [CollatzResearch.WordTrace]
  refine ⟨286248500830206932987512547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190832333886804621991675031 286248500830206932987512547)
  ·
    refine ⟨429372751245310399481268821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286248500830206932987512547 429372751245310399481268821)
    ·
      refine ⟨5031711928655981243921119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 429372751245310399481268821 5031711928655981243921119)
      ·
        refine ⟨7547567892983971865881679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5031711928655981243921119 7547567892983971865881679)
        ·
          refine ⟨11321351839475957798822519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7547567892983971865881679 11321351839475957798822519)
          ·
            refine ⟨16982027759213936698233779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11321351839475957798822519 16982027759213936698233779)
            ·
              refine ⟨25473041638820905047350669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16982027759213936698233779 25473041638820905047350669)
              ·
                refine ⟨9552390614557839392756501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25473041638820905047350669 9552390614557839392756501)
                ·
                  refine ⟨447768310057398721535461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9552390614557839392756501 447768310057398721535461)
                  ·
                    rfl

theorem cell23_7848231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 3, 6].length) (baseStart_7848231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7848231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7848231 prefixEnd_7848231 := by exact prefixLift 7848231
  have htrace : WordTrace (prefixWord ++ tailWord_7848231) baseStart_7848231 baseEnd_7848231 := by
    simpa [prefixWord, tailWord_7848231, baseEnd_7848231] using wordTrace_append hprefix tailTrace_7848231
  have hstable : (prefixWord ++ tailWord_7848231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7848231).length < 2 ^ (prefixWord ++ tailWord_7848231).sum := by decide
  have hdescent : baseEnd_7848231 < baseStart_7848231 := by decide
  rcases family_descends (prefixWord ++ tailWord_7848231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7848240 : List Nat := [2, 1, 1, 1, 2, 2, 2, 2, 6, 4]
def baseStart_7848240 : Nat := 118140960795 + 7848240 * 2 ^ 59
def prefixEnd_7848240 : Nat := 4983230072969 + 3 ^ 40 * 7848240 * 2
def baseEnd_7848240 : Nat := 1343306470614159652868869

theorem tailTrace_7848240 : CollatzResearch.WordTrace tailWord_7848240 prefixEnd_7848240 1343306470614159652868869 := by
  unfold tailWord_7848240
  simp only [CollatzResearch.WordTrace]
  refine ⟨143124414543587163762295087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190832552724782885016393449 143124414543587163762295087)
  ·
    refine ⟨214686621815380745643442631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143124414543587163762295087 214686621815380745643442631)
    ·
      refine ⟨322029932723071118465163947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214686621815380745643442631 322029932723071118465163947)
      ·
        refine ⟨483044899084606677697745921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322029932723071118465163947 483044899084606677697745921)
        ·
          refine ⟨362283674313455008273309441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 483044899084606677697745921 362283674313455008273309441)
          ·
            refine ⟨271712755735091256204982081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 362283674313455008273309441 271712755735091256204982081)
            ·
              refine ⟨203784566801318442153736561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 271712755735091256204982081 203784566801318442153736561)
              ·
                refine ⟨152838425100988831615302421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 203784566801318442153736561 152838425100988831615302421)
                ·
                  refine ⟨7164301176608851481967301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 152838425100988831615302421 7164301176608851481967301)
                  ·
                    refine ⟨1343306470614159652868869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7164301176608851481967301 1343306470614159652868869)
                    ·
                      rfl

theorem cell23_7848240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 6, 4].length) (baseStart_7848240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7848240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7848240 prefixEnd_7848240 := by exact prefixLift 7848240
  have htrace : WordTrace (prefixWord ++ tailWord_7848240) baseStart_7848240 baseEnd_7848240 := by
    simpa [prefixWord, tailWord_7848240, baseEnd_7848240] using wordTrace_append hprefix tailTrace_7848240
  have hstable : (prefixWord ++ tailWord_7848240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7848240).length < 2 ^ (prefixWord ++ tailWord_7848240).sum := by decide
  have hdescent : baseEnd_7848240 < baseStart_7848240 := by decide
  rcases family_descends (prefixWord ++ tailWord_7848240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7848244 : List Nat := [2, 5, 1, 1, 1, 2, 3, 2, 1, 5]
def baseStart_7848244 : Nat := 118140960795 + 7848244 * 2 ^ 59
def prefixEnd_7848244 : Nat := 4983230072969 + 3 ^ 40 * 7848244 * 2
def baseEnd_7848244 : Nat := 1343307155255032314318863

theorem tailTrace_7848244 : CollatzResearch.WordTrace tailWord_7848244 prefixEnd_7848244 1343307155255032314318863 := by
  unfold tailWord_7848244
  simp only [CollatzResearch.WordTrace]
  refine ⟨143124487489579918103867893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190832649986106557471823857 143124487489579918103867893)
  ·
    refine ⟨13417920702148117322237615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 143124487489579918103867893 13417920702148117322237615)
    ·
      refine ⟨20126881053222175983356423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13417920702148117322237615 20126881053222175983356423)
      ·
        refine ⟨30190321579833263975034635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20126881053222175983356423 30190321579833263975034635)
        ·
          refine ⟨45285482369749895962551953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30190321579833263975034635 45285482369749895962551953)
          ·
            refine ⟨33964111777312421971913965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45285482369749895962551953 33964111777312421971913965)
            ·
              refine ⟨12736541916492158239467737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33964111777312421971913965 12736541916492158239467737)
              ·
                refine ⟨9552406437369118679600803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12736541916492158239467737 9552406437369118679600803)
                ·
                  refine ⟨14328609656053678019401205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9552406437369118679600803 14328609656053678019401205)
                  ·
                    refine ⟨1343307155255032314318863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14328609656053678019401205 1343307155255032314318863)
                    ·
                      rfl

theorem cell23_7848244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 3, 2, 1, 5].length) (baseStart_7848244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7848244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7848244 prefixEnd_7848244 := by exact prefixLift 7848244
  have htrace : WordTrace (prefixWord ++ tailWord_7848244) baseStart_7848244 baseEnd_7848244 := by
    simpa [prefixWord, tailWord_7848244, baseEnd_7848244] using wordTrace_append hprefix tailTrace_7848244
  have hstable : (prefixWord ++ tailWord_7848244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7848244).length < 2 ^ (prefixWord ++ tailWord_7848244).sum := by decide
  have hdescent : baseEnd_7848244 < baseStart_7848244 := by decide
  rcases family_descends (prefixWord ++ tailWord_7848244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7848297 : List Nat := [1, 2, 1, 1, 1, 3, 6, 1, 1, 3, 3]
def baseStart_7848297 : Nat := 118140960795 + 7848297 * 2 ^ 59
def prefixEnd_7848297 : Nat := 4983230072969 + 3 ^ 40 * 7848297 * 2
def baseEnd_7848297 : Nat := 4029948680239785235593845

theorem tailTrace_7848297 : CollatzResearch.WordTrace tailWord_7848297 prefixEnd_7848297 4029948680239785235593845 := by
  unfold tailWord_7848297
  simp only [CollatzResearch.WordTrace]
  refine ⟨286250908047967826259415145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190833938698645217506276763 286250908047967826259415145)
  ·
    refine ⟨214688181035975869694561359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286250908047967826259415145 214688181035975869694561359)
    ·
      refine ⟨322032271553963804541842039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214688181035975869694561359 322032271553963804541842039)
      ·
        refine ⟨483048407330945706812763059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322032271553963804541842039 483048407330945706812763059)
        ·
          refine ⟨724572610996418560219144589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 483048407330945706812763059 724572610996418560219144589)
          ·
            refine ⟨271714729123656960082179221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 724572610996418560219144589 271714729123656960082179221)
            ·
              refine ⟨12736627927671420003852151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 271714729123656960082179221 12736627927671420003852151)
              ·
                refine ⟨19104941891507130005778227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12736627927671420003852151 19104941891507130005778227)
                ·
                  refine ⟨28657412837260695008667341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19104941891507130005778227 28657412837260695008667341)
                  ·
                    refine ⟨10746529813972760628250253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28657412837260695008667341 10746529813972760628250253)
                    ·
                      refine ⟨4029948680239785235593845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10746529813972760628250253 4029948680239785235593845)
                      ·
                        rfl

theorem cell23_7848297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 6, 1, 1, 3, 3].length) (baseStart_7848297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7848297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7848297 prefixEnd_7848297 := by exact prefixLift 7848297
  have htrace : WordTrace (prefixWord ++ tailWord_7848297) baseStart_7848297 baseEnd_7848297 := by
    simpa [prefixWord, tailWord_7848297, baseEnd_7848297] using wordTrace_append hprefix tailTrace_7848297
  have hstable : (prefixWord ++ tailWord_7848297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7848297).length < 2 ^ (prefixWord ++ tailWord_7848297).sum := by decide
  have hdescent : baseEnd_7848297 < baseStart_7848297 := by decide
  rcases family_descends (prefixWord ++ tailWord_7848297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7848331 : List Nat := [1, 1, 1, 1, 4, 6, 1, 2, 2, 1, 3]
def baseStart_7848331 : Nat := 118140960795 + 7848331 * 2 ^ 59
def prefixEnd_7848331 : Nat := 4983230072969 + 3 ^ 40 * 7848331 * 2
def baseEnd_7848331 : Nat := 4029966138582038102568689

theorem tailTrace_7848331 : CollatzResearch.WordTrace tailWord_7848331 prefixEnd_7848331 4029966138582038102568689 := by
  unfold tailWord_7848331
  simp only [CollatzResearch.WordTrace]
  refine ⟨286252148129844650066152847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190834765419896433377435231 286252148129844650066152847)
  ·
    refine ⟨429378222194766975099229271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286252148129844650066152847 429378222194766975099229271)
    ·
      refine ⟨644067333292150462648843907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 429378222194766975099229271 644067333292150462648843907)
      ·
        refine ⟨966100999938225693973265861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 644067333292150462648843907 966100999938225693973265861)
        ·
          refine ⟨181143937488417317619987349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 966100999938225693973265861 181143937488417317619987349)
          ·
            refine ⟨8491122069769561763436907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 181143937488417317619987349 8491122069769561763436907)
            ·
              refine ⟨12736683104654342645155361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8491122069769561763436907 12736683104654342645155361)
              ·
                refine ⟨9552512328490756983866521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12736683104654342645155361 9552512328490756983866521)
                ·
                  refine ⟨7164384246368067737899891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9552512328490756983866521 7164384246368067737899891)
                  ·
                    refine ⟨10746576369552101606849837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7164384246368067737899891 10746576369552101606849837)
                    ·
                      refine ⟨4029966138582038102568689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10746576369552101606849837 4029966138582038102568689)
                      ·
                        rfl

theorem cell23_7848331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 1, 2, 2, 1, 3].length) (baseStart_7848331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7848331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7848331 prefixEnd_7848331 := by exact prefixLift 7848331
  have htrace : WordTrace (prefixWord ++ tailWord_7848331) baseStart_7848331 baseEnd_7848331 := by
    simpa [prefixWord, tailWord_7848331, baseEnd_7848331] using wordTrace_append hprefix tailTrace_7848331
  have hstable : (prefixWord ++ tailWord_7848331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7848331).length < 2 ^ (prefixWord ++ tailWord_7848331).sum := by decide
  have hdescent : baseEnd_7848331 < baseStart_7848331 := by decide
  rcases family_descends (prefixWord ++ tailWord_7848331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7848342 : List Nat := [5, 3, 1, 2, 1, 1, 3, 1, 2, 4]
def baseStart_7848342 : Nat := 118140960795 + 7848342 * 2 ^ 59
def prefixEnd_7848342 : Nat := 4983230072969 + 3 ^ 40 * 7848342 * 2
def baseEnd_7848342 : Nat := 1343323928956412519843713

theorem tailTrace_7848342 : CollatzResearch.WordTrace tailWord_7848342 prefixEnd_7848342 1343323928956412519843713 := by
  unfold tailWord_7848342
  simp only [CollatzResearch.WordTrace]
  refine ⟨17890784333300299934050205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 190835032888536532629868853 17890784333300299934050205)
  ·
    refine ⟨6709044124987612475268827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17890784333300299934050205 6709044124987612475268827)
    ·
      refine ⟨10063566187481418712903241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6709044124987612475268827 10063566187481418712903241)
      ·
        refine ⟨7547674640611064034677431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10063566187481418712903241 7547674640611064034677431)
        ·
          refine ⟨11321511960916596052016147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7547674640611064034677431 11321511960916596052016147)
          ·
            refine ⟨16982267941374894078024221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11321511960916596052016147 16982267941374894078024221)
            ·
              refine ⟨6368350478015585279259083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16982267941374894078024221 6368350478015585279259083)
              ·
                refine ⟨9552525717023377918888625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6368350478015585279259083 9552525717023377918888625)
                ·
                  refine ⟨7164394287767533439166469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9552525717023377918888625 7164394287767533439166469)
                  ·
                    refine ⟨1343323928956412519843713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7164394287767533439166469 1343323928956412519843713)
                    ·
                      rfl

theorem cell23_7848342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_7848342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7848342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7848342 prefixEnd_7848342 := by exact prefixLift 7848342
  have htrace : WordTrace (prefixWord ++ tailWord_7848342) baseStart_7848342 baseEnd_7848342 := by
    simpa [prefixWord, tailWord_7848342, baseEnd_7848342] using wordTrace_append hprefix tailTrace_7848342
  have hstable : (prefixWord ++ tailWord_7848342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7848342).length < 2 ^ (prefixWord ++ tailWord_7848342).sum := by decide
  have hdescent : baseEnd_7848342 < baseStart_7848342 := by decide
  rcases family_descends (prefixWord ++ tailWord_7848342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7848405 : List Nat := [1, 3, 2, 3, 1, 4, 2, 1, 2, 2, 2]
def baseStart_7848405 : Nat := 118140960795 + 7848405 * 2 ^ 59
def prefixEnd_7848405 : Nat := 4983230072969 + 3 ^ 40 * 7848405 * 2
def baseEnd_7848405 : Nat := 4030004136150470813043349

theorem tailTrace_7848405 : CollatzResearch.WordTrace tailWord_7848405 prefixEnd_7848405 4030004136150470813043349 := by
  unfold tailWord_7848405
  simp only [CollatzResearch.WordTrace]
  refine ⟨286254847131576560704346669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190836564754384373802897779 286254847131576560704346669)
  ·
    refine ⟨107345567674341210264130001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 286254847131576560704346669 107345567674341210264130001)
    ·
      refine ⟨80509175755755907698097501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107345567674341210264130001 80509175755755907698097501)
      ·
        refine ⟨30190940908408465386786563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80509175755755907698097501 30190940908408465386786563)
        ·
          refine ⟨45286411362612698080179845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30190940908408465386786563 45286411362612698080179845)
          ·
            refine ⟨8491202130489880890033721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45286411362612698080179845 8491202130489880890033721)
            ·
              refine ⟨6368401597867410667525291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8491202130489880890033721 6368401597867410667525291)
              ·
                refine ⟨9552602396801116001287937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6368401597867410667525291 9552602396801116001287937)
                ·
                  refine ⟨7164451797600837000965953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9552602396801116001287937 7164451797600837000965953)
                  ·
                    refine ⟨5373338848200627750724465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7164451797600837000965953 5373338848200627750724465)
                    ·
                      refine ⟨4030004136150470813043349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5373338848200627750724465 4030004136150470813043349)
                      ·
                        rfl

theorem cell23_7848405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 2, 1, 2, 2, 2].length) (baseStart_7848405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7848405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7848405 prefixEnd_7848405 := by exact prefixLift 7848405
  have htrace : WordTrace (prefixWord ++ tailWord_7848405) baseStart_7848405 baseEnd_7848405 := by
    simpa [prefixWord, tailWord_7848405, baseEnd_7848405] using wordTrace_append hprefix tailTrace_7848405
  have hstable : (prefixWord ++ tailWord_7848405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7848405).length < 2 ^ (prefixWord ++ tailWord_7848405).sum := by decide
  have hdescent : baseEnd_7848405 < baseStart_7848405 := by decide
  rcases family_descends (prefixWord ++ tailWord_7848405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7848424 : List Nat := [2, 1, 4, 1, 1, 4, 2, 1, 2, 5]
def baseStart_7848424 : Nat := 118140960795 + 7848424 * 2 ^ 59
def prefixEnd_7848424 : Nat := 4983230072969 + 3 ^ 40 * 7848424 * 2
def baseEnd_7848424 : Nat := 1343337964094302079568587

theorem tailTrace_7848424 : CollatzResearch.WordTrace tailWord_7848424 prefixEnd_7848424 1343337964094302079568587 := by
  unfold tailWord_7848424
  simp only [CollatzResearch.WordTrace]
  refine ⟨143127770059253863474644163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190837026745671817966192217 143127770059253863474644163)
  ·
    refine ⟨214691655088880795211966245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143127770059253863474644163 214691655088880795211966245)
    ·
      refine ⟨40254685329165149102243671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 214691655088880795211966245 40254685329165149102243671)
      ·
        refine ⟨60382027993747723653365507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40254685329165149102243671 60382027993747723653365507)
        ·
          refine ⟨90573041990621585480048261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60382027993747723653365507 90573041990621585480048261)
          ·
            refine ⟨16982445373241547277509049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90573041990621585480048261 16982445373241547277509049)
            ·
              refine ⟨12736834029931160458131787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16982445373241547277509049 12736834029931160458131787)
              ·
                refine ⟨19105251044896740687197681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12736834029931160458131787 19105251044896740687197681)
                ·
                  refine ⟨14328938283672555515398261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19105251044896740687197681 14328938283672555515398261)
                  ·
                    refine ⟨1343337964094302079568587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14328938283672555515398261 1343337964094302079568587)
                    ·
                      rfl

theorem cell23_7848424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 2, 1, 2, 5].length) (baseStart_7848424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7848424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7848424 prefixEnd_7848424 := by exact prefixLift 7848424
  have htrace : WordTrace (prefixWord ++ tailWord_7848424) baseStart_7848424 baseEnd_7848424 := by
    simpa [prefixWord, tailWord_7848424, baseEnd_7848424] using wordTrace_append hprefix tailTrace_7848424
  have hstable : (prefixWord ++ tailWord_7848424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7848424).length < 2 ^ (prefixWord ++ tailWord_7848424).sum := by decide
  have hdescent : baseEnd_7848424 < baseStart_7848424 := by decide
  rcases family_descends (prefixWord ++ tailWord_7848424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7848444 : List Nat := [2, 2, 2, 1, 2, 1, 1, 4, 2, 4, 2]
def baseStart_7848444 : Nat := 118140960795 + 7848444 * 2 ^ 59
def prefixEnd_7848444 : Nat := 4983230072969 + 3 ^ 40 * 7848444 * 2
def baseEnd_7848444 : Nat := 4030024161895996160455669

theorem tailTrace_7848444 : CollatzResearch.WordTrace tailWord_7848444 prefixEnd_7848444 4030024161895996160455669 := by
  unfold tailWord_7848444
  simp only [CollatzResearch.WordTrace]
  refine ⟨143128134789217635182508193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190837513052290180243344257 143128134789217635182508193)
  ·
    refine ⟨107346101091913226386881145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143128134789217635182508193 107346101091913226386881145)
    ·
      refine ⟨80509575818934919790160859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107346101091913226386881145 80509575818934919790160859)
      ·
        refine ⟨120764363728402379685241289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80509575818934919790160859 120764363728402379685241289)
        ·
          refine ⟨90573272796301784763930967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120764363728402379685241289 90573272796301784763930967)
          ·
            refine ⟨135859909194452677145896451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90573272796301784763930967 135859909194452677145896451)
            ·
              refine ⟨203789863791679015718844677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135859909194452677145896451 203789863791679015718844677)
              ·
                refine ⟨38210599460939815447283377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 203789863791679015718844677 38210599460939815447283377)
                ·
                  refine ⟨28657949595704861585462533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38210599460939815447283377 28657949595704861585462533)
                  ·
                    refine ⟨5373365549194661547274225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28657949595704861585462533 5373365549194661547274225)
                    ·
                      refine ⟨4030024161895996160455669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5373365549194661547274225 4030024161895996160455669)
                      ·
                        rfl

theorem cell23_7848444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 4, 2, 4, 2].length) (baseStart_7848444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7848444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7848444 prefixEnd_7848444 := by exact prefixLift 7848444
  have htrace : WordTrace (prefixWord ++ tailWord_7848444) baseStart_7848444 baseEnd_7848444 := by
    simpa [prefixWord, tailWord_7848444, baseEnd_7848444] using wordTrace_append hprefix tailTrace_7848444
  have hstable : (prefixWord ++ tailWord_7848444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7848444).length < 2 ^ (prefixWord ++ tailWord_7848444).sum := by decide
  have hdescent : baseEnd_7848444 < baseStart_7848444 := by decide
  rcases family_descends (prefixWord ++ tailWord_7848444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7848467 : List Nat := [1, 1, 1, 2, 1, 5, 1, 5, 6]
def baseStart_7848467 : Nat := 118140960795 + 7848467 * 2 ^ 59
def prefixEnd_7848467 : Nat := 4983230072969 + 3 ^ 40 * 7848467 * 2
def baseEnd_7848467 : Nat := 447781774661227730052007

theorem tailTrace_7848467 : CollatzResearch.WordTrace tailWord_7848467 prefixEnd_7848467 447781774661227730052007 := by
  unfold tailWord_7848467
  simp only [CollatzResearch.WordTrace]
  refine ⟨286257108457351945293103655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190838072304901296862069103 286257108457351945293103655)
  ·
    refine ⟨429385662686027917939655483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286257108457351945293103655 429385662686027917939655483)
    ·
      refine ⟨644078494029041876909483225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 429385662686027917939655483 644078494029041876909483225)
      ·
        refine ⟨483058870521781407682112419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 644078494029041876909483225 483058870521781407682112419)
        ·
          refine ⟨724588305782672111523168629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 483058870521781407682112419 724588305782672111523168629)
          ·
            refine ⟨67930153667125510455297059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 724588305782672111523168629 67930153667125510455297059)
            ·
              refine ⟨101895230500688265682945589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67930153667125510455297059 101895230500688265682945589)
              ·
                refine ⟨9552677859439524907776149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 101895230500688265682945589 9552677859439524907776149)
                ·
                  refine ⟨447781774661227730052007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9552677859439524907776149 447781774661227730052007)
                  ·
                    rfl

theorem cell23_7848467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 5, 6].length) (baseStart_7848467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7848467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7848467 prefixEnd_7848467 := by exact prefixLift 7848467
  have htrace : WordTrace (prefixWord ++ tailWord_7848467) baseStart_7848467 baseEnd_7848467 := by
    simpa [prefixWord, tailWord_7848467, baseEnd_7848467] using wordTrace_append hprefix tailTrace_7848467
  have hstable : (prefixWord ++ tailWord_7848467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7848467).length < 2 ^ (prefixWord ++ tailWord_7848467).sum := by decide
  have hdescent : baseEnd_7848467 < baseStart_7848467 := by decide
  rcases family_descends (prefixWord ++ tailWord_7848467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7848488 : List Nat := [2, 1, 5, 2, 1, 1, 1, 5, 1, 4]
def baseStart_7848488 : Nat := 118140960795 + 7848488 * 2 ^ 59
def prefixEnd_7848488 : Nat := 4983230072969 + 3 ^ 40 * 7848488 * 2
def baseEnd_7848488 : Nat := 1343348918348264662768489

theorem tailTrace_7848488 : CollatzResearch.WordTrace tailWord_7848488 prefixEnd_7848488 1343348918348264662768489 := by
  unfold tailWord_7848488
  simp only [CollatzResearch.WordTrace]
  refine ⟨143128937195137932939809059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190838582926850577253078745 143128937195137932939809059)
  ·
    refine ⟨214693405792706899409713589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143128937195137932939809059 214693405792706899409713589)
    ·
      refine ⟨20127506793066271819660649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 214693405792706899409713589 20127506793066271819660649)
      ·
        refine ⟨15095630094799703864745487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20127506793066271819660649 15095630094799703864745487)
        ·
          refine ⟨22643445142199555797118231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15095630094799703864745487 22643445142199555797118231)
          ·
            refine ⟨33965167713299333695677347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22643445142199555797118231 33965167713299333695677347)
            ·
              refine ⟨50947751569949000543516021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33965167713299333695677347 50947751569949000543516021)
              ·
                refine ⟨4776351709682718800954627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50947751569949000543516021 4776351709682718800954627)
                ·
                  refine ⟨7164527564524078201431941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4776351709682718800954627 7164527564524078201431941)
                  ·
                    refine ⟨1343348918348264662768489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7164527564524078201431941 1343348918348264662768489)
                    ·
                      rfl

theorem cell23_7848488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 5, 1, 4].length) (baseStart_7848488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7848488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7848488 prefixEnd_7848488 := by exact prefixLift 7848488
  have htrace : WordTrace (prefixWord ++ tailWord_7848488) baseStart_7848488 baseEnd_7848488 := by
    simpa [prefixWord, tailWord_7848488, baseEnd_7848488] using wordTrace_append hprefix tailTrace_7848488
  have hstable : (prefixWord ++ tailWord_7848488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7848488).length < 2 ^ (prefixWord ++ tailWord_7848488).sum := by decide
  have hdescent : baseEnd_7848488 < baseStart_7848488 := by decide
  rcases family_descends (prefixWord ++ tailWord_7848488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7848511 : List Nat := [1, 1, 2, 2, 3, 2, 4, 1, 3, 1, 3]
def baseStart_7848511 : Nat := 118140960795 + 7848511 * 2 ^ 59
def prefixEnd_7848511 : Nat := 4983230072969 + 3 ^ 40 * 7848511 * 2
def baseEnd_7848511 : Nat := 4030058565099847398317861

theorem tailTrace_7848511 : CollatzResearch.WordTrace tailWord_7848511 prefixEnd_7848511 4030058565099847398317861 := by
  unfold tailWord_7848511
  simp only [CollatzResearch.WordTrace]
  refine ⟨286258713269192540807705387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190839142179461693871803591 286258713269192540807705387)
  ·
    refine ⟨429388069903788811211558081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286258713269192540807705387 429388069903788811211558081)
    ·
      refine ⟨322041052427841608408668561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 429388069903788811211558081 322041052427841608408668561)
      ·
        refine ⟨241530789320881206306501421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 322041052427841608408668561 241530789320881206306501421)
        ·
          refine ⟨90574045995330452364938033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 241530789320881206306501421 90574045995330452364938033)
          ·
            refine ⟨67930534496497839273703525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90574045995330452364938033 67930534496497839273703525)
            ·
              refine ⟨12736975218093344863819411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67930534496497839273703525 12736975218093344863819411)
              ·
                refine ⟨19105462827140017295729117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12736975218093344863819411 19105462827140017295729117)
                ·
                  refine ⟨7164548560177506485898419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19105462827140017295729117 7164548560177506485898419)
                  ·
                    refine ⟨10746822840266259728847629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7164548560177506485898419 10746822840266259728847629)
                    ·
                      refine ⟨4030058565099847398317861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10746822840266259728847629 4030058565099847398317861)
                      ·
                        rfl

theorem cell23_7848511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 4, 1, 3, 1, 3].length) (baseStart_7848511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7848511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7848511 prefixEnd_7848511 := by exact prefixLift 7848511
  have htrace : WordTrace (prefixWord ++ tailWord_7848511) baseStart_7848511 baseEnd_7848511 := by
    simpa [prefixWord, tailWord_7848511, baseEnd_7848511] using wordTrace_append hprefix tailTrace_7848511
  have hstable : (prefixWord ++ tailWord_7848511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7848511).length < 2 ^ (prefixWord ++ tailWord_7848511).sum := by decide
  have hdescent : baseEnd_7848511 < baseStart_7848511 := by decide
  rcases family_descends (prefixWord ++ tailWord_7848511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7848544 : List Nat := [2, 1, 1, 3, 2, 1, 3, 2, 4, 4]
def baseStart_7848544 : Nat := 118140960795 + 7848544 * 2 ^ 59
def prefixEnd_7848544 : Nat := 4983230072969 + 3 ^ 40 * 7848544 * 2
def baseEnd_7848544 : Nat := 1343358503320481923068403

theorem tailTrace_7848544 : CollatzResearch.WordTrace tailWord_7848544 prefixEnd_7848544 1343358503320481923068403 := by
  unfold tailWord_7848544
  simp only [CollatzResearch.WordTrace]
  refine ⟨143129958439036493721828343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190839944585381991629104457 143129958439036493721828343)
  ·
    refine ⟨214694937658554740582742515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143129958439036493721828343 214694937658554740582742515)
    ·
      refine ⟨322042406487832110874113773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214694937658554740582742515 322042406487832110874113773)
      ·
        refine ⟨120765902432937041577792665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 322042406487832110874113773 120765902432937041577792665)
        ·
          refine ⟨90574426824702781183344499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120765902432937041577792665 90574426824702781183344499)
          ·
            refine ⟨135861640237054171775016749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90574426824702781183344499 135861640237054171775016749)
            ·
              refine ⟨50948115088895314415631281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135861640237054171775016749 50948115088895314415631281)
              ·
                refine ⟨38211086316671485811723461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50948115088895314415631281 38211086316671485811723461)
                ·
                  refine ⟨7164578684375903589698149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38211086316671485811723461 7164578684375903589698149)
                  ·
                    refine ⟨1343358503320481923068403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7164578684375903589698149 1343358503320481923068403)
                    ·
                      rfl

theorem cell23_7848544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 2, 4, 4].length) (baseStart_7848544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7848544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7848544 prefixEnd_7848544 := by exact prefixLift 7848544
  have htrace : WordTrace (prefixWord ++ tailWord_7848544) baseStart_7848544 baseEnd_7848544 := by
    simpa [prefixWord, tailWord_7848544, baseEnd_7848544] using wordTrace_append hprefix tailTrace_7848544
  have hstable : (prefixWord ++ tailWord_7848544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7848544).length < 2 ^ (prefixWord ++ tailWord_7848544).sum := by decide
  have hdescent : baseEnd_7848544 < baseStart_7848544 := by decide
  rcases family_descends (prefixWord ++ tailWord_7848544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7848545 : List Nat := [1, 2, 3, 1, 1, 6, 1, 3, 1, 1, 3]
def baseStart_7848545 : Nat := 118140960795 + 7848545 * 2 ^ 59
def prefixEnd_7848545 : Nat := 4983230072969 + 3 ^ 40 * 7848545 * 2
def baseEnd_7848545 : Nat := 4030076023442100265292705

theorem tailTrace_7848545 : CollatzResearch.WordTrace tailWord_7848545 prefixEnd_7848545 4030076023442100265292705 := by
  unfold tailWord_7848545
  simp only [CollatzResearch.WordTrace]
  refine ⟨286259953351069364614443089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190839968900712909742962059 286259953351069364614443089)
  ·
    refine ⟨214694965013302023460832317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286259953351069364614443089 214694965013302023460832317)
    ·
      refine ⟨80510611879988258797812119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214694965013302023460832317 80510611879988258797812119)
      ·
        refine ⟨120765917819982388196718179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80510611879988258797812119 120765917819982388196718179)
        ·
          refine ⟨181148876729973582295077269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120765917819982388196718179 181148876729973582295077269)
          ·
            refine ⟨8491353596717511670081747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 181148876729973582295077269 8491353596717511670081747)
            ·
              refine ⟨12737030395076267505122621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8491353596717511670081747 12737030395076267505122621)
              ·
                refine ⟨4776386398153600314420983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12737030395076267505122621 4776386398153600314420983)
                ·
                  refine ⟨7164579597230400471631475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4776386398153600314420983 7164579597230400471631475)
                  ·
                    refine ⟨10746869395845600707447213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7164579597230400471631475 10746869395845600707447213)
                    ·
                      refine ⟨4030076023442100265292705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10746869395845600707447213 4030076023442100265292705)
                      ·
                        rfl

theorem cell23_7848545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 1, 3, 1, 1, 3].length) (baseStart_7848545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7848545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7848545 prefixEnd_7848545 := by exact prefixLift 7848545
  have htrace : WordTrace (prefixWord ++ tailWord_7848545) baseStart_7848545 baseEnd_7848545 := by
    simpa [prefixWord, tailWord_7848545, baseEnd_7848545] using wordTrace_append hprefix tailTrace_7848545
  have hstable : (prefixWord ++ tailWord_7848545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7848545).length < 2 ^ (prefixWord ++ tailWord_7848545).sum := by decide
  have hdescent : baseEnd_7848545 < baseStart_7848545 := by decide
  rcases family_descends (prefixWord ++ tailWord_7848545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7848562 : List Nat := [3, 2, 1, 2, 4, 1, 3, 2, 1, 1, 3]
def baseStart_7848562 : Nat := 118140960795 + 7848562 * 2 ^ 59
def prefixEnd_7848562 : Nat := 4983230072969 + 3 ^ 40 * 7848562 * 2
def baseEnd_7848562 : Nat := 4030084752613226698780127

theorem tailTrace_7848562 : CollatzResearch.WordTrace tailWord_7848562 prefixEnd_7848562 4030084752613226698780127 := by
  unfold tailWord_7848562
  simp only [CollatzResearch.WordTrace]
  refine ⟨71565143348001944129452985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190840382261338517678541293 71565143348001944129452985)
  ·
    refine ⟨53673857511001458097089739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71565143348001944129452985 53673857511001458097089739)
    ·
      refine ⟨80510786266502187145634609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53673857511001458097089739 80510786266502187145634609)
      ·
        refine ⟨60383089699876640359225957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80510786266502187145634609 60383089699876640359225957)
        ·
          refine ⟨11321829318726870067354867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60383089699876640359225957 11321829318726870067354867)
          ·
            refine ⟨16982743978090305101032301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11321829318726870067354867 16982743978090305101032301)
            ·
              refine ⟨6368528991783864412887113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16982743978090305101032301 6368528991783864412887113)
              ·
                refine ⟨4776396743837898309665335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6368528991783864412887113 4776396743837898309665335)
                ·
                  refine ⟨7164595115756847464498003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4776396743837898309665335 7164595115756847464498003)
                  ·
                    refine ⟨10746892673635271196747005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7164595115756847464498003 10746892673635271196747005)
                    ·
                      refine ⟨4030084752613226698780127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10746892673635271196747005 4030084752613226698780127)
                      ·
                        rfl

theorem cell23_7848562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 3, 2, 1, 1, 3].length) (baseStart_7848562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7848562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7848562 prefixEnd_7848562 := by exact prefixLift 7848562
  have htrace : WordTrace (prefixWord ++ tailWord_7848562) baseStart_7848562 baseEnd_7848562 := by
    simpa [prefixWord, tailWord_7848562, baseEnd_7848562] using wordTrace_append hprefix tailTrace_7848562
  have hstable : (prefixWord ++ tailWord_7848562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7848562).length < 2 ^ (prefixWord ++ tailWord_7848562).sum := by decide
  have hdescent : baseEnd_7848562 < baseStart_7848562 := by decide
  rcases family_descends (prefixWord ++ tailWord_7848562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7848587 : List Nat := [1, 1, 1, 1, 4, 1, 2, 1, 4, 7]
def baseStart_7848587 : Nat := 118140960795 + 7848587 * 2 ^ 59
def prefixEnd_7848587 : Nat := 4983230072969 + 3 ^ 40 * 7848587 * 2
def baseEnd_7848587 : Nat := 1343365863209863033655837

theorem tailTrace_7848587 : CollatzResearch.WordTrace tailWord_7848587 prefixEnd_7848587 1343365863209863033655837 := by
  unfold tailWord_7848587
  simp only [CollatzResearch.WordTrace]
  refine ⟨286261485216917205787472015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190840990144611470524981343 286261485216917205787472015)
  ·
    refine ⟨429392227825375808681208023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286261485216917205787472015 429392227825375808681208023)
    ·
      refine ⟨644088341738063713021812035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 429392227825375808681208023 644088341738063713021812035)
      ·
        refine ⟨966132512607095569532718053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 644088341738063713021812035 966132512607095569532718053)
        ·
          refine ⟨181149846113830419287384635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 966132512607095569532718053 181149846113830419287384635)
          ·
            refine ⟨271724769170745628931076953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181149846113830419287384635 271724769170745628931076953)
            ·
              refine ⟨203793576878059221698307715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 271724769170745628931076953 203793576878059221698307715)
              ·
                refine ⟨305690365317088832547461573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 203793576878059221698307715 305690365317088832547461573)
                ·
                  refine ⟨57316943496954156102649045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 305690365317088832547461573 57316943496954156102649045)
                  ·
                    refine ⟨1343365863209863033655837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57316943496954156102649045 1343365863209863033655837)
                    ·
                      rfl

theorem cell23_7848587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 4, 7].length) (baseStart_7848587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7848587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7848587 prefixEnd_7848587 := by exact prefixLift 7848587
  have htrace : WordTrace (prefixWord ++ tailWord_7848587) baseStart_7848587 baseEnd_7848587 := by
    simpa [prefixWord, tailWord_7848587, baseEnd_7848587] using wordTrace_append hprefix tailTrace_7848587
  have hstable : (prefixWord ++ tailWord_7848587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7848587).length < 2 ^ (prefixWord ++ tailWord_7848587).sum := by decide
  have hdescent : baseEnd_7848587 < baseStart_7848587 := by decide
  rcases family_descends (prefixWord ++ tailWord_7848587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7848634 : List Nat := [3, 1, 1, 1, 2, 3, 3, 1, 2, 6]
def baseStart_7848634 : Nat := 118140960795 + 7848634 * 2 ^ 59
def prefixEnd_7848634 : Nat := 4983230072969 + 3 ^ 40 * 7848634 * 2
def baseEnd_7848634 : Nat := 1343373907740116805693265

theorem tailTrace_7848634 : CollatzResearch.WordTrace tailWord_7848634 prefixEnd_7848634 1343373907740116805693265 := by
  unfold tailWord_7848634
  simp only [CollatzResearch.WordTrace]
  refine ⟨71565799861936733203608239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190842132965164621876288637 71565799861936733203608239)
  ·
    refine ⟨107348699792905099805412359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71565799861936733203608239 107348699792905099805412359)
    ·
      refine ⟨161023049689357649708118539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107348699792905099805412359 161023049689357649708118539)
      ·
        refine ⟨241534574534036474562177809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161023049689357649708118539 241534574534036474562177809)
        ·
          refine ⟨181150930900527355921633357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 241534574534036474562177809 181150930900527355921633357)
          ·
            refine ⟨67931599087697758470612509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 181150930900527355921633357 67931599087697758470612509)
            ·
              refine ⟨25474349657886659426479691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67931599087697758470612509 25474349657886659426479691)
              ·
                refine ⟨38211524486829989139719537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25474349657886659426479691 38211524486829989139719537)
                ·
                  refine ⟨28658643365122491854789653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38211524486829989139719537 28658643365122491854789653)
                  ·
                    refine ⟨1343373907740116805693265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28658643365122491854789653 1343373907740116805693265)
                    ·
                      rfl

theorem cell23_7848634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 1, 2, 6].length) (baseStart_7848634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7848634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7848634 prefixEnd_7848634 := by exact prefixLift 7848634
  have htrace : WordTrace (prefixWord ++ tailWord_7848634) baseStart_7848634 baseEnd_7848634 := by
    simpa [prefixWord, tailWord_7848634, baseEnd_7848634] using wordTrace_append hprefix tailTrace_7848634
  have hstable : (prefixWord ++ tailWord_7848634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7848634).length < 2 ^ (prefixWord ++ tailWord_7848634).sum := by decide
  have hdescent : baseEnd_7848634 < baseStart_7848634 := by decide
  rcases family_descends (prefixWord ++ tailWord_7848634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7848675 : List Nat := [1, 1, 1, 7, 1, 2, 1, 1, 4, 2, 2]
def baseStart_7848675 : Nat := 118140960795 + 7848675 * 2 ^ 59
def prefixEnd_7848675 : Nat := 4983230072969 + 3 ^ 40 * 7848675 * 2
def baseEnd_7848675 : Nat := 4030142775927184756667107

theorem tailTrace_7848675 : CollatzResearch.WordTrace tailWord_7848675 prefixEnd_7848675 4030142775927184756667107 := by
  unfold tailWord_7848675
  simp only [CollatzResearch.WordTrace]
  refine ⟨286264694840598396816675479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190843129893732264544450319 286264694840598396816675479)
  ·
    refine ⟨429397042260897595225013219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286264694840598396816675479 429397042260897595225013219)
    ·
      refine ⟨644095563391346392837519829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 429397042260897595225013219 644095563391346392837519829)
      ·
        refine ⟨15095989766984681082129371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 644095563391346392837519829 15095989766984681082129371)
        ·
          refine ⟨22643984650477021623194057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15095989766984681082129371 22643984650477021623194057)
          ·
            refine ⟨16982988487857766217395543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22643984650477021623194057 16982988487857766217395543)
            ·
              refine ⟨25474482731786649326093315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16982988487857766217395543 25474482731786649326093315)
              ·
                refine ⟨38211724097679973989139973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25474482731786649326093315 38211724097679973989139973)
                ·
                  refine ⟨7164698268314995122963745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38211724097679973989139973 7164698268314995122963745)
                  ·
                    refine ⟨5373523701236246342222809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7164698268314995122963745 5373523701236246342222809)
                    ·
                      refine ⟨4030142775927184756667107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5373523701236246342222809 4030142775927184756667107)
                      ·
                        rfl

theorem cell23_7848675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 1, 4, 2, 2].length) (baseStart_7848675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7848675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7848675 prefixEnd_7848675 := by exact prefixLift 7848675
  have htrace : WordTrace (prefixWord ++ tailWord_7848675) baseStart_7848675 baseEnd_7848675 := by
    simpa [prefixWord, tailWord_7848675, baseEnd_7848675] using wordTrace_append hprefix tailTrace_7848675
  have hstable : (prefixWord ++ tailWord_7848675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7848675).length < 2 ^ (prefixWord ++ tailWord_7848675).sum := by decide
  have hdescent : baseEnd_7848675 < baseStart_7848675 := by decide
  rcases family_descends (prefixWord ++ tailWord_7848675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7848681 : List Nat := [1, 2, 1, 1, 1, 2, 6, 4, 5]
def baseStart_7848681 : Nat := 118140960795 + 7848681 * 2 ^ 59
def prefixEnd_7848681 : Nat := 4983230072969 + 3 ^ 40 * 7848681 * 2
def baseEnd_7848681 : Nat := 447793984090123525910231

theorem tailTrace_7848681 : CollatzResearch.WordTrace tailWord_7848681 prefixEnd_7848681 447793984090123525910231 := by
  unfold tailWord_7848681
  simp only [CollatzResearch.WordTrace]
  refine ⟨286264913678576659841393897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190843275785717773227595931 286264913678576659841393897)
  ·
    refine ⟨214698685258932494881045423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286264913678576659841393897 214698685258932494881045423)
    ·
      refine ⟨322048027888398742321568135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214698685258932494881045423 322048027888398742321568135)
      ·
        refine ⟨483072041832598113482352203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322048027888398742321568135 483072041832598113482352203)
        ·
          refine ⟨724608062748897170223528305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 483072041832598113482352203 724608062748897170223528305)
          ·
            refine ⟨543456047061672877667646229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 724608062748897170223528305 543456047061672877667646229)
            ·
              refine ⟨25474502206015916140670917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 543456047061672877667646229 25474502206015916140670917)
              ·
                refine ⟨4776469163627984276375797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25474502206015916140670917 4776469163627984276375797)
                ·
                  refine ⟨447793984090123525910231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4776469163627984276375797 447793984090123525910231)
                  ·
                    rfl

theorem cell23_7848681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 4, 5].length) (baseStart_7848681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7848681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7848681 prefixEnd_7848681 := by exact prefixLift 7848681
  have htrace : WordTrace (prefixWord ++ tailWord_7848681) baseStart_7848681 baseEnd_7848681 := by
    simpa [prefixWord, tailWord_7848681, baseEnd_7848681] using wordTrace_append hprefix tailTrace_7848681
  have hstable : (prefixWord ++ tailWord_7848681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7848681).length < 2 ^ (prefixWord ++ tailWord_7848681).sum := by decide
  have hdescent : baseEnd_7848681 < baseStart_7848681 := by decide
  rcases family_descends (prefixWord ++ tailWord_7848681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7848711 : List Nat := [1, 1, 4, 4, 1, 1, 2, 1, 1, 7]
def baseStart_7848711 : Nat := 118140960795 + 7848711 * 2 ^ 59
def prefixEnd_7848711 : Nat := 4983230072969 + 3 ^ 40 * 7848711 * 2
def baseEnd_7848711 : Nat := 1343387087076915538605647

theorem tailTrace_7848711 : CollatzResearch.WordTrace tailWord_7848711 prefixEnd_7848711 1343387087076915538605647 := by
  unfold tailWord_7848711
  simp only [CollatzResearch.WordTrace]
  refine ⟨286266007868467974964985987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190844005245645316643323991 286266007868467974964985987)
  ·
    refine ⟨429399011802701962447478981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286266007868467974964985987 429399011802701962447478981)
    ·
      refine ⟨80512314713006617958902309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 429399011802701962447478981 80512314713006617958902309)
      ·
        refine ⟨15096059008688740867294183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80512314713006617958902309 15096059008688740867294183)
        ·
          refine ⟨22644088513033111300941275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15096059008688740867294183 22644088513033111300941275)
          ·
            refine ⟨33966132769549666951411913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22644088513033111300941275 33966132769549666951411913)
            ·
              refine ⟨25474599577162250213558935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33966132769549666951411913 25474599577162250213558935)
              ·
                refine ⟨38211899365743375320338403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25474599577162250213558935 38211899365743375320338403)
                ·
                  refine ⟨57317849048615062980507605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38211899365743375320338403 57317849048615062980507605)
                  ·
                    refine ⟨1343387087076915538605647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57317849048615062980507605 1343387087076915538605647)
                    ·
                      rfl

theorem cell23_7848711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 1, 1, 7].length) (baseStart_7848711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7848711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7848711 prefixEnd_7848711 := by exact prefixLift 7848711
  have htrace : WordTrace (prefixWord ++ tailWord_7848711) baseStart_7848711 baseEnd_7848711 := by
    simpa [prefixWord, tailWord_7848711, baseEnd_7848711] using wordTrace_append hprefix tailTrace_7848711
  have hstable : (prefixWord ++ tailWord_7848711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7848711).length < 2 ^ (prefixWord ++ tailWord_7848711).sum := by decide
  have hdescent : baseEnd_7848711 < baseStart_7848711 := by decide
  rcases family_descends (prefixWord ++ tailWord_7848711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7848765 : List Nat := [1, 4, 1, 4, 2, 1, 2, 1, 2, 1, 4]
def baseStart_7848765 : Nat := 118140960795 + 7848765 * 2 ^ 59
def prefixEnd_7848765 : Nat := 4983230072969 + 3 ^ 40 * 7848765 * 2
def baseEnd_7848765 : Nat := 4030188989186089404541693

theorem tailTrace_7848765 : CollatzResearch.WordTrace tailWord_7848765 prefixEnd_7848765 4030188989186089404541693 := by
  unfold tailWord_7848765
  simp only [CollatzResearch.WordTrace]
  refine ⟨286267977410272342187451749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190845318273514894791634499 286267977410272342187451749)
  ·
    refine ⟨53675245764426064160147203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 286267977410272342187451749 53675245764426064160147203)
    ·
      refine ⟨80512868646639096240220805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53675245764426064160147203 80512868646639096240220805)
      ·
        refine ⟨15096162871244830545041401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80512868646639096240220805 15096162871244830545041401)
        ·
          refine ⟨11322122153433622908781051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15096162871244830545041401 11322122153433622908781051)
          ·
            refine ⟨16983183230150434363171577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11322122153433622908781051 16983183230150434363171577)
            ·
              refine ⟨12737387422612825772378683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16983183230150434363171577 12737387422612825772378683)
              ·
                refine ⟨19106081133919238658568025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12737387422612825772378683 19106081133919238658568025)
                ·
                  refine ⟨14329560850439428993926019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19106081133919238658568025 14329560850439428993926019)
                  ·
                    refine ⟨21494341275659143490889029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14329560850439428993926019 21494341275659143490889029)
                    ·
                      refine ⟨4030188989186089404541693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21494341275659143490889029 4030188989186089404541693)
                      ·
                        rfl

theorem cell23_7848765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_7848765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7848765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7848765 prefixEnd_7848765 := by exact prefixLift 7848765
  have htrace : WordTrace (prefixWord ++ tailWord_7848765) baseStart_7848765 baseEnd_7848765 := by
    simpa [prefixWord, tailWord_7848765, baseEnd_7848765] using wordTrace_append hprefix tailTrace_7848765
  have hstable : (prefixWord ++ tailWord_7848765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7848765).length < 2 ^ (prefixWord ++ tailWord_7848765).sum := by decide
  have hdescent : baseEnd_7848765 < baseStart_7848765 := by decide
  rcases family_descends (prefixWord ++ tailWord_7848765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7848825 : List Nat := [1, 2, 1, 3, 2, 3, 3, 1, 2, 3, 2]
def baseStart_7848825 : Nat := 118140960795 + 7848825 * 2 ^ 59
def prefixEnd_7848825 : Nat := 4983230072969 + 3 ^ 40 * 7848825 * 2
def baseEnd_7848825 : Nat := 4030219798025359169791417

theorem tailTrace_7848825 : CollatzResearch.WordTrace tailWord_7848825 prefixEnd_7848825 4030219798025359169791417 := by
  unfold tailWord_7848825
  simp only [CollatzResearch.WordTrace]
  refine ⟨286270165790054972434635929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190846777193369981623090619 286270165790054972434635929)
  ·
    refine ⟨214702624342541229325976947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286270165790054972434635929 214702624342541229325976947)
    ·
      refine ⟨322053936513811843988965421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214702624342541229325976947 322053936513811843988965421)
      ·
        refine ⟨120770226192679441495862033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 322053936513811843988965421 120770226192679441495862033)
        ·
          refine ⟨90577669644509581121896525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120770226192679441495862033 90577669644509581121896525)
          ·
            refine ⟨33966626116691092920711197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90577669644509581121896525 33966626116691092920711197)
            ·
              refine ⟨12737484793759159845266699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33966626116691092920711197 12737484793759159845266699)
              ·
                refine ⟨19106227190638739767900049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12737484793759159845266699 19106227190638739767900049)
                ·
                  refine ⟨14329670392979054825925037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19106227190638739767900049 14329670392979054825925037)
                  ·
                    refine ⟨5373626397367145559721889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14329670392979054825925037 5373626397367145559721889)
                    ·
                      refine ⟨4030219798025359169791417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5373626397367145559721889 4030219798025359169791417)
                      ·
                        rfl

theorem cell23_7848825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 3, 1, 2, 3, 2].length) (baseStart_7848825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7848825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7848825 prefixEnd_7848825 := by exact prefixLift 7848825
  have htrace : WordTrace (prefixWord ++ tailWord_7848825) baseStart_7848825 baseEnd_7848825 := by
    simpa [prefixWord, tailWord_7848825, baseEnd_7848825] using wordTrace_append hprefix tailTrace_7848825
  have hstable : (prefixWord ++ tailWord_7848825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7848825).length < 2 ^ (prefixWord ++ tailWord_7848825).sum := by decide
  have hdescent : baseEnd_7848825 < baseStart_7848825 := by decide
  rcases family_descends (prefixWord ++ tailWord_7848825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7848831 : List Nat := [1, 1, 2, 2, 1, 1, 6, 2, 1, 6]
def baseStart_7848831 : Nat := 118140960795 + 7848831 * 2 ^ 59
def prefixEnd_7848831 : Nat := 4983230072969 + 3 ^ 40 * 7848831 * 2
def baseEnd_7848831 : Nat := 1343407626303095382105463

theorem tailTrace_7848831 : CollatzResearch.WordTrace tailWord_7848831 prefixEnd_7848831 1343407626303095382105463 := by
  unfold tailWord_7848831
  simp only [CollatzResearch.WordTrace]
  refine ⟨286270384628033235459354347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190846923085355490306236231 286270384628033235459354347)
  ·
    refine ⟨429405576942049853189031521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286270384628033235459354347 429405576942049853189031521)
    ·
      refine ⟨322054182706537389891773641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 429405576942049853189031521 322054182706537389891773641)
      ·
        refine ⟨241540637029903042418830231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 322054182706537389891773641 241540637029903042418830231)
        ·
          refine ⟨362310955544854563628245347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241540637029903042418830231 362310955544854563628245347)
          ·
            refine ⟨543466433317281845442368021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 362310955544854563628245347 543466433317281845442368021)
            ·
              refine ⟨25474989061747586505111001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 543466433317281845442368021 25474989061747586505111001)
              ·
                refine ⟨19106241796310689878833251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25474989061747586505111001 19106241796310689878833251)
                ·
                  refine ⟨28659362694466034818249877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19106241796310689878833251 28659362694466034818249877)
                  ·
                    refine ⟨1343407626303095382105463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28659362694466034818249877 1343407626303095382105463)
                    ·
                      rfl

theorem cell23_7848831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 2, 1, 6].length) (baseStart_7848831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7848831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7848831 prefixEnd_7848831 := by exact prefixLift 7848831
  have htrace : WordTrace (prefixWord ++ tailWord_7848831) baseStart_7848831 baseEnd_7848831 := by
    simpa [prefixWord, tailWord_7848831, baseEnd_7848831] using wordTrace_append hprefix tailTrace_7848831
  have hstable : (prefixWord ++ tailWord_7848831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7848831).length < 2 ^ (prefixWord ++ tailWord_7848831).sum := by decide
  have hdescent : baseEnd_7848831 < baseStart_7848831 := by decide
  rcases family_descends (prefixWord ++ tailWord_7848831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7848861 : List Nat := [1, 4, 2, 1, 2, 1, 2, 10]
def baseStart_7848861 : Nat := 118140960795 + 7848861 * 2 ^ 59
def prefixEnd_7848861 : Nat := 4983230072969 + 3 ^ 40 * 7848861 * 2
def baseEnd_7848861 : Nat := 149268084567737815886713

theorem tailTrace_7848861 : CollatzResearch.WordTrace tailWord_7848861 prefixEnd_7848861 149268084567737815886713 := by
  unfold tailWord_7848861
  simp only [CollatzResearch.WordTrace]
  refine ⟨286271478817924550582946437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190847652545283033721964291 286271478817924550582946437)
  ·
    refine ⟨53675902278360853234302457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 286271478817924550582946437 53675902278360853234302457)
    ·
      refine ⟨40256926708770639925726843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53675902278360853234302457 40256926708770639925726843)
      ·
        refine ⟨60385390063155959888590265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40256926708770639925726843 60385390063155959888590265)
        ·
          refine ⟨45289042547366969916442699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60385390063155959888590265 45289042547366969916442699)
          ·
            refine ⟨67933563821050454874664049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45289042547366969916442699 67933563821050454874664049)
            ·
              refine ⟨50950172865787841155998037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67933563821050454874664049 50950172865787841155998037)
              ·
                refine ⟨149268084567737815886713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 50950172865787841155998037 149268084567737815886713)
                ·
                  rfl

theorem cell23_7848861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 10].length) (baseStart_7848861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7848861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7848861 prefixEnd_7848861 := by exact prefixLift 7848861
  have htrace : WordTrace (prefixWord ++ tailWord_7848861) baseStart_7848861 baseEnd_7848861 := by
    simpa [prefixWord, tailWord_7848861, baseEnd_7848861] using wordTrace_append hprefix tailTrace_7848861
  have hstable : (prefixWord ++ tailWord_7848861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7848861).length < 2 ^ (prefixWord ++ tailWord_7848861).sum := by decide
  have hdescent : baseEnd_7848861 < baseStart_7848861 := by decide
  rcases family_descends (prefixWord ++ tailWord_7848861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7848865 : List Nat := [1, 2, 3, 4, 1, 3, 1, 1, 1, 6]
def baseStart_7848865 : Nat := 118140960795 + 7848865 * 2 ^ 59
def prefixEnd_7848865 : Nat := 4983230072969 + 3 ^ 40 * 7848865 * 2
def baseEnd_7848865 : Nat := 1343413445750513004430411

theorem tailTrace_7848865 : CollatzResearch.WordTrace tailWord_7848865 prefixEnd_7848865 1343413445750513004430411 := by
  unfold tailWord_7848865
  simp only [CollatzResearch.WordTrace]
  refine ⟨286271624709910059266092049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190847749806606706177394699 286271624709910059266092049)
  ·
    refine ⟨214703718532432544449569037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286271624709910059266092049 214703718532432544449569037)
    ·
      refine ⟨80513894449662204168588389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214703718532432544449569037 80513894449662204168588389)
      ·
        refine ⟨15096355209311663281610323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80513894449662204168588389 15096355209311663281610323)
        ·
          refine ⟨22644532813967494922415485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15096355209311663281610323 22644532813967494922415485)
          ·
            refine ⟨8491699805237810595905807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22644532813967494922415485 8491699805237810595905807)
            ·
              refine ⟨12737549707856715893858711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8491699805237810595905807 12737549707856715893858711)
              ·
                refine ⟨19106324561785073840788067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12737549707856715893858711 19106324561785073840788067)
                ·
                  refine ⟨28659486842677610761182101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19106324561785073840788067 28659486842677610761182101)
                  ·
                    refine ⟨1343413445750513004430411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28659486842677610761182101 1343413445750513004430411)
                    ·
                      rfl

theorem cell23_7848865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 1, 1, 1, 6].length) (baseStart_7848865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7848865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7848865 prefixEnd_7848865 := by exact prefixLift 7848865
  have htrace : WordTrace (prefixWord ++ tailWord_7848865) baseStart_7848865 baseEnd_7848865 := by
    simpa [prefixWord, tailWord_7848865, baseEnd_7848865] using wordTrace_append hprefix tailTrace_7848865
  have hstable : (prefixWord ++ tailWord_7848865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7848865).length < 2 ^ (prefixWord ++ tailWord_7848865).sum := by decide
  have hdescent : baseEnd_7848865 < baseStart_7848865 := by decide
  rcases family_descends (prefixWord ++ tailWord_7848865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7848889 : List Nat := [1, 2, 1, 4, 2, 2, 3, 3, 1, 2, 2]
def baseStart_7848889 : Nat := 118140960795 + 7848889 * 2 ^ 59
def prefixEnd_7848889 : Nat := 4983230072969 + 3 ^ 40 * 7848889 * 2
def baseEnd_7848889 : Nat := 4030252660787246919391123

theorem tailTrace_7848889 : CollatzResearch.WordTrace tailWord_7848889 prefixEnd_7848889 4030252660787246919391123 := by
  unfold tailWord_7848889
  simp only [CollatzResearch.WordTrace]
  refine ⟨286272500061823111364965721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190848333374548740909977147 286272500061823111364965721)
  ·
    refine ⟨214704375046367333523724291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286272500061823111364965721 214704375046367333523724291)
    ·
      refine ⟨322056562569551000285586437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214704375046367333523724291 322056562569551000285586437)
      ·
        refine ⟨60385605481790812553547457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 322056562569551000285586437 60385605481790812553547457)
        ·
          refine ⟨45289204111343109415160593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60385605481790812553547457 45289204111343109415160593)
          ·
            refine ⟨33966903083507332061370445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45289204111343109415160593 33966903083507332061370445)
            ·
              refine ⟨12737588656315249523013917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33966903083507332061370445 12737588656315249523013917)
              ·
                refine ⟨4776595746118218571130219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12737588656315249523013917 4776595746118218571130219)
                ·
                  refine ⟨7164893619177327856695329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4776595746118218571130219 7164893619177327856695329)
                  ·
                    refine ⟨5373670214382995892521497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7164893619177327856695329 5373670214382995892521497)
                    ·
                      refine ⟨4030252660787246919391123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5373670214382995892521497 4030252660787246919391123)
                      ·
                        rfl

theorem cell23_7848889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 3, 3, 1, 2, 2].length) (baseStart_7848889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7848889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7848889 prefixEnd_7848889 := by exact prefixLift 7848889
  have htrace : WordTrace (prefixWord ++ tailWord_7848889) baseStart_7848889 baseEnd_7848889 := by
    simpa [prefixWord, tailWord_7848889, baseEnd_7848889] using wordTrace_append hprefix tailTrace_7848889
  have hstable : (prefixWord ++ tailWord_7848889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7848889).length < 2 ^ (prefixWord ++ tailWord_7848889).sum := by decide
  have hdescent : baseEnd_7848889 < baseStart_7848889 := by decide
  rcases family_descends (prefixWord ++ tailWord_7848889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7848922 : List Nat := [3, 1, 1, 2, 4, 2, 1, 3, 2, 1, 3]
def baseStart_7848922 : Nat := 118140960795 + 7848922 * 2 ^ 59
def prefixEnd_7848922 : Nat := 4983230072969 + 3 ^ 40 * 7848922 * 2
def baseEnd_7848922 : Nat := 4030269605648845290278471

theorem tailTrace_7848922 : CollatzResearch.WordTrace tailWord_7848922 prefixEnd_7848922 4030269605648845290278471 := by
  unfold tailWord_7848922
  simp only [CollatzResearch.WordTrace]
  refine ⟨71568425917675889500229255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190849135780469038667278013 71568425917675889500229255)
  ·
    refine ⟨107352638876513834250343883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71568425917675889500229255 107352638876513834250343883)
    ·
      refine ⟨161028958314770751375515825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107352638876513834250343883 161028958314770751375515825)
      ·
        refine ⟨120771718736078063531636869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161028958314770751375515825 120771718736078063531636869)
        ·
          refine ⟨22644697263014636912181913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 120771718736078063531636869 22644697263014636912181913)
          ·
            refine ⟨16983522947260977684136435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22644697263014636912181913 16983522947260977684136435)
            ·
              refine ⟨25475284420891466526204653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16983522947260977684136435 25475284420891466526204653)
              ·
                refine ⟨9553231657834299947326745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25475284420891466526204653 9553231657834299947326745)
                ·
                  refine ⟨7164923743375724960495059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9553231657834299947326745 7164923743375724960495059)
                  ·
                    refine ⟨10747385615063587440742589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7164923743375724960495059 10747385615063587440742589)
                    ·
                      refine ⟨4030269605648845290278471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10747385615063587440742589 4030269605648845290278471)
                      ·
                        rfl

theorem cell23_7848922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 3, 2, 1, 3].length) (baseStart_7848922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7848922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7848922 prefixEnd_7848922 := by exact prefixLift 7848922
  have htrace : WordTrace (prefixWord ++ tailWord_7848922) baseStart_7848922 baseEnd_7848922 := by
    simpa [prefixWord, tailWord_7848922, baseEnd_7848922] using wordTrace_append hprefix tailTrace_7848922
  have hstable : (prefixWord ++ tailWord_7848922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7848922).length < 2 ^ (prefixWord ++ tailWord_7848922).sum := by decide
  have hdescent : baseEnd_7848922 < baseStart_7848922 := by decide
  rcases family_descends (prefixWord ++ tailWord_7848922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7848945 : List Nat := [1, 2, 2, 2, 4, 1, 1, 1, 3, 4, 2]
def baseStart_7848945 : Nat := 118140960795 + 7848945 * 2 ^ 59
def prefixEnd_7848945 : Nat := 4983230072969 + 3 ^ 40 * 7848945 * 2
def baseEnd_7848945 : Nat := 4030281415703898700290865

theorem tailTrace_7848945 : CollatzResearch.WordTrace tailWord_7848945 prefixEnd_7848945 4030281415703898700290865 := by
  unfold tailWord_7848945
  simp only [CollatzResearch.WordTrace]
  refine ⟨286274542549620232929004289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190849695033080155286002859 286274542549620232929004289)
  ·
    refine ⟨214705906912215174696753217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286274542549620232929004289 214705906912215174696753217)
    ·
      refine ⟨161029430184161381022564913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214705906912215174696753217 161029430184161381022564913)
      ·
        refine ⟨120772072638121035766923685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161029430184161381022564913 120772072638121035766923685)
        ·
          refine ⟨22644763619647694206298191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 120772072638121035766923685 22644763619647694206298191)
          ·
            refine ⟨33967145429471541309447287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22644763619647694206298191 33967145429471541309447287)
            ·
              refine ⟨50950718144207311964170931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33967145429471541309447287 50950718144207311964170931)
              ·
                refine ⟨76426077216310967946256397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50950718144207311964170931 76426077216310967946256397)
                ·
                  refine ⟨28659778956116612979846149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76426077216310967946256397 28659778956116612979846149)
                  ·
                    refine ⟨5373708554271864933721153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28659778956116612979846149 5373708554271864933721153)
                    ·
                      refine ⟨4030281415703898700290865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5373708554271864933721153 4030281415703898700290865)
                      ·
                        rfl

theorem cell23_7848945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 1, 3, 4, 2].length) (baseStart_7848945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7848945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7848945 prefixEnd_7848945 := by exact prefixLift 7848945
  have htrace : WordTrace (prefixWord ++ tailWord_7848945) baseStart_7848945 baseEnd_7848945 := by
    simpa [prefixWord, tailWord_7848945, baseEnd_7848945] using wordTrace_append hprefix tailTrace_7848945
  have hstable : (prefixWord ++ tailWord_7848945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7848945).length < 2 ^ (prefixWord ++ tailWord_7848945).sum := by decide
  have hdescent : baseEnd_7848945 < baseStart_7848945 := by decide
  rcases family_descends (prefixWord ++ tailWord_7848945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7849012 : List Nat := [2, 5, 1, 2, 1, 1, 1, 2, 2, 3, 3]
def baseStart_7849012 : Nat := 118140960795 + 7849012 * 2 ^ 59
def prefixEnd_7849012 : Nat := 4983230072969 + 3 ^ 40 * 7849012 * 2
def baseEnd_7849012 : Nat := 4030315818907749938153057

theorem tailTrace_7849012 : CollatzResearch.WordTrace tailWord_7849012 prefixEnd_7849012 4030315818907749938153057 := by
  unfold tailWord_7849012
  simp only [CollatzResearch.WordTrace]
  refine ⟨143138493120188751685846645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190851324160251668914462193 143138493120188751685846645)
  ·
    refine ⟨13419233730017695470548123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 143138493120188751685846645 13419233730017695470548123)
    ·
      refine ⟨20128850595026543205822185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13419233730017695470548123 20128850595026543205822185)
      ·
        refine ⟨15096637946269907404366639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20128850595026543205822185 15096637946269907404366639)
        ·
          refine ⟨22644956919404861106549959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15096637946269907404366639 22644956919404861106549959)
          ·
            refine ⟨33967435379107291659824939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22644956919404861106549959 33967435379107291659824939)
            ·
              refine ⟨50951153068660937489737409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33967435379107291659824939 50951153068660937489737409)
              ·
                refine ⟨38213364801495703117303057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50951153068660937489737409 38213364801495703117303057)
                ·
                  refine ⟨28660023601121777337977293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38213364801495703117303057 28660023601121777337977293)
                  ·
                    refine ⟨10747508850420666501741485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28660023601121777337977293 10747508850420666501741485)
                    ·
                      refine ⟨4030315818907749938153057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10747508850420666501741485 4030315818907749938153057)
                      ·
                        rfl

theorem cell23_7849012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_7849012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7849012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7849012 prefixEnd_7849012 := by exact prefixLift 7849012
  have htrace : WordTrace (prefixWord ++ tailWord_7849012) baseStart_7849012 baseEnd_7849012 := by
    simpa [prefixWord, tailWord_7849012, baseEnd_7849012] using wordTrace_append hprefix tailTrace_7849012
  have hstable : (prefixWord ++ tailWord_7849012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7849012).length < 2 ^ (prefixWord ++ tailWord_7849012).sum := by decide
  have hdescent : baseEnd_7849012 < baseStart_7849012 := by decide
  rcases family_descends (prefixWord ++ tailWord_7849012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7849045 : List Nat := [1, 3, 2, 2, 1, 2, 1, 4, 3, 4]
def baseStart_7849045 : Nat := 118140960795 + 7849045 * 2 ^ 59
def prefixEnd_7849045 : Nat := 4983230072969 + 3 ^ 40 * 7849045 * 2
def baseEnd_7849045 : Nat := 1343444254589782769680135

theorem tailTrace_7849045 : CollatzResearch.WordTrace tailWord_7849045 prefixEnd_7849045 1343444254589782769680135 := by
  unfold tailWord_7849045
  simp only [CollatzResearch.WordTrace]
  refine ⟨286278189849257950007644589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190852126566171966671763059 286278189849257950007644589)
  ·
    refine ⟨107354321193471731252866721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 286278189849257950007644589 107354321193471731252866721)
    ·
      refine ⟨80515740895103798439650041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107354321193471731252866721 80515740895103798439650041)
      ·
        refine ⟨60386805671327848829737531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80515740895103798439650041 60386805671327848829737531)
        ·
          refine ⟨90580208506991773244606297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60386805671327848829737531 90580208506991773244606297)
          ·
            refine ⟨67935156380243829933454723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90580208506991773244606297 67935156380243829933454723)
            ·
              refine ⟨101902734570365744900182085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67935156380243829933454723 101902734570365744900182085)
              ·
                refine ⟨19106762731943577168784141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 101902734570365744900182085 19106762731943577168784141)
                ·
                  refine ⟨7165036024478841438294053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19106762731943577168784141 7165036024478841438294053)
                  ·
                    refine ⟨1343444254589782769680135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7165036024478841438294053 1343444254589782769680135)
                    ·
                      rfl

theorem cell23_7849045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 4, 3, 4].length) (baseStart_7849045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7849045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7849045 prefixEnd_7849045 := by exact prefixLift 7849045
  have htrace : WordTrace (prefixWord ++ tailWord_7849045) baseStart_7849045 baseEnd_7849045 := by
    simpa [prefixWord, tailWord_7849045, baseEnd_7849045] using wordTrace_append hprefix tailTrace_7849045
  have hstable : (prefixWord ++ tailWord_7849045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7849045).length < 2 ^ (prefixWord ++ tailWord_7849045).sum := by decide
  have hdescent : baseEnd_7849045 < baseStart_7849045 := by decide
  rcases family_descends (prefixWord ++ tailWord_7849045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7849048 : List Nat := [2, 1, 2, 2, 1, 3, 1, 1, 2, 4, 4]
def baseStart_7849048 : Nat := 118140960795 + 7849048 * 2 ^ 59
def prefixEnd_7849048 : Nat := 4983230072969 + 3 ^ 40 * 7849048 * 2
def baseEnd_7849048 : Nat := 4030334304211311797302891

theorem tailTrace_7849048 : CollatzResearch.WordTrace tailWord_7849048 prefixEnd_7849048 4030334304211311797302891 := by
  unfold tailWord_7849048
  simp only [CollatzResearch.WordTrace]
  refine ⟨143139149634123540760001899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190852199512164721013335865 143139149634123540760001899)
  ·
    refine ⟨214708724451185311140002849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143139149634123540760001899 214708724451185311140002849)
    ·
      refine ⟨161031543338388983355002137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214708724451185311140002849 161031543338388983355002137)
      ·
        refine ⟨120773657503791737516251603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161031543338388983355002137 120773657503791737516251603)
        ·
          refine ⟨181160486255687606274377405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120773657503791737516251603 181160486255687606274377405)
          ·
            refine ⟨67935182345882852352891527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 181160486255687606274377405 67935182345882852352891527)
            ·
              refine ⟨101902773518824278529337291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67935182345882852352891527 101902773518824278529337291)
              ·
                refine ⟨152854160278236417794005937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101902773518824278529337291 152854160278236417794005937)
                ·
                  refine ⟨114640620208677313345504453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 152854160278236417794005937 114640620208677313345504453)
                  ·
                    refine ⟨21495116289126996252282085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 114640620208677313345504453 21495116289126996252282085)
                    ·
                      refine ⟨4030334304211311797302891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21495116289126996252282085 4030334304211311797302891)
                      ·
                        rfl

theorem cell23_7849048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 1, 2, 4, 4].length) (baseStart_7849048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7849048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7849048 prefixEnd_7849048 := by exact prefixLift 7849048
  have htrace : WordTrace (prefixWord ++ tailWord_7849048) baseStart_7849048 baseEnd_7849048 := by
    simpa [prefixWord, tailWord_7849048, baseEnd_7849048] using wordTrace_append hprefix tailTrace_7849048
  have hstable : (prefixWord ++ tailWord_7849048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7849048).length < 2 ^ (prefixWord ++ tailWord_7849048).sum := by decide
  have hdescent : baseEnd_7849048 < baseStart_7849048 := by decide
  rcases family_descends (prefixWord ++ tailWord_7849048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7849055 : List Nat := [1, 1, 2, 3, 1, 1, 4, 3, 2, 2, 3]
def baseStart_7849055 : Nat := 118140960795 + 7849055 * 2 ^ 59
def prefixEnd_7849055 : Nat := 4983230072969 + 3 ^ 40 * 7849055 * 2
def baseEnd_7849055 : Nat := 4030337898575893269915359

theorem tailTrace_7849055 : CollatzResearch.WordTrace tailWord_7849055 prefixEnd_7849055 4030337898575893269915359 := by
  unfold tailWord_7849055
  simp only [CollatzResearch.WordTrace]
  refine ⟨286278554579221721715508619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190852369719481147810339079 286278554579221721715508619)
  ·
    refine ⟨429417831868832582573262929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286278554579221721715508619 429417831868832582573262929)
    ·
      refine ⟨322063373901624436929947197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 429417831868832582573262929 322063373901624436929947197)
      ·
        refine ⟨120773765213109163848730199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 322063373901624436929947197 120773765213109163848730199)
        ·
          refine ⟨181160647819663745773095299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120773765213109163848730199 181160647819663745773095299)
          ·
            refine ⟨271740971729495618659642949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181160647819663745773095299 271740971729495618659642949)
            ·
              refine ⟨50951432199280428498683053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 271740971729495618659642949 50951432199280428498683053)
              ·
                refine ⟨19106787074730160687006145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50951432199280428498683053 19106787074730160687006145)
                ·
                  refine ⟨14330090306047620515254609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19106787074730160687006145 14330090306047620515254609)
                  ·
                    refine ⟨10747567729535715386440957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14330090306047620515254609 10747567729535715386440957)
                    ·
                      refine ⟨4030337898575893269915359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10747567729535715386440957 4030337898575893269915359)
                      ·
                        rfl

theorem cell23_7849055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 3, 2, 2, 3].length) (baseStart_7849055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7849055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7849055 prefixEnd_7849055 := by exact prefixLift 7849055
  have htrace : WordTrace (prefixWord ++ tailWord_7849055) baseStart_7849055 baseEnd_7849055 := by
    simpa [prefixWord, tailWord_7849055, baseEnd_7849055] using wordTrace_append hprefix tailTrace_7849055
  have hstable : (prefixWord ++ tailWord_7849055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7849055).length < 2 ^ (prefixWord ++ tailWord_7849055).sum := by decide
  have hdescent : baseEnd_7849055 < baseStart_7849055 := by decide
  rcases family_descends (prefixWord ++ tailWord_7849055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7849079 : List Nat := [1, 1, 3, 1, 1, 4, 5, 2, 1, 4]
def baseStart_7849079 : Nat := 118140960795 + 7849079 * 2 ^ 59
def prefixEnd_7849079 : Nat := 4983230072969 + 3 ^ 40 * 7849079 * 2
def baseEnd_7849079 : Nat := 1343450074037200392005083

theorem tailTrace_7849079 : CollatzResearch.WordTrace tailWord_7849079 prefixEnd_7849079 1343450074037200392005083 := by
  unfold tailWord_7849079
  simp only [CollatzResearch.WordTrace]
  refine ⟨286279429931134773814382291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190852953287423182542921527 286279429931134773814382291)
  ·
    refine ⟨429419144896702160721573437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286279429931134773814382291 429419144896702160721573437)
    ·
      refine ⟨161032179336263310270590039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 429419144896702160721573437 161032179336263310270590039)
      ·
        refine ⟨241548269004394965405885059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161032179336263310270590039 241548269004394965405885059)
        ·
          refine ⟨362322403506592448108827589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241548269004394965405885059 362322403506592448108827589)
          ·
            refine ⟨67935450657486084020405173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 362322403506592448108827589 67935450657486084020405173)
            ·
              refine ⟨6368948499139320376912985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67935450657486084020405173 6368948499139320376912985)
              ·
                refine ⟨4776711374354490282684739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6368948499139320376912985 4776711374354490282684739)
                ·
                  refine ⟨7165067061531735424027109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4776711374354490282684739 7165067061531735424027109)
                  ·
                    refine ⟨1343450074037200392005083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7165067061531735424027109 1343450074037200392005083)
                    ·
                      rfl

theorem cell23_7849079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 5, 2, 1, 4].length) (baseStart_7849079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7849079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7849079 prefixEnd_7849079 := by exact prefixLift 7849079
  have htrace : WordTrace (prefixWord ++ tailWord_7849079) baseStart_7849079 baseEnd_7849079 := by
    simpa [prefixWord, tailWord_7849079, baseEnd_7849079] using wordTrace_append hprefix tailTrace_7849079
  have hstable : (prefixWord ++ tailWord_7849079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7849079).length < 2 ^ (prefixWord ++ tailWord_7849079).sum := by decide
  have hdescent : baseEnd_7849079 < baseStart_7849079 := by decide
  rcases family_descends (prefixWord ++ tailWord_7849079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7849092 : List Nat := [2, 3, 2, 1, 2, 2, 4, 1, 6]
def baseStart_7849092 : Nat := 118140960795 + 7849092 * 2 ^ 59
def prefixEnd_7849092 : Nat := 4983230072969 + 3 ^ 40 * 7849092 * 2
def baseEnd_7849092 : Nat := 447817433040012180572521

theorem tailTrace_7849092 : CollatzResearch.WordTrace tailWord_7849092 prefixEnd_7849092 447817433040012180572521 := by
  unfold tailWord_7849092
  simp only [CollatzResearch.WordTrace]
  refine ⟨143139952040043838517302765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190853269386725118023070353 143139952040043838517302765)
  ·
    refine ⟨53677482015016439443988537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143139952040043838517302765 53677482015016439443988537)
    ·
      refine ⟨40258111511262329582991403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53677482015016439443988537 40258111511262329582991403)
      ·
        refine ⟨60387167266893494374487105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40258111511262329582991403 60387167266893494374487105)
        ·
          refine ⟨45290375450170120780865329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60387167266893494374487105 45290375450170120780865329)
          ·
            refine ⟨33967781587627590585648997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45290375450170120780865329 33967781587627590585648997)
            ·
              refine ⟨6368959047680173234809187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33967781587627590585648997 6368959047680173234809187)
              ·
                refine ⟨9553438571520259852213781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6368959047680173234809187 9553438571520259852213781)
                ·
                  refine ⟨447817433040012180572521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9553438571520259852213781 447817433040012180572521)
                  ·
                    rfl

theorem cell23_7849092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 4, 1, 6].length) (baseStart_7849092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7849092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7849092 prefixEnd_7849092 := by exact prefixLift 7849092
  have htrace : WordTrace (prefixWord ++ tailWord_7849092) baseStart_7849092 baseEnd_7849092 := by
    simpa [prefixWord, tailWord_7849092, baseEnd_7849092] using wordTrace_append hprefix tailTrace_7849092
  have hstable : (prefixWord ++ tailWord_7849092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7849092).length < 2 ^ (prefixWord ++ tailWord_7849092).sum := by decide
  have hdescent : baseEnd_7849092 < baseStart_7849092 := by decide
  rcases family_descends (prefixWord ++ tailWord_7849092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7849135 : List Nat := [1, 1, 2, 1, 2, 3, 2, 3, 4, 4]
def baseStart_7849135 : Nat := 118140960795 + 7849135 * 2 ^ 59
def prefixEnd_7849135 : Nat := 4983230072969 + 3 ^ 40 * 7849135 * 2
def baseEnd_7849135 : Nat := 1343459659009417652304997

theorem tailTrace_7849135 : CollatzResearch.WordTrace tailWord_7849135 prefixEnd_7849135 1343459659009417652304997 := by
  unfold tailWord_7849135
  simp only [CollatzResearch.WordTrace]
  refine ⟨286281472418931895378420859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190854314945954596918947239 286281472418931895378420859)
  ·
    refine ⟨429422208628397843067631289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286281472418931895378420859 429422208628397843067631289)
    ·
      refine ⟨322066656471298382300723467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 429422208628397843067631289 322066656471298382300723467)
      ·
        refine ⟨483099984706947573451085201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322066656471298382300723467 483099984706947573451085201)
        ·
          refine ⟨362324988530210680088313901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 483099984706947573451085201 362324988530210680088313901)
          ·
            refine ⟨135871870698829005033117713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 362324988530210680088313901 135871870698829005033117713)
            ·
              refine ⟨101903903024121753774838285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135871870698829005033117713 101903903024121753774838285)
              ·
                refine ⟨38213963634045657665564357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101903903024121753774838285 38213963634045657665564357)
                ·
                  refine ⟨7165118181383560812293317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38213963634045657665564357 7165118181383560812293317)
                  ·
                    refine ⟨1343459659009417652304997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7165118181383560812293317 1343459659009417652304997)
                    ·
                      rfl

theorem cell23_7849135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 3, 4, 4].length) (baseStart_7849135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7849135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7849135 prefixEnd_7849135 := by exact prefixLift 7849135
  have htrace : WordTrace (prefixWord ++ tailWord_7849135) baseStart_7849135 baseEnd_7849135 := by
    simpa [prefixWord, tailWord_7849135, baseEnd_7849135] using wordTrace_append hprefix tailTrace_7849135
  have hstable : (prefixWord ++ tailWord_7849135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7849135).length < 2 ^ (prefixWord ++ tailWord_7849135).sum := by decide
  have hdescent : baseEnd_7849135 < baseStart_7849135 := by decide
  rcases family_descends (prefixWord ++ tailWord_7849135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7849152 : List Nat := [2, 1, 1, 2, 6, 1, 2, 1, 1, 6]
def baseStart_7849152 : Nat := 118140960795 + 7849152 * 2 ^ 59
def prefixEnd_7849152 : Nat := 4983230072969 + 3 ^ 40 * 7849152 * 2
def baseEnd_7849152 : Nat := 1343462568733126463467471

theorem tailTrace_7849152 : CollatzResearch.WordTrace tailWord_7849152 prefixEnd_7849152 1343462568733126463467471 := by
  unfold tailWord_7849152
  simp only [CollatzResearch.WordTrace]
  refine ⟨143141046229935153640894855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190854728306580204854526473 143141046229935153640894855)
  ·
    refine ⟨214711569344902730461342283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143141046229935153640894855 214711569344902730461342283)
    ·
      refine ⟨322067354017354095692013425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214711569344902730461342283 322067354017354095692013425)
      ·
        refine ⟨241550515513015571769010069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 322067354017354095692013425 241550515513015571769010069)
        ·
          refine ⟨11322680414672604926672347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 241550515513015571769010069 11322680414672604926672347)
          ·
            refine ⟨16984020622008907390008521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11322680414672604926672347 16984020622008907390008521)
            ·
              refine ⟨12738015466506680542506391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16984020622008907390008521 12738015466506680542506391)
              ·
                refine ⟨19107023199760020813759587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12738015466506680542506391 19107023199760020813759587)
                ·
                  refine ⟨28660534799640031220639381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19107023199760020813759587 28660534799640031220639381)
                  ·
                    refine ⟨1343462568733126463467471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28660534799640031220639381 1343462568733126463467471)
                    ·
                      rfl

theorem cell23_7849152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 2, 1, 1, 6].length) (baseStart_7849152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7849152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7849152 prefixEnd_7849152 := by exact prefixLift 7849152
  have htrace : WordTrace (prefixWord ++ tailWord_7849152) baseStart_7849152 baseEnd_7849152 := by
    simpa [prefixWord, tailWord_7849152, baseEnd_7849152] using wordTrace_append hprefix tailTrace_7849152
  have hstable : (prefixWord ++ tailWord_7849152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7849152).length < 2 ^ (prefixWord ++ tailWord_7849152).sum := by decide
  have hdescent : baseEnd_7849152 < baseStart_7849152 := by decide
  rcases family_descends (prefixWord ++ tailWord_7849152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7849162 : List Nat := [3, 1, 2, 1, 3, 2, 2, 1, 3, 2, 3]
def baseStart_7849162 : Nat := 118140960795 + 7849162 * 2 ^ 59
def prefixEnd_7849162 : Nat := 4983230072969 + 3 ^ 40 * 7849162 * 2
def baseEnd_7849162 : Nat := 4030392841005924351277367

theorem tailTrace_7849162 : CollatzResearch.WordTrace tailWord_7849162 prefixEnd_7849162 4030392841005924351277367 := by
  unfold tailWord_7849162
  simp only [CollatzResearch.WordTrace]
  refine ⟨71570614297458519747413435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190854971459889385993102493 71570614297458519747413435)
  ·
    refine ⟨107355921446187779621120153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71570614297458519747413435 107355921446187779621120153)
    ·
      refine ⟨80516941084640834715840115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107355921446187779621120153 80516941084640834715840115)
      ·
        refine ⟨120775411626961252073760173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80516941084640834715840115 120775411626961252073760173)
        ·
          refine ⟨45290779360110469527660065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120775411626961252073760173 45290779360110469527660065)
          ·
            refine ⟨33968084520082852145745049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45290779360110469527660065 33968084520082852145745049)
            ·
              refine ⟨25476063390062139109308787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33968084520082852145745049 25476063390062139109308787)
              ·
                refine ⟨38214095085093208663963181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25476063390062139109308787 38214095085093208663963181)
                ·
                  refine ⟨14330285656909953248986193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38214095085093208663963181 14330285656909953248986193)
                  ·
                    refine ⟨10747714242682464936739645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14330285656909953248986193 10747714242682464936739645)
                    ·
                      refine ⟨4030392841005924351277367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10747714242682464936739645 4030392841005924351277367)
                      ·
                        rfl

theorem cell23_7849162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 1, 3, 2, 3].length) (baseStart_7849162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7849162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7849162 prefixEnd_7849162 := by exact prefixLift 7849162
  have htrace : WordTrace (prefixWord ++ tailWord_7849162) baseStart_7849162 baseEnd_7849162 := by
    simpa [prefixWord, tailWord_7849162, baseEnd_7849162] using wordTrace_append hprefix tailTrace_7849162
  have hstable : (prefixWord ++ tailWord_7849162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7849162).length < 2 ^ (prefixWord ++ tailWord_7849162).sum := by decide
  have hdescent : baseEnd_7849162 < baseStart_7849162 := by decide
  rcases family_descends (prefixWord ++ tailWord_7849162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7849176 : List Nat := [2, 1, 2, 2, 5, 2, 2, 1, 1, 1, 4]
def baseStart_7849176 : Nat := 118140960795 + 7849176 * 2 ^ 59
def prefixEnd_7849176 : Nat := 4983230072969 + 3 ^ 40 * 7849176 * 2
def baseEnd_7849176 : Nat := 4030400029735087296502303

theorem tailTrace_7849176 : CollatzResearch.WordTrace tailWord_7849176 prefixEnd_7849176 4030400029735087296502303 := by
  unfold tailWord_7849176
  simp only [CollatzResearch.WordTrace]
  refine ⟨143141483905891679690331691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190855311874522239587108921 143141483905891679690331691)
  ·
    refine ⟨214712225858837519535497537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143141483905891679690331691 214712225858837519535497537)
    ·
      refine ⟨161034169394128139651623153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214712225858837519535497537 161034169394128139651623153)
      ·
        refine ⟨120775627045596104738717365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161034169394128139651623153 120775627045596104738717365)
        ·
          refine ⟨11322715035524634819254753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 120775627045596104738717365 11322715035524634819254753)
          ·
            refine ⟨8492036276643476114441065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11322715035524634819254753 8492036276643476114441065)
            ·
              refine ⟨6369027207482607085830799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8492036276643476114441065 6369027207482607085830799)
              ·
                refine ⟨9553540811223910628746199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6369027207482607085830799 9553540811223910628746199)
                ·
                  refine ⟨14330311216835865943119299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9553540811223910628746199 14330311216835865943119299)
                  ·
                    refine ⟨21495466825253798914678949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14330311216835865943119299 21495466825253798914678949)
                    ·
                      refine ⟨4030400029735087296502303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21495466825253798914678949 4030400029735087296502303)
                      ·
                        rfl

theorem cell23_7849176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 2, 1, 1, 1, 4].length) (baseStart_7849176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7849176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7849176 prefixEnd_7849176 := by exact prefixLift 7849176
  have htrace : WordTrace (prefixWord ++ tailWord_7849176) baseStart_7849176 baseEnd_7849176 := by
    simpa [prefixWord, tailWord_7849176, baseEnd_7849176] using wordTrace_append hprefix tailTrace_7849176
  have hstable : (prefixWord ++ tailWord_7849176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7849176).length < 2 ^ (prefixWord ++ tailWord_7849176).sum := by decide
  have hdescent : baseEnd_7849176 < baseStart_7849176 := by decide
  rcases family_descends (prefixWord ++ tailWord_7849176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7849219 : List Nat := [1, 1, 1, 3, 2, 4, 1, 4, 1, 3, 2]
def baseStart_7849219 : Nat := 118140960795 + 7849219 * 2 ^ 59
def prefixEnd_7849219 : Nat := 4983230072969 + 3 ^ 40 * 7849219 * 2
def baseEnd_7849219 : Nat := 4030422109403230628264605

theorem tailTrace_7849219 : CollatzResearch.WordTrace tailWord_7849219 prefixEnd_7849219 4030422109403230628264605 := by
  unfold tailWord_7849219
  simp only [CollatzResearch.WordTrace]
  refine ⟨286284536150627577724478711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190856357433751718482985807 286284536150627577724478711)
  ·
    refine ⟨429426804225941366586718067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286284536150627577724478711 429426804225941366586718067)
    ·
      refine ⟨644140206338912049880077101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 429426804225941366586718067 644140206338912049880077101)
      ·
        refine ⟨241552577377092018705028913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 644140206338912049880077101 241552577377092018705028913)
        ·
          refine ⟨181164433032819014028771685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 241552577377092018705028913 181164433032819014028771685)
          ·
            refine ⟨33968331193653565130394691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 181164433032819014028771685 33968331193653565130394691)
            ·
              refine ⟨50952496790480347695592037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33968331193653565130394691 50952496790480347695592037)
              ·
                refine ⟨9553593148215065192923507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50952496790480347695592037 9553593148215065192923507)
                ·
                  refine ⟨14330389722322597789385261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9553593148215065192923507 14330389722322597789385261)
                  ·
                    refine ⟨5373896145870974171019473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14330389722322597789385261 5373896145870974171019473)
                    ·
                      refine ⟨4030422109403230628264605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5373896145870974171019473 4030422109403230628264605)
                      ·
                        rfl

theorem cell23_7849219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 4, 1, 3, 2].length) (baseStart_7849219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7849219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7849219 prefixEnd_7849219 := by exact prefixLift 7849219
  have htrace : WordTrace (prefixWord ++ tailWord_7849219) baseStart_7849219 baseEnd_7849219 := by
    simpa [prefixWord, tailWord_7849219, baseEnd_7849219] using wordTrace_append hprefix tailTrace_7849219
  have hstable : (prefixWord ++ tailWord_7849219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7849219).length < 2 ^ (prefixWord ++ tailWord_7849219).sum := by decide
  have hdescent : baseEnd_7849219 < baseStart_7849219 := by decide
  rcases family_descends (prefixWord ++ tailWord_7849219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7849235 : List Nat := [1, 1, 1, 2, 1, 3, 1, 1, 3, 6, 3]
def baseStart_7849235 : Nat := 118140960795 + 7849235 * 2 ^ 59
def prefixEnd_7849235 : Nat := 4983230072969 + 3 ^ 40 * 7849235 * 2
def baseEnd_7849235 : Nat := 4030430325093702565664531

theorem tailTrace_7849235 : CollatzResearch.WordTrace tailWord_7849235 prefixEnd_7849235 4030430325093702565664531 := by
  unfold tailWord_7849235
  simp only [CollatzResearch.WordTrace]
  refine ⟨286285119718569612457061159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190856746479046408304707439 286285119718569612457061159)
  ·
    refine ⟨429427679577854418685591739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286285119718569612457061159 429427679577854418685591739)
    ·
      refine ⟨644141519366781628028387609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 429427679577854418685591739 644141519366781628028387609)
      ·
        refine ⟨483106139525086221021290707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 644141519366781628028387609 483106139525086221021290707)
        ·
          refine ⟨724659209287629331531936061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 483106139525086221021290707 724659209287629331531936061)
          ·
            refine ⟨271747203482860999324476023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 724659209287629331531936061 271747203482860999324476023)
            ·
              refine ⟨407620805224291498986714035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 271747203482860999324476023 407620805224291498986714035)
              ·
                refine ⟨611431207836437248480071053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 407620805224291498986714035 611431207836437248480071053)
                ·
                  refine ⟨229286702938663968180026645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 611431207836437248480071053 229286702938663968180026645)
                  ·
                    refine ⟨10747814200249873508438749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 229286702938663968180026645 10747814200249873508438749)
                    ·
                      refine ⟨4030430325093702565664531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10747814200249873508438749 4030430325093702565664531)
                      ·
                        rfl

theorem cell23_7849235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 3, 6, 3].length) (baseStart_7849235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7849235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7849235 prefixEnd_7849235 := by exact prefixLift 7849235
  have htrace : WordTrace (prefixWord ++ tailWord_7849235) baseStart_7849235 baseEnd_7849235 := by
    simpa [prefixWord, tailWord_7849235, baseEnd_7849235] using wordTrace_append hprefix tailTrace_7849235
  have hstable : (prefixWord ++ tailWord_7849235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7849235).length < 2 ^ (prefixWord ++ tailWord_7849235).sum := by decide
  have hdescent : baseEnd_7849235 < baseStart_7849235 := by decide
  rcases family_descends (prefixWord ++ tailWord_7849235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7849252 : List Nat := [2, 3, 1, 3, 1, 1, 2, 1, 2, 4, 3]
def baseStart_7849252 : Nat := 118140960795 + 7849252 * 2 ^ 59
def prefixEnd_7849252 : Nat := 4983230072969 + 3 ^ 40 * 7849252 * 2
def baseEnd_7849252 : Nat := 4030439054264828999151953

theorem tailTrace_7849252 : CollatzResearch.WordTrace tailWord_7849252 prefixEnd_7849252 4030439054264828999151953 := by
  unfold tailWord_7849252
  simp only [CollatzResearch.WordTrace]
  refine ⟨143142869879754012180215005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190857159839672016240286673 143142869879754012180215005)
  ·
    refine ⟨53678576204907754567580627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143142869879754012180215005 53678576204907754567580627)
    ·
      refine ⟨80517864307361631851370941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53678576204907754567580627 80517864307361631851370941)
      ·
        refine ⟨30194199115260611944264103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80517864307361631851370941 30194199115260611944264103)
        ·
          refine ⟨45291298672890917916396155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30194199115260611944264103 45291298672890917916396155)
          ·
            refine ⟨67936948009336376874594233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45291298672890917916396155 67936948009336376874594233)
            ·
              refine ⟨50952711007002282655945675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67936948009336376874594233 50952711007002282655945675)
              ·
                refine ⟨76429066510503423983918513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50952711007002282655945675 76429066510503423983918513)
                ·
                  refine ⟨57321799882877567987938885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76429066510503423983918513 57321799882877567987938885)
                  ·
                    refine ⟨10747837478039543997738541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57321799882877567987938885 10747837478039543997738541)
                    ·
                      refine ⟨4030439054264828999151953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10747837478039543997738541 4030439054264828999151953)
                      ·
                        rfl

theorem cell23_7849252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 1, 2, 4, 3].length) (baseStart_7849252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7849252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7849252 prefixEnd_7849252 := by exact prefixLift 7849252
  have htrace : WordTrace (prefixWord ++ tailWord_7849252) baseStart_7849252 baseEnd_7849252 := by
    simpa [prefixWord, tailWord_7849252, baseEnd_7849252] using wordTrace_append hprefix tailTrace_7849252
  have hstable : (prefixWord ++ tailWord_7849252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7849252).length < 2 ^ (prefixWord ++ tailWord_7849252).sum := by decide
  have hdescent : baseEnd_7849252 < baseStart_7849252 := by decide
  rcases family_descends (prefixWord ++ tailWord_7849252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7849285 : List Nat := [1, 3, 1, 1, 1, 2, 1, 5, 1, 7]
def baseStart_7849285 : Nat := 118140960795 + 7849285 * 2 ^ 59
def prefixEnd_7849285 : Nat := 4983230072969 + 3 ^ 40 * 7849285 * 2
def baseEnd_7849285 : Nat := 1343485333042142456679767

theorem tailTrace_7849285 : CollatzResearch.WordTrace tailWord_7849285 prefixEnd_7849285 1343485333042142456679767 := by
  unfold tailWord_7849285
  simp only [CollatzResearch.WordTrace]
  refine ⟨286286943368388470996381309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190857962245592313997587539 286286943368388470996381309)
  ·
    refine ⟨107357603763145676623642991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 286286943368388470996381309 107357603763145676623642991)
    ·
      refine ⟨161036405644718514935464487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107357603763145676623642991 161036405644718514935464487)
      ·
        refine ⟨241554608467077772403196731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161036405644718514935464487 241554608467077772403196731)
        ·
          refine ⟨362331912700616658604795097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241554608467077772403196731 362331912700616658604795097)
          ·
            refine ⟨271748934525462493953596323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 362331912700616658604795097 271748934525462493953596323)
            ·
              refine ⟨407623401788193740930394485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 271748934525462493953596323 407623401788193740930394485)
              ·
                refine ⟨38214693917643163212224483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 407623401788193740930394485 38214693917643163212224483)
                ·
                  refine ⟨57322040876464744818336725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38214693917643163212224483 57322040876464744818336725)
                  ·
                    refine ⟨1343485333042142456679767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57322040876464744818336725 1343485333042142456679767)
                    ·
                      rfl

theorem cell23_7849285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 5, 1, 7].length) (baseStart_7849285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7849285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7849285 prefixEnd_7849285 := by exact prefixLift 7849285
  have htrace : WordTrace (prefixWord ++ tailWord_7849285) baseStart_7849285 baseEnd_7849285 := by
    simpa [prefixWord, tailWord_7849285, baseEnd_7849285] using wordTrace_append hprefix tailTrace_7849285
  have hstable : (prefixWord ++ tailWord_7849285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7849285).length < 2 ^ (prefixWord ++ tailWord_7849285).sum := by decide
  have hdescent : baseEnd_7849285 < baseStart_7849285 := by decide
  rcases family_descends (prefixWord ++ tailWord_7849285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7849312 : List Nat := [2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 5]
def baseStart_7849312 : Nat := 118140960795 + 7849312 * 2 ^ 59
def prefixEnd_7849312 : Nat := 4983230072969 + 3 ^ 40 * 7849312 * 2
def baseEnd_7849312 : Nat := 4030469863104098764401677

theorem tailTrace_7849312 : CollatzResearch.WordTrace tailWord_7849312 prefixEnd_7849312 4030469863104098764401677 := by
  unfold tailWord_7849312
  simp only [CollatzResearch.WordTrace]
  refine ⟨143143964069645327303807095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190858618759527103071742793 143143964069645327303807095)
  ·
    refine ⟨214715946104467990955710643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143143964069645327303807095 214715946104467990955710643)
    ·
      refine ⟨322073919156701986433565965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214715946104467990955710643 322073919156701986433565965)
      ·
        refine ⟨120777719683763244912587237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 322073919156701986433565965 120777719683763244912587237)
        ·
          refine ⟨22645822440705608421110107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 120777719683763244912587237 22645822440705608421110107)
          ·
            refine ⟨33968733661058412631665161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22645822440705608421110107 33968733661058412631665161)
            ·
              refine ⟨25476550245793809473748871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33968733661058412631665161 25476550245793809473748871)
              ·
                refine ⟨38214825368690714210623307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25476550245793809473748871 38214825368690714210623307)
                ·
                  refine ⟨57322238053036071315934961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38214825368690714210623307 57322238053036071315934961)
                  ·
                    refine ⟨42991678539777053486951221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57322238053036071315934961 42991678539777053486951221)
                    ·
                      refine ⟨4030469863104098764401677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42991678539777053486951221 4030469863104098764401677)
                      ·
                        rfl

theorem cell23_7849312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 5].length) (baseStart_7849312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7849312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7849312 prefixEnd_7849312 := by exact prefixLift 7849312
  have htrace : WordTrace (prefixWord ++ tailWord_7849312) baseStart_7849312 baseEnd_7849312 := by
    simpa [prefixWord, tailWord_7849312, baseEnd_7849312] using wordTrace_append hprefix tailTrace_7849312
  have hstable : (prefixWord ++ tailWord_7849312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7849312).length < 2 ^ (prefixWord ++ tailWord_7849312).sum := by decide
  have hdescent : baseEnd_7849312 < baseStart_7849312 := by decide
  rcases family_descends (prefixWord ++ tailWord_7849312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7849352 : List Nat := [2, 1, 3, 3, 1, 2, 1, 1, 2, 1, 6]
def baseStart_7849352 : Nat := 118140960795 + 7849352 * 2 ^ 59
def prefixEnd_7849352 : Nat := 4983230072969 + 3 ^ 40 * 7849352 * 2
def baseEnd_7849352 : Nat := 4030490402330278607901493

theorem tailTrace_7849352 : CollatzResearch.WordTrace tailWord_7849352 prefixEnd_7849352 4030490402330278607901493 := by
  unfold tailWord_7849352
  simp only [CollatzResearch.WordTrace]
  refine ⟨143144693529572870719535155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190859591372763827626046873 143144693529572870719535155)
  ·
    refine ⟨214717040294359306079302733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143144693529572870719535155 214717040294359306079302733)
    ·
      refine ⟨80518890110384739779738525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214717040294359306079302733 80518890110384739779738525)
      ·
        refine ⟨30194583791394277417401947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80518890110384739779738525 30194583791394277417401947)
        ·
          refine ⟨45291875687091416126102921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30194583791394277417401947 45291875687091416126102921)
          ·
            refine ⟨33968906765318562094577191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45291875687091416126102921 33968906765318562094577191)
            ·
              refine ⟨50953360147977843141865787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33968906765318562094577191 50953360147977843141865787)
              ·
                refine ⟨76430040221966764712798681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50953360147977843141865787 76430040221966764712798681)
                ·
                  refine ⟨57322530166475073534599011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76430040221966764712798681 57322530166475073534599011)
                  ·
                    refine ⟨85983795249712610301898517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57322530166475073534599011 85983795249712610301898517)
                    ·
                      refine ⟨4030490402330278607901493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85983795249712610301898517 4030490402330278607901493)
                      ·
                        rfl

theorem cell23_7849352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_7849352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7849352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7849352 prefixEnd_7849352 := by exact prefixLift 7849352
  have htrace : WordTrace (prefixWord ++ tailWord_7849352) baseStart_7849352 baseEnd_7849352 := by
    simpa [prefixWord, tailWord_7849352, baseEnd_7849352] using wordTrace_append hprefix tailTrace_7849352
  have hstable : (prefixWord ++ tailWord_7849352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7849352).length < 2 ^ (prefixWord ++ tailWord_7849352).sum := by decide
  have hdescent : baseEnd_7849352 < baseStart_7849352 := by decide
  rcases family_descends (prefixWord ++ tailWord_7849352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7849379 : List Nat := [1, 1, 1, 4, 1, 3, 5, 1, 6]
def baseStart_7849379 : Nat := 118140960795 + 7849379 * 2 ^ 59
def prefixEnd_7849379 : Nat := 4983230072969 + 3 ^ 40 * 7849379 * 2
def baseEnd_7849379 : Nat := 447833807367550000251541

theorem tailTrace_7849379 : CollatzResearch.WordTrace tailWord_7849379 prefixEnd_7849379 447833807367550000251541 := by
  unfold tailWord_7849379
  simp only [CollatzResearch.WordTrace]
  refine ⟨286290371830047925050303191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190860247886698616700202127 286290371830047925050303191)
  ·
    refine ⟨429435557745071887575454787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286290371830047925050303191 429435557745071887575454787)
    ·
      refine ⟨644153336617607831363182181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 429435557745071887575454787 644153336617607831363182181)
      ·
        refine ⟨120778750615801468380596659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 644153336617607831363182181 120778750615801468380596659)
        ·
          refine ⟨181168125923702202570894989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120778750615801468380596659 181168125923702202570894989)
          ·
            refine ⟨67938047221388325964085621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 181168125923702202570894989 67938047221388325964085621)
            ·
              refine ⟨6369191927005155559133027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67938047221388325964085621 6369191927005155559133027)
              ·
                refine ⟨9553787890507733338699541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6369191927005155559133027 9553787890507733338699541)
                ·
                  refine ⟨447833807367550000251541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9553787890507733338699541 447833807367550000251541)
                  ·
                    rfl

theorem cell23_7849379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 5, 1, 6].length) (baseStart_7849379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7849379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7849379 prefixEnd_7849379 := by exact prefixLift 7849379
  have htrace : WordTrace (prefixWord ++ tailWord_7849379) baseStart_7849379 baseEnd_7849379 := by
    simpa [prefixWord, tailWord_7849379, baseEnd_7849379] using wordTrace_append hprefix tailTrace_7849379
  have hstable : (prefixWord ++ tailWord_7849379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7849379).length < 2 ^ (prefixWord ++ tailWord_7849379).sum := by decide
  have hdescent : baseEnd_7849379 < baseStart_7849379 := by decide
  rcases family_descends (prefixWord ++ tailWord_7849379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7849399 : List Nat := [1, 1, 3, 1, 3, 2, 1, 3, 1, 5, 2]
def baseStart_7849399 : Nat := 118140960795 + 7849399 * 2 ^ 59
def prefixEnd_7849399 : Nat := 4983230072969 + 3 ^ 40 * 7849399 * 2
def baseEnd_7849399 : Nat := 4030514535921039924013777

theorem tailTrace_7849399 : CollatzResearch.WordTrace tailWord_7849399 prefixEnd_7849399 4030514535921039924013777 := by
  unfold tailWord_7849399
  simp only [CollatzResearch.WordTrace]
  refine ⟨286291101289975468466031251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190860734193316978977354167 286291101289975468466031251)
  ·
    refine ⟨429436651934963202699046877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286291101289975468466031251 429436651934963202699046877)
    ·
      refine ⟨161038744475611201012142579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 429436651934963202699046877 161038744475611201012142579)
      ·
        refine ⟨241558116713416801518213869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161038744475611201012142579 241558116713416801518213869)
        ·
          refine ⟨90584293767531300569330201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 241558116713416801518213869 90584293767531300569330201)
          ·
            refine ⟨67938220325648475426997651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90584293767531300569330201 67938220325648475426997651)
            ·
              refine ⟨101907330488472713140496477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67938220325648475426997651 101907330488472713140496477)
              ·
                refine ⟨38215248933177267427686179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101907330488472713140496477 38215248933177267427686179)
                ·
                  refine ⟨57322873399765901141529269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38215248933177267427686179 57322873399765901141529269)
                  ·
                    refine ⟨5374019381228053232018369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57322873399765901141529269 5374019381228053232018369)
                    ·
                      refine ⟨4030514535921039924013777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5374019381228053232018369 4030514535921039924013777)
                      ·
                        rfl

theorem cell23_7849399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 3, 1, 5, 2].length) (baseStart_7849399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7849399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7849399 prefixEnd_7849399 := by exact prefixLift 7849399
  have htrace : WordTrace (prefixWord ++ tailWord_7849399) baseStart_7849399 baseEnd_7849399 := by
    simpa [prefixWord, tailWord_7849399, baseEnd_7849399] using wordTrace_append hprefix tailTrace_7849399
  have hstable : (prefixWord ++ tailWord_7849399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7849399).length < 2 ^ (prefixWord ++ tailWord_7849399).sum := by decide
  have hdescent : baseEnd_7849399 < baseStart_7849399 := by decide
  rcases family_descends (prefixWord ++ tailWord_7849399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7849416 : List Nat := [2, 1, 3, 1, 3, 1, 3, 2, 2, 3, 2]
def baseStart_7849416 : Nat := 118140960795 + 7849416 * 2 ^ 59
def prefixEnd_7849416 : Nat := 4983230072969 + 3 ^ 40 * 7849416 * 2
def baseEnd_7849416 : Nat := 4030523265092166357501199

theorem tailTrace_7849416 : CollatzResearch.WordTrace tailWord_7849416 prefixEnd_7849416 4030523265092166357501199 := by
  unfold tailWord_7849416
  simp only [CollatzResearch.WordTrace]
  refine ⟨143145860665456940184700051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190861147553942586912933401 143145860665456940184700051)
  ·
    refine ⟨214718790998185410277050077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143145860665456940184700051 214718790998185410277050077)
    ·
      refine ⟨80519546624319528853893779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214718790998185410277050077 80519546624319528853893779)
      ·
        refine ⟨120779319936479293280840669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80519546624319528853893779 120779319936479293280840669)
        ·
          refine ⟨45292244976179734980315251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120779319936479293280840669 45292244976179734980315251)
          ·
            refine ⟨67938367464269602470472877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45292244976179734980315251 67938367464269602470472877)
            ·
              refine ⟨25476887799101100926427329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67938367464269602470472877 25476887799101100926427329)
              ·
                refine ⟨19107665849325825694820497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25476887799101100926427329 19107665849325825694820497)
                ·
                  refine ⟨14330749386994369271115373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19107665849325825694820497 14330749386994369271115373)
                  ·
                    refine ⟨5374031020122888476668265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14330749386994369271115373 5374031020122888476668265)
                    ·
                      refine ⟨4030523265092166357501199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5374031020122888476668265 4030523265092166357501199)
                      ·
                        rfl

theorem cell23_7849416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 2, 2, 3, 2].length) (baseStart_7849416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7849416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7849416 prefixEnd_7849416 := by exact prefixLift 7849416
  have htrace : WordTrace (prefixWord ++ tailWord_7849416) baseStart_7849416 baseEnd_7849416 := by
    simpa [prefixWord, tailWord_7849416, baseEnd_7849416] using wordTrace_append hprefix tailTrace_7849416
  have hstable : (prefixWord ++ tailWord_7849416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7849416).length < 2 ^ (prefixWord ++ tailWord_7849416).sum := by decide
  have hdescent : baseEnd_7849416 < baseStart_7849416 := by decide
  rcases family_descends (prefixWord ++ tailWord_7849416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7849429 : List Nat := [1, 3, 2, 3, 1, 1, 2, 2, 3, 1, 4]
def baseStart_7849429 : Nat := 118140960795 + 7849429 * 2 ^ 59
def prefixEnd_7849429 : Nat := 4983230072969 + 3 ^ 40 * 7849429 * 2
def baseEnd_7849429 : Nat := 4030529940340674806638639

theorem tailTrace_7849429 : CollatzResearch.WordTrace tailWord_7849429 prefixEnd_7849429 4030529940340674806638639 := by
  unfold tailWord_7849429
  simp only [CollatzResearch.WordTrace]
  refine ⟨286292195479866783589623341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190861463653244522393082227 286292195479866783589623341)
  ·
    refine ⟨107359573304950043846108753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 286292195479866783589623341 107359573304950043846108753)
    ·
      refine ⟨80519679978712532884581565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107359573304950043846108753 80519679978712532884581565)
      ·
        refine ⟨30194879992017199831718087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80519679978712532884581565 30194879992017199831718087)
        ·
          refine ⟨45292319988025799747577131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30194879992017199831718087 45292319988025799747577131)
          ·
            refine ⟨67938479982038699621365697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45292319988025799747577131 67938479982038699621365697)
            ·
              refine ⟨50953859986529024716024273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67938479982038699621365697 50953859986529024716024273)
              ·
                refine ⟨38215394989896768537018205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50953859986529024716024273 38215394989896768537018205)
                ·
                  refine ⟨14330773121211288201381827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38215394989896768537018205 14330773121211288201381827)
                  ·
                    refine ⟨21496159681816932302072741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14330773121211288201381827 21496159681816932302072741)
                    ·
                      refine ⟨4030529940340674806638639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21496159681816932302072741 4030529940340674806638639)
                      ·
                        rfl

theorem cell23_7849429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_7849429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7849429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7849429 prefixEnd_7849429 := by exact prefixLift 7849429
  have htrace : WordTrace (prefixWord ++ tailWord_7849429) baseStart_7849429 baseEnd_7849429 := by
    simpa [prefixWord, tailWord_7849429, baseEnd_7849429] using wordTrace_append hprefix tailTrace_7849429
  have hstable : (prefixWord ++ tailWord_7849429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7849429).length < 2 ^ (prefixWord ++ tailWord_7849429).sum := by decide
  have hdescent : baseEnd_7849429 < baseStart_7849429 := by decide
  rcases family_descends (prefixWord ++ tailWord_7849429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7849473 : List Nat := [1, 2, 4, 1, 4, 1, 2, 2, 2, 4]
def baseStart_7849473 : Nat := 118140960795 + 7849473 * 2 ^ 59
def prefixEnd_7849473 : Nat := 4983230072969 + 3 ^ 40 * 7849473 * 2
def baseEnd_7849473 : Nat := 1343517511163157544829479

theorem tailTrace_7849473 : CollatzResearch.WordTrace tailWord_7849473 prefixEnd_7849473 1343517511163157544829479 := by
  unfold tailWord_7849473
  simp only [CollatzResearch.WordTrace]
  refine ⟨286293800291707379104225073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190862533527804919402816715 286293800291707379104225073)
  ·
    refine ⟨214720350218780534328168805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286293800291707379104225073 214720350218780534328168805)
    ·
      refine ⟨40260065666021350186531651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 214720350218780534328168805 40260065666021350186531651)
      ·
        refine ⟨60390098499032025279797477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40260065666021350186531651 60390098499032025279797477)
        ·
          refine ⟨11323143468568504739962027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60390098499032025279797477 11323143468568504739962027)
          ·
            refine ⟨16984715202852757109943041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11323143468568504739962027 16984715202852757109943041)
            ·
              refine ⟨12738536402139567832457281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16984715202852757109943041 12738536402139567832457281)
              ·
                refine ⟨9553902301604675874342961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12738536402139567832457281 9553902301604675874342961)
                ·
                  refine ⟨7165426726203506905757221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9553902301604675874342961 7165426726203506905757221)
                  ·
                    refine ⟨1343517511163157544829479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7165426726203506905757221 1343517511163157544829479)
                    ·
                      rfl

theorem cell23_7849473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 2, 2, 2, 4].length) (baseStart_7849473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7849473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7849473 prefixEnd_7849473 := by exact prefixLift 7849473
  have htrace : WordTrace (prefixWord ++ tailWord_7849473) baseStart_7849473 baseEnd_7849473 := by
    simpa [prefixWord, tailWord_7849473, baseEnd_7849473] using wordTrace_append hprefix tailTrace_7849473
  have hstable : (prefixWord ++ tailWord_7849473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7849473).length < 2 ^ (prefixWord ++ tailWord_7849473).sum := by decide
  have hdescent : baseEnd_7849473 < baseStart_7849473 := by decide
  rcases family_descends (prefixWord ++ tailWord_7849473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7849474 : List Nat := [3, 4, 1, 2, 1, 3, 2, 2, 1, 1, 3]
def baseStart_7849474 : Nat := 118140960795 + 7849474 * 2 ^ 59
def prefixEnd_7849474 : Nat := 4983230072969 + 3 ^ 40 * 7849474 * 2
def baseEnd_7849474 : Nat := 4030553046970127130575933

theorem tailTrace_7849474 : CollatzResearch.WordTrace tailWord_7849474 prefixEnd_7849474 4030553046970127130575933 := by
  unfold tailWord_7849474
  simp only [CollatzResearch.WordTrace]
  refine ⟨71573459191175939068752869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190862557843135837516674317 71573459191175939068752869)
  ·
    refine ⟨13420023598345488575391163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71573459191175939068752869 13420023598345488575391163)
    ·
      refine ⟨20130035397518232863086745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13420023598345488575391163 20130035397518232863086745)
      ·
        refine ⟨15097526548138674647315059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20130035397518232863086745 15097526548138674647315059)
        ·
          refine ⟨22646289822208011970972589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15097526548138674647315059 22646289822208011970972589)
          ·
            refine ⟨8492358683328004489114721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22646289822208011970972589 8492358683328004489114721)
            ·
              refine ⟨6369269012496003366836041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8492358683328004489114721 6369269012496003366836041)
              ·
                refine ⟨4776951759372002525127031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6369269012496003366836041 4776951759372002525127031)
                ·
                  refine ⟨7165427639058003787690547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4776951759372002525127031 7165427639058003787690547)
                  ·
                    refine ⟨10748141458587005681535821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7165427639058003787690547 10748141458587005681535821)
                    ·
                      refine ⟨4030553046970127130575933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10748141458587005681535821 4030553046970127130575933)
                      ·
                        rfl

theorem cell23_7849474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 2, 2, 1, 1, 3].length) (baseStart_7849474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7849474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7849474 prefixEnd_7849474 := by exact prefixLift 7849474
  have htrace : WordTrace (prefixWord ++ tailWord_7849474) baseStart_7849474 baseEnd_7849474 := by
    simpa [prefixWord, tailWord_7849474, baseEnd_7849474] using wordTrace_append hprefix tailTrace_7849474
  have hstable : (prefixWord ++ tailWord_7849474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7849474).length < 2 ^ (prefixWord ++ tailWord_7849474).sum := by decide
  have hdescent : baseEnd_7849474 < baseStart_7849474 := by decide
  rcases family_descends (prefixWord ++ tailWord_7849474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7849486 : List Nat := [4, 1, 1, 2, 4, 2, 1, 8]
def baseStart_7849486 : Nat := 118140960795 + 7849486 * 2 ^ 59
def prefixEnd_7849486 : Nat := 4983230072969 + 3 ^ 40 * 7849486 * 2
def baseEnd_7849486 : Nat := 149279970693999299393551

theorem tailTrace_7849486 : CollatzResearch.WordTrace tailWord_7849486 prefixEnd_7849486 149279970693999299393551 := by
  unfold tailWord_7849486
  simp only [CollatzResearch.WordTrace]
  refine ⟨35786784305082535290556039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 190862849627106854882965541 35786784305082535290556039)
  ·
    refine ⟨53680176457623802935834059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35786784305082535290556039 53680176457623802935834059)
    ·
      refine ⟨80520264686435704403751089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53680176457623802935834059 80520264686435704403751089)
      ·
        refine ⟨60390198514826778302813317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80520264686435704403751089 60390198514826778302813317)
        ·
          refine ⟨11323162221530020931777497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60390198514826778302813317 11323162221530020931777497)
          ·
            refine ⟨8492371666147515698833123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11323162221530020931777497 8492371666147515698833123)
            ·
              refine ⟨12738557499221273548249685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8492371666147515698833123 12738557499221273548249685)
              ·
                refine ⟨149279970693999299393551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12738557499221273548249685 149279970693999299393551)
                ·
                  rfl

theorem cell23_7849486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 1, 8].length) (baseStart_7849486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7849486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7849486 prefixEnd_7849486 := by exact prefixLift 7849486
  have htrace : WordTrace (prefixWord ++ tailWord_7849486) baseStart_7849486 baseEnd_7849486 := by
    simpa [prefixWord, tailWord_7849486, baseEnd_7849486] using wordTrace_append hprefix tailTrace_7849486
  have hstable : (prefixWord ++ tailWord_7849486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7849486).length < 2 ^ (prefixWord ++ tailWord_7849486).sum := by decide
  have hdescent : baseEnd_7849486 < baseStart_7849486 := by decide
  rcases family_descends (prefixWord ++ tailWord_7849486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7849523 : List Nat := [1, 1, 1, 2, 4, 4, 1, 3, 1, 3, 2]
def baseStart_7849523 : Nat := 118140960795 + 7849523 * 2 ^ 59
def prefixEnd_7849523 : Nat := 4983230072969 + 3 ^ 40 * 7849523 * 2
def baseEnd_7849523 : Nat := 4030578207522197438863207

theorem tailTrace_7849523 : CollatzResearch.WordTrace tailWord_7849523 prefixEnd_7849523 4030578207522197438863207 := by
  unfold tailWord_7849523
  simp only [CollatzResearch.WordTrace]
  refine ⟨286295623941526237643545223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190863749294350825095696815 286295623941526237643545223)
  ·
    refine ⟨429443435912289356465317835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286295623941526237643545223 429443435912289356465317835)
    ·
      refine ⟨644165153868434034697976753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 429443435912289356465317835 644165153868434034697976753)
      ·
        refine ⟨483123865401325526023482565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 644165153868434034697976753 483123865401325526023482565)
        ·
          refine ⟨90585724762748536129402981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 483123865401325526023482565 90585724762748536129402981)
          ·
            refine ⟨16984823393015350524263059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90585724762748536129402981 16984823393015350524263059)
            ·
              refine ⟨25477235089523025786394589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16984823393015350524263059 25477235089523025786394589)
              ·
                refine ⟨9553963158571134669897971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25477235089523025786394589 9553963158571134669897971)
                ·
                  refine ⟨14330944737856702004846957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9553963158571134669897971 14330944737856702004846957)
                  ·
                    refine ⟨5374104276696263251817609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14330944737856702004846957 5374104276696263251817609)
                    ·
                      refine ⟨4030578207522197438863207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5374104276696263251817609 4030578207522197438863207)
                      ·
                        rfl

theorem cell23_7849523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 3, 1, 3, 2].length) (baseStart_7849523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7849523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7849523 prefixEnd_7849523 := by exact prefixLift 7849523
  have htrace : WordTrace (prefixWord ++ tailWord_7849523) baseStart_7849523 baseEnd_7849523 := by
    simpa [prefixWord, tailWord_7849523, baseEnd_7849523] using wordTrace_append hprefix tailTrace_7849523
  have hstable : (prefixWord ++ tailWord_7849523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7849523).length < 2 ^ (prefixWord ++ tailWord_7849523).sum := by decide
  have hdescent : baseEnd_7849523 < baseStart_7849523 := by decide
  rcases family_descends (prefixWord ++ tailWord_7849523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7849529 : List Nat := [1, 2, 1, 5, 1, 2, 1, 2, 2, 6]
def baseStart_7849529 : Nat := 118140960795 + 7849529 * 2 ^ 59
def prefixEnd_7849529 : Nat := 4983230072969 + 3 ^ 40 * 7849529 * 2
def baseEnd_7849529 : Nat := 1343527096135374805129393

theorem tailTrace_7849529 : CollatzResearch.WordTrace tailWord_7849529 prefixEnd_7849529 1343527096135374805129393 := by
  unfold tailWord_7849529
  simp only [CollatzResearch.WordTrace]
  refine ⟨286295842779504500668263641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190863895186336333778842427 286295842779504500668263641)
  ·
    refine ⟨214721882084628375501197731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286295842779504500668263641 214721882084628375501197731)
    ·
      refine ⟨322082823126942563251796597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214721882084628375501197731 322082823126942563251796597)
      ·
        refine ⟨30195264668150865304855931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 322082823126942563251796597 30195264668150865304855931)
        ·
          refine ⟨45292897002226297957283897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30195264668150865304855931 45292897002226297957283897)
          ·
            refine ⟨33969672751669723467962923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45292897002226297957283897 33969672751669723467962923)
            ·
              refine ⟨50954509127504585201944385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33969672751669723467962923 50954509127504585201944385)
              ·
                refine ⟨38215881845628438901458289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50954509127504585201944385 38215881845628438901458289)
                ·
                  refine ⟨28661911384221329176093717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38215881845628438901458289 28661911384221329176093717)
                  ·
                    refine ⟨1343527096135374805129393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28661911384221329176093717 1343527096135374805129393)
                    ·
                      rfl

theorem cell23_7849529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 2, 2, 6].length) (baseStart_7849529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7849529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7849529 prefixEnd_7849529 := by exact prefixLift 7849529
  have htrace : WordTrace (prefixWord ++ tailWord_7849529) baseStart_7849529 baseEnd_7849529 := by
    simpa [prefixWord, tailWord_7849529, baseEnd_7849529] using wordTrace_append hprefix tailTrace_7849529
  have hstable : (prefixWord ++ tailWord_7849529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7849529).length < 2 ^ (prefixWord ++ tailWord_7849529).sum := by decide
  have hdescent : baseEnd_7849529 < baseStart_7849529 := by decide
  rcases family_descends (prefixWord ++ tailWord_7849529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7849559 : List Nat := [1, 1, 3, 2, 2, 3, 2, 2, 7]
def baseStart_7849559 : Nat := 118140960795 + 7849559 * 2 ^ 59
def prefixEnd_7849559 : Nat := 4983230072969 + 3 ^ 40 * 7849559 * 2
def baseEnd_7849559 : Nat := 447844076980639922001449

theorem tailTrace_7849559 : CollatzResearch.WordTrace tailWord_7849559 prefixEnd_7849559 447844076980639922001449 := by
  unfold tailWord_7849559
  simp only [CollatzResearch.WordTrace]
  refine ⟨286296936969395815791855731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190864624646263877194570487 286296936969395815791855731)
  ·
    refine ⟨429445405454093723687783597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286296936969395815791855731 429445405454093723687783597)
    ·
      refine ⟨161042027045285146382918849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 429445405454093723687783597 161042027045285146382918849)
      ·
        refine ⟨120781520283963859787189137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161042027045285146382918849 120781520283963859787189137)
        ·
          refine ⟨90586140212972894840391853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120781520283963859787189137 90586140212972894840391853)
          ·
            refine ⟨33969802579864835565146945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90586140212972894840391853 33969802579864835565146945)
            ·
              refine ⟨25477351934898626673860209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33969802579864835565146945 25477351934898626673860209)
              ·
                refine ⟨19108013951173970005395157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25477351934898626673860209 19108013951173970005395157)
                ·
                  refine ⟨447844076980639922001449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19108013951173970005395157 447844076980639922001449)
                  ·
                    rfl

theorem cell23_7849559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 2, 7].length) (baseStart_7849559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7849559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7849559 prefixEnd_7849559 := by exact prefixLift 7849559
  have htrace : WordTrace (prefixWord ++ tailWord_7849559) baseStart_7849559 baseEnd_7849559 := by
    simpa [prefixWord, tailWord_7849559, baseEnd_7849559] using wordTrace_append hprefix tailTrace_7849559
  have hstable : (prefixWord ++ tailWord_7849559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7849559).length < 2 ^ (prefixWord ++ tailWord_7849559).sum := by decide
  have hdescent : baseEnd_7849559 < baseStart_7849559 := by decide
  rcases family_descends (prefixWord ++ tailWord_7849559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7849593 : List Nat := [1, 2, 1, 3, 3, 1, 5, 2, 5]
def baseStart_7849593 : Nat := 118140960795 + 7849593 * 2 ^ 59
def prefixEnd_7849593 : Nat := 4983230072969 + 3 ^ 40 * 7849593 * 2
def baseEnd_7849593 : Nat := 447846016796445796109765

theorem tailTrace_7849593 : CollatzResearch.WordTrace tailWord_7849593 prefixEnd_7849593 447846016796445796109765 := by
  unfold tailWord_7849593
  simp only [CollatzResearch.WordTrace]
  refine ⟨286298177051272639598593433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190865451367515093065728955 286298177051272639598593433)
  ·
    refine ⟨214723632788454479698945075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286298177051272639598593433 214723632788454479698945075)
    ·
      refine ⟨322085449182681719548417613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214723632788454479698945075 322085449182681719548417613)
      ·
        refine ⟨120782043443505644830656605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 322085449182681719548417613 120782043443505644830656605)
        ·
          refine ⟨45293266291314616811496227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120782043443505644830656605 45293266291314616811496227)
          ·
            refine ⟨67939899436971925217244341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45293266291314616811496227 67939899436971925217244341)
            ·
              refine ⟨6369365572216117989116657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67939899436971925217244341 6369365572216117989116657)
              ·
                refine ⟨4777024179162088491837493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6369365572216117989116657 4777024179162088491837493)
                ·
                  refine ⟨447846016796445796109765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4777024179162088491837493 447846016796445796109765)
                  ·
                    rfl

theorem cell23_7849593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 5, 2, 5].length) (baseStart_7849593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7849593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7849593 prefixEnd_7849593 := by exact prefixLift 7849593
  have htrace : WordTrace (prefixWord ++ tailWord_7849593) baseStart_7849593 baseEnd_7849593 := by
    simpa [prefixWord, tailWord_7849593, baseEnd_7849593] using wordTrace_append hprefix tailTrace_7849593
  have hstable : (prefixWord ++ tailWord_7849593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7849593).length < 2 ^ (prefixWord ++ tailWord_7849593).sum := by decide
  have hdescent : baseEnd_7849593 < baseStart_7849593 := by decide
  rcases family_descends (prefixWord ++ tailWord_7849593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7849596 : List Nat := [2, 2, 2, 1, 1, 2, 1, 3, 2, 5, 2]
def baseStart_7849596 : Nat := 118140960795 + 7849596 * 2 ^ 59
def prefixEnd_7849596 : Nat := 4983230072969 + 3 ^ 40 * 7849596 * 2
def baseEnd_7849596 : Nat := 4030615691609975653250371

theorem tailTrace_7849596 : CollatzResearch.WordTrace tailWord_7849596 prefixEnd_7849596 4030615691609975653250371 := by
  unfold tailWord_7849596
  simp only [CollatzResearch.WordTrace]
  refine ⟨143149143235130885555476321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190865524313507847407301761 143149143235130885555476321)
  ·
    refine ⟨107361857426348164166607241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143149143235130885555476321 107361857426348164166607241)
    ·
      refine ⟨80521393069761123124955431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107361857426348164166607241 80521393069761123124955431)
      ·
        refine ⟨120782089604641684687433147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80521393069761123124955431 120782089604641684687433147)
        ·
          refine ⟨181173134406962527031149721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120782089604641684687433147 181173134406962527031149721)
          ·
            refine ⟨135879850805221895273362291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181173134406962527031149721 135879850805221895273362291)
            ·
              refine ⟨203819776207832842910043437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135879850805221895273362291 203819776207832842910043437)
              ·
                refine ⟨76432416077937316091266289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 203819776207832842910043437 76432416077937316091266289)
                ·
                  refine ⟨57324312058452987068449717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76432416077937316091266289 57324312058452987068449717)
                  ·
                    refine ⟨5374154255479967537667161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57324312058452987068449717 5374154255479967537667161)
                    ·
                      refine ⟨4030615691609975653250371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5374154255479967537667161 4030615691609975653250371)
                      ·
                        rfl

theorem cell23_7849596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 3, 2, 5, 2].length) (baseStart_7849596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7849596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7849596 prefixEnd_7849596 := by exact prefixLift 7849596
  have htrace : WordTrace (prefixWord ++ tailWord_7849596) baseStart_7849596 baseEnd_7849596 := by
    simpa [prefixWord, tailWord_7849596, baseEnd_7849596] using wordTrace_append hprefix tailTrace_7849596
  have hstable : (prefixWord ++ tailWord_7849596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7849596).length < 2 ^ (prefixWord ++ tailWord_7849596).sum := by decide
  have hdescent : baseEnd_7849596 < baseStart_7849596 := by decide
  rcases family_descends (prefixWord ++ tailWord_7849596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7849604 : List Nat := [2, 3, 2, 1, 4, 2, 2, 1, 2, 2, 2]
def baseStart_7849604 : Nat := 118140960795 + 7849604 * 2 ^ 59
def prefixEnd_7849604 : Nat := 4983230072969 + 3 ^ 40 * 7849604 * 2
def baseEnd_7849604 : Nat := 4030619799455211621950335

theorem tailTrace_7849604 : CollatzResearch.WordTrace tailWord_7849604 prefixEnd_7849604 4030619799455211621950335 := by
  unfold tailWord_7849604
  simp only [CollatzResearch.WordTrace]
  refine ⟨143149289127116394238621933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190865718836155192318162577 143149289127116394238621933)
  ·
    refine ⟨53680983422668647839483225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143149289127116394238621933 53680983422668647839483225)
    ·
      refine ⟨40260737567001485879612419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53680983422668647839483225 40260737567001485879612419)
      ·
        refine ⟨60391106350502228819418629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40260737567001485879612419 60391106350502228819418629)
        ·
          refine ⟨11323332440719167903640993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60391106350502228819418629 11323332440719167903640993)
          ·
            refine ⟨8492499330539375927730745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11323332440719167903640993 8492499330539375927730745)
            ·
              refine ⟨6369374497904531945798059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8492499330539375927730745 6369374497904531945798059)
              ·
                refine ⟨9554061746856797918697089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6369374497904531945798059 9554061746856797918697089)
                ·
                  refine ⟨7165546310142598439022817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9554061746856797918697089 7165546310142598439022817)
                  ·
                    refine ⟨5374159732606948829267113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7165546310142598439022817 5374159732606948829267113)
                    ·
                      refine ⟨4030619799455211621950335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5374159732606948829267113 4030619799455211621950335)
                      ·
                        rfl

theorem cell23_7849604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 2, 1, 2, 2, 2].length) (baseStart_7849604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7849604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7849604 prefixEnd_7849604 := by exact prefixLift 7849604
  have htrace : WordTrace (prefixWord ++ tailWord_7849604) baseStart_7849604 baseEnd_7849604 := by
    simpa [prefixWord, tailWord_7849604, baseEnd_7849604] using wordTrace_append hprefix tailTrace_7849604
  have hstable : (prefixWord ++ tailWord_7849604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7849604).length < 2 ^ (prefixWord ++ tailWord_7849604).sum := by decide
  have hdescent : baseEnd_7849604 < baseStart_7849604 := by decide
  rcases family_descends (prefixWord ++ tailWord_7849604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7849609 : List Nat := [1, 2, 1, 1, 4, 1, 2, 1, 3, 3, 4]
def baseStart_7849609 : Nat := 118140960795 + 7849609 * 2 ^ 59
def prefixEnd_7849609 : Nat := 4983230072969 + 3 ^ 40 * 7849609 * 2
def baseEnd_7849609 : Nat := 4030622366858484102387811

theorem tailTrace_7849609 : CollatzResearch.WordTrace tailWord_7849609 prefixEnd_7849609 4030622366858484102387811 := by
  unfold tailWord_7849609
  simp only [CollatzResearch.WordTrace]
  refine ⟨286298760619214674331175881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190865840412809782887450587 286298760619214674331175881)
  ·
    refine ⟨214724070464411005748381911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286298760619214674331175881 214724070464411005748381911)
    ·
      refine ⟨322086105696616508622572867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214724070464411005748381911 322086105696616508622572867)
      ·
        refine ⟨483129158544924762933859301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322086105696616508622572867 483129158544924762933859301)
        ·
          refine ⟨90586717227173393050098619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 483129158544924762933859301 90586717227173393050098619)
          ·
            refine ⟨135880075840760089575147929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90586717227173393050098619 135880075840760089575147929)
            ·
              refine ⟨101910056880570067181360947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135880075840760089575147929 101910056880570067181360947)
              ·
                refine ⟨152865085320855100772041421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101910056880570067181360947 152865085320855100772041421)
                ·
                  refine ⟨57324406995320662789515533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 152865085320855100772041421 57324406995320662789515533)
                  ·
                    refine ⟨21496652623245248546068325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57324406995320662789515533 21496652623245248546068325)
                    ·
                      refine ⟨4030622366858484102387811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21496652623245248546068325 4030622366858484102387811)
                      ·
                        rfl

theorem cell23_7849609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 1, 3, 3, 4].length) (baseStart_7849609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7849609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7849609 prefixEnd_7849609 := by exact prefixLift 7849609
  have htrace : WordTrace (prefixWord ++ tailWord_7849609) baseStart_7849609 baseEnd_7849609 := by
    simpa [prefixWord, tailWord_7849609, baseEnd_7849609] using wordTrace_append hprefix tailTrace_7849609
  have hstable : (prefixWord ++ tailWord_7849609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7849609).length < 2 ^ (prefixWord ++ tailWord_7849609).sum := by decide
  have hdescent : baseEnd_7849609 < baseStart_7849609 := by decide
  rcases family_descends (prefixWord ++ tailWord_7849609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7849669 : List Nat := [1, 3, 1, 1, 1, 1, 2, 4, 1, 2, 6]
def baseStart_7849669 : Nat := 118140960795 + 7849669 * 2 ^ 59
def prefixEnd_7849669 : Nat := 4983230072969 + 3 ^ 40 * 7849669 * 2
def baseEnd_7849669 : Nat := 4030653175697753867637535

theorem tailTrace_7849669 : CollatzResearch.WordTrace tailWord_7849669 prefixEnd_7849669 4030653175697753867637535 := by
  unfold tailWord_7849669
  simp only [CollatzResearch.WordTrace]
  refine ⟨286300948998997304578360061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190867299332664869718906707 286300948998997304578360061)
  ·
    refine ⟨107362855874623989216885023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 286300948998997304578360061 107362855874623989216885023)
    ·
      refine ⟨161044283811935983825327535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107362855874623989216885023 161044283811935983825327535)
      ·
        refine ⟨241566425717903975737991303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161044283811935983825327535 241566425717903975737991303)
        ·
          refine ⟨362349638576855963606986955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241566425717903975737991303 362349638576855963606986955)
          ·
            refine ⟨543524457865283945410480433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 362349638576855963606986955 543524457865283945410480433)
            ·
              refine ⟨407643343398962959057860325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 543524457865283945410480433 407643343398962959057860325)
              ·
                refine ⟨76433126887305554823348811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 407643343398962959057860325 76433126887305554823348811)
                ·
                  refine ⟨114649690330958332235023217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76433126887305554823348811 114649690330958332235023217)
                  ·
                    refine ⟨85987267748218749176267413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 114649690330958332235023217 85987267748218749176267413)
                    ·
                      refine ⟨4030653175697753867637535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85987267748218749176267413 4030653175697753867637535)
                      ·
                        rfl

theorem cell23_7849669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 4, 1, 2, 6].length) (baseStart_7849669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7849669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7849669 prefixEnd_7849669 := by exact prefixLift 7849669
  have htrace : WordTrace (prefixWord ++ tailWord_7849669) baseStart_7849669 baseEnd_7849669 := by
    simpa [prefixWord, tailWord_7849669, baseEnd_7849669] using wordTrace_append hprefix tailTrace_7849669
  have hstable : (prefixWord ++ tailWord_7849669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7849669).length < 2 ^ (prefixWord ++ tailWord_7849669).sum := by decide
  have hdescent : baseEnd_7849669 < baseStart_7849669 := by decide
  rcases family_descends (prefixWord ++ tailWord_7849669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7849677 : List Nat := [1, 6, 2, 1, 1, 3, 1, 1, 2, 1, 4]
def baseStart_7849677 : Nat := 118140960795 + 7849677 * 2 ^ 59
def prefixEnd_7849677 : Nat := 4983230072969 + 3 ^ 40 * 7849677 * 2
def baseEnd_7849677 : Nat := 4030657283542989836337499

theorem tailTrace_7849677 : CollatzResearch.WordTrace tailWord_7849677 prefixEnd_7849677 4030657283542989836337499 := by
  unfold tailWord_7849677
  simp only [CollatzResearch.WordTrace]
  refine ⟨286301240782968321944651285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190867493855312214629767523 286301240782968321944651285)
  ·
    refine ⟨13420370661701640091155529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 286301240782968321944651285 13420370661701640091155529)
    ·
      refine ⟨10065277996276230068366647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13420370661701640091155529 10065277996276230068366647)
      ·
        refine ⟨15097916994414345102549971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10065277996276230068366647 15097916994414345102549971)
        ·
          refine ⟨22646875491621517653824957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15097916994414345102549971 22646875491621517653824957)
          ·
            refine ⟨8492578309358069120184359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22646875491621517653824957 8492578309358069120184359)
            ·
              refine ⟨12738867464037103680276539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8492578309358069120184359 12738867464037103680276539)
              ·
                refine ⟨19108301196055655520414809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12738867464037103680276539 19108301196055655520414809)
                ·
                  refine ⟨14331225897041741640311107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19108301196055655520414809 14331225897041741640311107)
                  ·
                    refine ⟨21496838845562612460466661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14331225897041741640311107 21496838845562612460466661)
                    ·
                      refine ⟨4030657283542989836337499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21496838845562612460466661 4030657283542989836337499)
                      ·
                        rfl

theorem cell23_7849677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_7849677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7849677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7849677 prefixEnd_7849677 := by exact prefixLift 7849677
  have htrace : WordTrace (prefixWord ++ tailWord_7849677) baseStart_7849677 baseEnd_7849677 := by
    simpa [prefixWord, tailWord_7849677, baseEnd_7849677] using wordTrace_append hprefix tailTrace_7849677
  have hstable : (prefixWord ++ tailWord_7849677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7849677).length < 2 ^ (prefixWord ++ tailWord_7849677).sum := by decide
  have hdescent : baseEnd_7849677 < baseStart_7849677 := by decide
  rcases family_descends (prefixWord ++ tailWord_7849677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7849710 : List Nat := [4, 1, 2, 1, 1, 2, 4, 1, 3, 1, 3]
def baseStart_7849710 : Nat := 118140960795 + 7849710 * 2 ^ 59
def prefixEnd_7849710 : Nat := 4983230072969 + 3 ^ 40 * 7849710 * 2
def baseEnd_7849710 : Nat := 4030674228404588207224847

theorem tailTrace_7849710 : CollatzResearch.WordTrace tailWord_7849710 prefixEnd_7849710 4030674228404588207224847 := by
  unfold tailWord_7849710
  simp only [CollatzResearch.WordTrace]
  refine ⟨35787805548981096072575323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 190868296261232512387068389 35787805548981096072575323)
  ·
    refine ⟨53681708323471644108862985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35787805548981096072575323 53681708323471644108862985)
    ·
      refine ⟨40261281242603733081647239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53681708323471644108862985 40261281242603733081647239)
      ·
        refine ⟨60391921863905599622470859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40261281242603733081647239 60391921863905599622470859)
        ·
          refine ⟨90587882795858399433706289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60391921863905599622470859 90587882795858399433706289)
          ·
            refine ⟨67940912096893799575279717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90587882795858399433706289 67940912096893799575279717)
            ·
              refine ⟨12738921018167587420364947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67940912096893799575279717 12738921018167587420364947)
              ·
                refine ⟨19108381527251381130547421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12738921018167587420364947 19108381527251381130547421)
                ·
                  refine ⟨7165643072719267923955283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19108381527251381130547421 7165643072719267923955283)
                  ·
                    refine ⟨10748464609078901885932925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7165643072719267923955283 10748464609078901885932925)
                    ·
                      refine ⟨4030674228404588207224847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10748464609078901885932925 4030674228404588207224847)
                      ·
                        rfl

theorem cell23_7849710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 4, 1, 3, 1, 3].length) (baseStart_7849710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7849710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7849710 prefixEnd_7849710 := by exact prefixLift 7849710
  have htrace : WordTrace (prefixWord ++ tailWord_7849710) baseStart_7849710 baseEnd_7849710 := by
    simpa [prefixWord, tailWord_7849710, baseEnd_7849710] using wordTrace_append hprefix tailTrace_7849710
  have hstable : (prefixWord ++ tailWord_7849710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7849710).length < 2 ^ (prefixWord ++ tailWord_7849710).sum := by decide
  have hdescent : baseEnd_7849710 < baseStart_7849710 := by decide
  rcases family_descends (prefixWord ++ tailWord_7849710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7849730 : List Nat := [3, 4, 1, 1, 1, 1, 4, 2, 1, 5]
def baseStart_7849730 : Nat := 118140960795 + 7849730 * 2 ^ 59
def prefixEnd_7849730 : Nat := 4983230072969 + 3 ^ 40 * 7849730 * 2
def baseEnd_7849730 : Nat := 1343561499339226042991585

theorem tailTrace_7849730 : CollatzResearch.WordTrace tailWord_7849730 prefixEnd_7849730 1343561499339226042991585 := by
  unfold tailWord_7849730
  simp only [CollatzResearch.WordTrace]
  refine ⟨71575793462944077999082661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190868782567850874664220429 71575793462944077999082661)
  ·
    refine ⟨13420461274302014624827999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71575793462944077999082661 13420461274302014624827999)
    ·
      refine ⟨20130691911453021937241999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13420461274302014624827999 20130691911453021937241999)
      ·
        refine ⟨30196037867179532905862999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20130691911453021937241999 30196037867179532905862999)
        ·
          refine ⟨45294056800769299358794499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30196037867179532905862999 45294056800769299358794499)
          ·
            refine ⟨67941085201153949038191749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45294056800769299358794499 67941085201153949038191749)
            ·
              refine ⟨12738953475216365444660953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67941085201153949038191749 12738953475216365444660953)
              ·
                refine ⟨9554215106412274083495715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12738953475216365444660953 9554215106412274083495715)
                ·
                  refine ⟨14331322659618411125243573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9554215106412274083495715 14331322659618411125243573)
                  ·
                    refine ⟨1343561499339226042991585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14331322659618411125243573 1343561499339226042991585)
                    ·
                      rfl

theorem cell23_7849730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 4, 2, 1, 5].length) (baseStart_7849730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7849730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7849730 prefixEnd_7849730 := by exact prefixLift 7849730
  have htrace : WordTrace (prefixWord ++ tailWord_7849730) baseStart_7849730 baseEnd_7849730 := by
    simpa [prefixWord, tailWord_7849730, baseEnd_7849730] using wordTrace_append hprefix tailTrace_7849730
  have hstable : (prefixWord ++ tailWord_7849730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7849730).length < 2 ^ (prefixWord ++ tailWord_7849730).sum := by decide
  have hdescent : baseEnd_7849730 < baseStart_7849730 := by decide
  rcases family_descends (prefixWord ++ tailWord_7849730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7849736 : List Nat := [2, 1, 3, 2, 2, 1, 1, 2, 3, 1, 5]
def baseStart_7849736 : Nat := 118140960795 + 7849736 * 2 ^ 59
def prefixEnd_7849736 : Nat := 4983230072969 + 3 ^ 40 * 7849736 * 2
def baseEnd_7849736 : Nat := 4030687578901605105499727

theorem tailTrace_7849736 : CollatzResearch.WordTrace tailWord_7849736 prefixEnd_7849736 4030687578901605105499727 := by
  unfold tailWord_7849736
  simp only [CollatzResearch.WordTrace]
  refine ⟨143151696344877287510524531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190868928459836383347366041 143151696344877287510524531)
  ·
    refine ⟨214727544517315931265786797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143151696344877287510524531 214727544517315931265786797)
    ·
      refine ⟨80522829193993474224670049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214727544517315931265786797 80522829193993474224670049)
      ·
        refine ⟨60392121895495105668502537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80522829193993474224670049 60392121895495105668502537)
        ·
          refine ⟨45294091421621329251376903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60392121895495105668502537 45294091421621329251376903)
          ·
            refine ⟨67941137132431993877065355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45294091421621329251376903 67941137132431993877065355)
            ·
              refine ⟨101911705698647990815598033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67941137132431993877065355 101911705698647990815598033)
              ·
                refine ⟨76433779273985993111698525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101911705698647990815598033 76433779273985993111698525)
                ·
                  refine ⟨28662667227744747416886947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76433779273985993111698525 28662667227744747416886947)
                  ·
                    refine ⟨42994000841617121125330421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28662667227744747416886947 42994000841617121125330421)
                    ·
                      refine ⟨4030687578901605105499727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42994000841617121125330421 4030687578901605105499727)
                      ·
                        rfl

theorem cell23_7849736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 2, 3, 1, 5].length) (baseStart_7849736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7849736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7849736 prefixEnd_7849736 := by exact prefixLift 7849736
  have htrace : WordTrace (prefixWord ++ tailWord_7849736) baseStart_7849736 baseEnd_7849736 := by
    simpa [prefixWord, tailWord_7849736, baseEnd_7849736] using wordTrace_append hprefix tailTrace_7849736
  have hstable : (prefixWord ++ tailWord_7849736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7849736).length < 2 ^ (prefixWord ++ tailWord_7849736).sum := by decide
  have hdescent : baseEnd_7849736 < baseStart_7849736 := by decide
  rcases family_descends (prefixWord ++ tailWord_7849736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7849777 : List Nat := [1, 2, 2, 3, 2, 4, 2, 1, 2, 4]
def baseStart_7849777 : Nat := 118140960795 + 7849777 * 2 ^ 59
def prefixEnd_7849777 : Nat := 4983230072969 + 3 ^ 40 * 7849777 * 2
def baseEnd_7849777 : Nat := 1343569543869479815029013

theorem tailTrace_7849777 : CollatzResearch.WordTrace tailWord_7849777 prefixEnd_7849777 1343569543869479815029013 := by
  unfold tailWord_7849777
  simp only [CollatzResearch.WordTrace]
  refine ⟨286304888082606039023291585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190869925388404026015527723 286304888082606039023291585)
  ·
    refine ⟨214728666061954529267468689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286304888082606039023291585 214728666061954529267468689)
    ·
      refine ⟨161046499546465896950601517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214728666061954529267468689 161046499546465896950601517)
      ·
        refine ⟨60392437329924711356475569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161046499546465896950601517 60392437329924711356475569)
        ·
          refine ⟨45294327997443533517356677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60392437329924711356475569 45294327997443533517356677)
          ·
            refine ⟨8492686499520662534504377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45294327997443533517356677 8492686499520662534504377)
            ·
              refine ⟨6369514874640496900878283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8492686499520662534504377 6369514874640496900878283)
              ·
                refine ⟨9554272311960745351317425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6369514874640496900878283 9554272311960745351317425)
                ·
                  refine ⟨7165704233970559013488069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9554272311960745351317425 7165704233970559013488069)
                  ·
                    refine ⟨1343569543869479815029013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7165704233970559013488069 1343569543869479815029013)
                    ·
                      rfl

theorem cell23_7849777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 2, 1, 2, 4].length) (baseStart_7849777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7849777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7849777 prefixEnd_7849777 := by exact prefixLift 7849777
  have htrace : WordTrace (prefixWord ++ tailWord_7849777) baseStart_7849777 baseEnd_7849777 := by
    simpa [prefixWord, tailWord_7849777, baseEnd_7849777] using wordTrace_append hprefix tailTrace_7849777
  have hstable : (prefixWord ++ tailWord_7849777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7849777).length < 2 ^ (prefixWord ++ tailWord_7849777).sum := by decide
  have hdescent : baseEnd_7849777 < baseStart_7849777 := by decide
  rcases family_descends (prefixWord ++ tailWord_7849777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7849783 : List Nat := [1, 1, 3, 1, 2, 1, 2, 2, 6, 1, 3]
def baseStart_7849783 : Nat := 118140960795 + 7849783 * 2 ^ 59
def prefixEnd_7849783 : Nat := 4983230072969 + 3 ^ 40 * 7849783 * 2
def baseEnd_7849783 : Nat := 4030711712492366421612011

theorem tailTrace_7849783 : CollatzResearch.WordTrace tailWord_7849783 prefixEnd_7849783 4030711712492366421612011 := by
  unfold tailWord_7849783
  simp only [CollatzResearch.WordTrace]
  refine ⟨286305106920584302048010003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190870071280389534698673335 286305106920584302048010003)
  ·
    refine ⟨429457660380876453072015005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286305106920584302048010003 429457660380876453072015005)
    ·
      refine ⟨161046622642828669902005627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 429457660380876453072015005 161046622642828669902005627)
      ·
        refine ⟨241569933964243004853008441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161046622642828669902005627 241569933964243004853008441)
        ·
          refine ⟨181177450473182253639756331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 241569933964243004853008441 181177450473182253639756331)
          ·
            refine ⟨271766175709773380459634497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181177450473182253639756331 271766175709773380459634497)
            ·
              refine ⟨203824631782330035344725873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 271766175709773380459634497 203824631782330035344725873)
              ·
                refine ⟨152868473836747526508544405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 203824631782330035344725873 152868473836747526508544405)
                ·
                  refine ⟨7165709711097540305088019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 152868473836747526508544405 7165709711097540305088019)
                  ·
                    refine ⟨10748564566646310457632029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7165709711097540305088019 10748564566646310457632029)
                    ·
                      refine ⟨4030711712492366421612011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10748564566646310457632029 4030711712492366421612011)
                      ·
                        rfl

theorem cell23_7849783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 2, 6, 1, 3].length) (baseStart_7849783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7849783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7849783 prefixEnd_7849783 := by exact prefixLift 7849783
  have htrace : WordTrace (prefixWord ++ tailWord_7849783) baseStart_7849783 baseEnd_7849783 := by
    simpa [prefixWord, tailWord_7849783, baseEnd_7849783] using wordTrace_append hprefix tailTrace_7849783
  have hstable : (prefixWord ++ tailWord_7849783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7849783).length < 2 ^ (prefixWord ++ tailWord_7849783).sum := by decide
  have hdescent : baseEnd_7849783 < baseStart_7849783 := by decide
  rcases family_descends (prefixWord ++ tailWord_7849783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7849840 : List Nat := [2, 1, 1, 1, 4, 1, 1, 2, 6, 2, 2]
def baseStart_7849840 : Nat := 118140960795 + 7849840 * 2 ^ 59
def prefixEnd_7849840 : Nat := 4983230072969 + 3 ^ 40 * 7849840 * 2
def baseEnd_7849840 : Nat := 4030740980889672698599249

theorem tailTrace_7849840 : CollatzResearch.WordTrace tailWord_7849840 prefixEnd_7849840 4030740980889672698599249 := by
  unfold tailWord_7849840
  simp only [CollatzResearch.WordTrace]
  refine ⟨143153592940688900391417487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190871457254251867188556649 143153592940688900391417487)
  ·
    refine ⟨214730389411033350587126231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143153592940688900391417487 214730389411033350587126231)
    ·
      refine ⟨322095584116550025880689347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214730389411033350587126231 322095584116550025880689347)
      ·
        refine ⟨483143376174825038821034021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322095584116550025880689347 483143376174825038821034021)
        ·
          refine ⟨90589383032779694778943879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 483143376174825038821034021 90589383032779694778943879)
          ·
            refine ⟨135884074549169542168415819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90589383032779694778943879 135884074549169542168415819)
            ·
              refine ⟨203826111823754313252623729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135884074549169542168415819 203826111823754313252623729)
              ·
                refine ⟨152869583867815734939467797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 203826111823754313252623729 152869583867815734939467797)
                ·
                  refine ⟨7165761743803862575287553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 152869583867815734939467797 7165761743803862575287553)
                  ·
                    refine ⟨5374321307852896931465665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7165761743803862575287553 5374321307852896931465665)
                    ·
                      refine ⟨4030740980889672698599249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5374321307852896931465665 4030740980889672698599249)
                      ·
                        rfl

theorem cell23_7849840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 6, 2, 2].length) (baseStart_7849840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7849840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7849840 prefixEnd_7849840 := by exact prefixLift 7849840
  have htrace : WordTrace (prefixWord ++ tailWord_7849840) baseStart_7849840 baseEnd_7849840 := by
    simpa [prefixWord, tailWord_7849840, baseEnd_7849840] using wordTrace_append hprefix tailTrace_7849840
  have hstable : (prefixWord ++ tailWord_7849840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7849840).length < 2 ^ (prefixWord ++ tailWord_7849840).sum := by decide
  have hdescent : baseEnd_7849840 < baseStart_7849840 := by decide
  rcases family_descends (prefixWord ++ tailWord_7849840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7849873 : List Nat := [1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 3]
def baseStart_7849873 : Nat := 118140960795 + 7849873 * 2 ^ 59
def prefixEnd_7849873 : Nat := 4983230072969 + 3 ^ 40 * 7849873 * 2
def baseEnd_7849873 : Nat := 4030757925751271069486597

theorem tailTrace_7849873 : CollatzResearch.WordTrace tailWord_7849873 prefixEnd_7849873 4030757925751271069486597 := by
  unfold tailWord_7849873
  simp only [CollatzResearch.WordTrace]
  refine ⟨286308389490258247418786273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190872259660172164945857515 286308389490258247418786273)
  ·
    refine ⟨214731292117693685564089705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286308389490258247418786273 214731292117693685564089705)
    ·
      refine ⟨161048469088270264173067279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214731292117693685564089705 161048469088270264173067279)
      ·
        refine ⟨241572703632405396259600919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161048469088270264173067279 241572703632405396259600919)
        ·
          refine ⟨362359055448608094389401379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241572703632405396259600919 362359055448608094389401379)
          ·
            refine ⟨543538583172912141584102069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 362359055448608094389401379 543538583172912141584102069)
            ·
              refine ⟨50956742172460513273509569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 543538583172912141584102069 50956742172460513273509569)
              ·
                refine ⟨38217556629345384955132177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50956742172460513273509569 38217556629345384955132177)
                ·
                  refine ⟨28663167472009038716349133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38217556629345384955132177 28663167472009038716349133)
                  ·
                    refine ⟨10748687802003389518630925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28663167472009038716349133 10748687802003389518630925)
                    ·
                      refine ⟨4030757925751271069486597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10748687802003389518630925 4030757925751271069486597)
                      ·
                        rfl

theorem cell23_7849873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 3].length) (baseStart_7849873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7849873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7849873 prefixEnd_7849873 := by exact prefixLift 7849873
  have htrace : WordTrace (prefixWord ++ tailWord_7849873) baseStart_7849873 baseEnd_7849873 := by
    simpa [prefixWord, tailWord_7849873, baseEnd_7849873] using wordTrace_append hprefix tailTrace_7849873
  have hstable : (prefixWord ++ tailWord_7849873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7849873).length < 2 ^ (prefixWord ++ tailWord_7849873).sum := by decide
  have hdescent : baseEnd_7849873 < baseStart_7849873 := by decide
  rcases family_descends (prefixWord ++ tailWord_7849873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7849874 : List Nat := [3, 2, 3, 2, 1, 2, 1, 1, 4, 2, 2]
def baseStart_7849874 : Nat := 118140960795 + 7849874 * 2 ^ 59
def prefixEnd_7849874 : Nat := 4983230072969 + 3 ^ 40 * 7849874 * 2
def baseEnd_7849874 : Nat := 4030758439231925565574093

theorem tailTrace_7849874 : CollatzResearch.WordTrace tailWord_7849874 prefixEnd_7849874 4030758439231925565574093 := by
  unfold tailWord_7849874
  simp only [CollatzResearch.WordTrace]
  refine ⟨71577106490813656147393169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190872283975503083059715117 71577106490813656147393169)
  ·
    refine ⟨53682829868110242110544877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71577106490813656147393169 53682829868110242110544877)
    ·
      refine ⟨20131061200541340791454329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53682829868110242110544877 20131061200541340791454329)
      ·
        refine ⟨15098295900406005593590747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20131061200541340791454329 15098295900406005593590747)
        ·
          refine ⟨22647443850609008390386121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15098295900406005593590747 22647443850609008390386121)
          ·
            refine ⟨16985582887956756292789591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22647443850609008390386121 16985582887956756292789591)
            ·
              refine ⟨25478374331935134439184387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16985582887956756292789591 25478374331935134439184387)
              ·
                refine ⟨38217561497902701658776581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25478374331935134439184387 38217561497902701658776581)
                ·
                  refine ⟨7165792780856756561020609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38217561497902701658776581 7165792780856756561020609)
                  ·
                    refine ⟨5374344585642567420765457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7165792780856756561020609 5374344585642567420765457)
                    ·
                      refine ⟨4030758439231925565574093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5374344585642567420765457 4030758439231925565574093)
                      ·
                        rfl

theorem cell23_7849874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 1, 4, 2, 2].length) (baseStart_7849874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7849874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7849874 prefixEnd_7849874 := by exact prefixLift 7849874
  have htrace : WordTrace (prefixWord ++ tailWord_7849874) baseStart_7849874 baseEnd_7849874 := by
    simpa [prefixWord, tailWord_7849874, baseEnd_7849874] using wordTrace_append hprefix tailTrace_7849874
  have hstable : (prefixWord ++ tailWord_7849874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7849874).length < 2 ^ (prefixWord ++ tailWord_7849874).sum := by decide
  have hdescent : baseEnd_7849874 < baseStart_7849874 := by decide
  rcases family_descends (prefixWord ++ tailWord_7849874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7849913 : List Nat := [1, 2, 1, 4, 2, 1, 1, 3, 1, 3, 4]
def baseStart_7849913 : Nat := 118140960795 + 7849913 * 2 ^ 59
def prefixEnd_7849913 : Nat := 4983230072969 + 3 ^ 40 * 7849913 * 2
def baseEnd_7849913 : Nat := 4030778464977450912986413

theorem tailTrace_7849913 : CollatzResearch.WordTrace tailWord_7849913 prefixEnd_7849913 4030778464977450912986413 := by
  unfold tailWord_7849913
  simp only [CollatzResearch.WordTrace]
  refine ⟨286309848410113334250242393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190873232273408889500161595 286309848410113334250242393)
  ·
    refine ⟨214732386307585000687681795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286309848410113334250242393 214732386307585000687681795)
    ·
      refine ⟨322098579461377501031522693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214732386307585000687681795 322098579461377501031522693)
      ·
        refine ⟨60393483649008281443410505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 322098579461377501031522693 60393483649008281443410505)
        ·
          refine ⟨45295112736756211082557879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60393483649008281443410505 45295112736756211082557879)
          ·
            refine ⟨67942669105134316623836819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45295112736756211082557879 67942669105134316623836819)
            ·
              refine ⟨101914003657701474935755229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67942669105134316623836819 101914003657701474935755229)
              ·
                refine ⟨38217751371638053100908211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101914003657701474935755229 38217751371638053100908211)
                ·
                  refine ⟨57326627057457079651362317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38217751371638053100908211 57326627057457079651362317)
                  ·
                    refine ⟨21497485146546404869260869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57326627057457079651362317 21497485146546404869260869)
                    ·
                      refine ⟨4030778464977450912986413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21497485146546404869260869 4030778464977450912986413)
                      ·
                        rfl

theorem cell23_7849913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 3, 1, 3, 4].length) (baseStart_7849913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7849913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7849913 prefixEnd_7849913 := by exact prefixLift 7849913
  have htrace : WordTrace (prefixWord ++ tailWord_7849913) baseStart_7849913 baseEnd_7849913 := by
    simpa [prefixWord, tailWord_7849913, baseEnd_7849913] using wordTrace_append hprefix tailTrace_7849913
  have hstable : (prefixWord ++ tailWord_7849913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7849913).length < 2 ^ (prefixWord ++ tailWord_7849913).sum := by decide
  have hdescent : baseEnd_7849913 < baseStart_7849913 := by decide
  rcases family_descends (prefixWord ++ tailWord_7849913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7849930 : List Nat := [3, 1, 2, 1, 2, 1, 2, 1, 4, 4, 2]
def baseStart_7849930 : Nat := 118140960795 + 7849930 * 2 ^ 59
def prefixEnd_7849930 : Nat := 4983230072969 + 3 ^ 40 * 7849930 * 2
def baseEnd_7849930 : Nat := 4030787194148577346473835

theorem tailTrace_7849930 : CollatzResearch.WordTrace tailWord_7849930 prefixEnd_7849930 4030787194148577346473835 := by
  unfold tailWord_7849930
  simp only [CollatzResearch.WordTrace]
  refine ⟨71577617112762936538402811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190873645634034497435740829 71577617112762936538402811)
  ·
    refine ⟨107366425669144404807604217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71577617112762936538402811 107366425669144404807604217)
    ·
      refine ⟨80524819251858303605703163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107366425669144404807604217 80524819251858303605703163)
      ·
        refine ⟨120787228877787455408554745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80524819251858303605703163 120787228877787455408554745)
        ·
          refine ⟨90590421658340591556416059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120787228877787455408554745 90590421658340591556416059)
          ·
            refine ⟨135885632487510887334624089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90590421658340591556416059 135885632487510887334624089)
            ·
              refine ⟨101914224365633165500968067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135885632487510887334624089 101914224365633165500968067)
              ·
                refine ⟨152871336548449748251452101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101914224365633165500968067 152871336548449748251452101)
                ·
                  refine ⟨28663375602834327797147269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 152871336548449748251452101 28663375602834327797147269)
                  ·
                    refine ⟨5374382925531436461965113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28663375602834327797147269 5374382925531436461965113)
                    ·
                      refine ⟨4030787194148577346473835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5374382925531436461965113 4030787194148577346473835)
                      ·
                        rfl

theorem cell23_7849930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 1, 4, 4, 2].length) (baseStart_7849930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7849930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7849930 prefixEnd_7849930 := by exact prefixLift 7849930
  have htrace : WordTrace (prefixWord ++ tailWord_7849930) baseStart_7849930 baseEnd_7849930 := by
    simpa [prefixWord, tailWord_7849930, baseEnd_7849930] using wordTrace_append hprefix tailTrace_7849930
  have hstable : (prefixWord ++ tailWord_7849930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7849930).length < 2 ^ (prefixWord ++ tailWord_7849930).sum := by decide
  have hdescent : baseEnd_7849930 < baseStart_7849930 := by decide
  rcases family_descends (prefixWord ++ tailWord_7849930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7849963 : List Nat := [1, 1, 1, 1, 2, 3, 1, 3, 2, 5, 3]
def baseStart_7849963 : Nat := 118140960795 + 7849963 * 2 ^ 59
def prefixEnd_7849963 : Nat := 4983230072969 + 3 ^ 40 * 7849963 * 2
def baseEnd_7849963 : Nat := 4030804139010175717361183

theorem tailTrace_7849963 : CollatzResearch.WordTrace tailWord_7849963 prefixEnd_7849963 4030804139010175717361183 := by
  unfold tailWord_7849963
  simp only [CollatzResearch.WordTrace]
  refine ⟨286311672059932192789562543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190874448039954795193041695 286311672059932192789562543)
  ·
    refine ⟨429467508089898289184343815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286311672059932192789562543 429467508089898289184343815)
    ·
      refine ⟨644201262134847433776515723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 429467508089898289184343815 644201262134847433776515723)
      ·
        refine ⟨966301893202271150664773585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 644201262134847433776515723 966301893202271150664773585)
        ·
          refine ⟨724726419901703362998580189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 966301893202271150664773585 724726419901703362998580189)
          ·
            refine ⟨271772407463138761124467571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 724726419901703362998580189 271772407463138761124467571)
            ·
              refine ⟨407658611194708141686701357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 271772407463138761124467571 407658611194708141686701357)
              ·
                refine ⟨152871979198015553132513009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 407658611194708141686701357 152871979198015553132513009)
                ·
                  refine ⟨114653984398511664849384757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 152871979198015553132513009 114653984398511664849384757)
                  ·
                    refine ⟨10748811037360468579629821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 114653984398511664849384757 10748811037360468579629821)
                    ·
                      refine ⟨4030804139010175717361183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10748811037360468579629821 4030804139010175717361183)
                      ·
                        rfl

theorem cell23_7849963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 3, 2, 5, 3].length) (baseStart_7849963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7849963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7849963 prefixEnd_7849963 := by exact prefixLift 7849963
  have htrace : WordTrace (prefixWord ++ tailWord_7849963) baseStart_7849963 baseEnd_7849963 := by
    simpa [prefixWord, tailWord_7849963, baseEnd_7849963] using wordTrace_append hprefix tailTrace_7849963
  have hstable : (prefixWord ++ tailWord_7849963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7849963).length < 2 ^ (prefixWord ++ tailWord_7849963).sum := by decide
  have hdescent : baseEnd_7849963 < baseStart_7849963 := by decide
  rcases family_descends (prefixWord ++ tailWord_7849963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7849991 : List Nat := [1, 1, 4, 3, 1, 4, 2, 2, 1, 4]
def baseStart_7849991 : Nat := 118140960795 + 7849991 * 2 ^ 59
def prefixEnd_7849991 : Nat := 4983230072969 + 3 ^ 40 * 7849991 * 2
def baseEnd_7849991 : Nat := 1343606172156167202603685

theorem tailTrace_7849991 : CollatzResearch.WordTrace tailWord_7849991 prefixEnd_7849991 1343606172156167202603685 := by
  unfold tailWord_7849991
  simp only [CollatzResearch.WordTrace]
  refine ⟨286312693303830753571581827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190875128869220502381054551 286312693303830753571581827)
  ·
    refine ⟨429469039955746130357372741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286312693303830753571581827 429469039955746130357372741)
    ·
      refine ⟨80525444991702399442007389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 429469039955746130357372741 80525444991702399442007389)
      ·
        refine ⟨30197041871888399790752771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80525444991702399442007389 30197041871888399790752771)
        ·
          refine ⟨45295562807832599686129157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30197041871888399790752771 45295562807832599686129157)
          ·
            refine ⟨8492918026468612441149217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45295562807832599686129157 8492918026468612441149217)
            ·
              refine ⟨6369688519851459330861913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8492918026468612441149217 6369688519851459330861913)
              ·
                refine ⟨4777266389888594498146435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6369688519851459330861913 4777266389888594498146435)
                ·
                  refine ⟨7165899584832891747219653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4777266389888594498146435 7165899584832891747219653)
                  ·
                    refine ⟨1343606172156167202603685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7165899584832891747219653 1343606172156167202603685)
                    ·
                      rfl

theorem cell23_7849991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 2, 2, 1, 4].length) (baseStart_7849991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7849991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7849991 prefixEnd_7849991 := by exact prefixLift 7849991
  have htrace : WordTrace (prefixWord ++ tailWord_7849991) baseStart_7849991 baseEnd_7849991 := by
    simpa [prefixWord, tailWord_7849991, baseEnd_7849991] using wordTrace_append hprefix tailTrace_7849991
  have hstable : (prefixWord ++ tailWord_7849991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7849991).length < 2 ^ (prefixWord ++ tailWord_7849991).sum := by decide
  have hdescent : baseEnd_7849991 < baseStart_7849991 := by decide
  rcases family_descends (prefixWord ++ tailWord_7849991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7850034 : List Nat := [3, 2, 1, 1, 2, 5, 2, 1, 1, 5]
def baseStart_7850034 : Nat := 118140960795 + 7850034 * 2 ^ 59
def prefixEnd_7850034 : Nat := 4983230072969 + 3 ^ 40 * 7850034 * 2
def baseEnd_7850034 : Nat := 1343613532045548313191119

theorem tailTrace_7850034 : CollatzResearch.WordTrace tailWord_7850034 prefixEnd_7850034 1343613532045548313191119 := by
  unfold tailWord_7850034
  simp only [CollatzResearch.WordTrace]
  refine ⟨71578565410668742978849289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190876174428449981276931437 71578565410668742978849289)
  ·
    refine ⟨53683924058001557234136967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71578565410668742978849289 53683924058001557234136967)
    ·
      refine ⟨80525886087002335851205451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53683924058001557234136967 80525886087002335851205451)
      ·
        refine ⟨120788829130503503776808177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80525886087002335851205451 120788829130503503776808177)
        ·
          refine ⟨90591621847877627832606133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120788829130503503776808177 90591621847877627832606133)
          ·
            refine ⟨8492964548238527609306825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 90591621847877627832606133 8492964548238527609306825)
            ·
              refine ⟨6369723411178895706980119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8492964548238527609306825 6369723411178895706980119)
              ·
                refine ⟨9554585116768343560470179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6369723411178895706980119 9554585116768343560470179)
                ·
                  refine ⟨14331877675152515340705269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9554585116768343560470179 14331877675152515340705269)
                  ·
                    refine ⟨1343613532045548313191119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14331877675152515340705269 1343613532045548313191119)
                    ·
                      rfl

theorem cell23_7850034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 2, 1, 1, 5].length) (baseStart_7850034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7850034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7850034 prefixEnd_7850034 := by exact prefixLift 7850034
  have htrace : WordTrace (prefixWord ++ tailWord_7850034) baseStart_7850034 baseEnd_7850034 := by
    simpa [prefixWord, tailWord_7850034, baseEnd_7850034] using wordTrace_append hprefix tailTrace_7850034
  have hstable : (prefixWord ++ tailWord_7850034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7850034).length < 2 ^ (prefixWord ++ tailWord_7850034).sum := by decide
  have hdescent : baseEnd_7850034 < baseStart_7850034 := by decide
  rcases family_descends (prefixWord ++ tailWord_7850034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7850047 : List Nat := [1, 1, 2, 2, 3, 1, 5, 2, 2, 4]
def baseStart_7850047 : Nat := 118140960795 + 7850047 * 2 ^ 59
def prefixEnd_7850047 : Nat := 4983230072969 + 3 ^ 40 * 7850047 * 2
def baseEnd_7850047 : Nat := 1343615757128384462903599

theorem tailTrace_7850047 : CollatzResearch.WordTrace tailWord_7850047 prefixEnd_7850047 1343615757128384462903599 := by
  unfold tailWord_7850047
  simp only [CollatzResearch.WordTrace]
  refine ⟨286314735791627875135620395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190876490527751916757080263 286314735791627875135620395)
  ·
    refine ⟨429472103687441812703430593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286314735791627875135620395 429472103687441812703430593)
    ·
      refine ⟨322104077765581359527572945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 429472103687441812703430593 322104077765581359527572945)
      ·
        refine ⟨241578058324186019645679709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 322104077765581359527572945 241578058324186019645679709)
        ·
          refine ⟨90591771871569757367129891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 241578058324186019645679709 90591771871569757367129891)
          ·
            refine ⟨135887657807354636050694837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90591771871569757367129891 135887657807354636050694837)
            ·
              refine ⟨12739467919439497129752641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 135887657807354636050694837 12739467919439497129752641)
              ·
                refine ⟨9554600939579622847314481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12739467919439497129752641 9554600939579622847314481)
                ·
                  refine ⟨7165950704684717135485861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9554600939579622847314481 7165950704684717135485861)
                  ·
                    refine ⟨1343615757128384462903599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7165950704684717135485861 1343615757128384462903599)
                    ·
                      rfl

theorem cell23_7850047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 5, 2, 2, 4].length) (baseStart_7850047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7850047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7850047 prefixEnd_7850047 := by exact prefixLift 7850047
  have htrace : WordTrace (prefixWord ++ tailWord_7850047) baseStart_7850047 baseEnd_7850047 := by
    simpa [prefixWord, tailWord_7850047, baseEnd_7850047] using wordTrace_append hprefix tailTrace_7850047
  have hstable : (prefixWord ++ tailWord_7850047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7850047).length < 2 ^ (prefixWord ++ tailWord_7850047).sum := by decide
  have hdescent : baseEnd_7850047 < baseStart_7850047 := by decide
  rcases family_descends (prefixWord ++ tailWord_7850047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7850053 : List Nat := [1, 3, 1, 1, 1, 3, 1, 1, 2, 2, 7]
def baseStart_7850053 : Nat := 118140960795 + 7850053 * 2 ^ 59
def prefixEnd_7850053 : Nat := 4983230072969 + 3 ^ 40 * 7850053 * 2
def baseEnd_7850053 : Nat := 4030850352269080365235769

theorem tailTrace_7850053 : CollatzResearch.WordTrace tailWord_7850053 prefixEnd_7850053 4030850352269080365235769 := by
  unfold tailWord_7850053
  simp only [CollatzResearch.WordTrace]
  refine ⟨286314954629606138160338813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190876636419737425440225875 286314954629606138160338813)
  ·
    refine ⟨107368107986102301810127055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 286314954629606138160338813 107368107986102301810127055)
    ·
      refine ⟨161052161979153452715190583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107368107986102301810127055 161052161979153452715190583)
      ·
        refine ⟨241578242968730179072785875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161052161979153452715190583 241578242968730179072785875)
        ·
          refine ⟨362367364453095268609178813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241578242968730179072785875 362367364453095268609178813)
          ·
            refine ⟨135887761669910725728442055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 362367364453095268609178813 135887761669910725728442055)
            ·
              refine ⟨203831642504866088592663083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135887761669910725728442055 203831642504866088592663083)
              ·
                refine ⟨305747463757299132888994625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 203831642504866088592663083 305747463757299132888994625)
                ·
                  refine ⟨229310597817974349666745969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 305747463757299132888994625 229310597817974349666745969)
                  ·
                    refine ⟨171982948363480762250059477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 229310597817974349666745969 171982948363480762250059477)
                    ·
                      refine ⟨4030850352269080365235769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 171982948363480762250059477 4030850352269080365235769)
                      ·
                        rfl

theorem cell23_7850053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 2, 2, 7].length) (baseStart_7850053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7850053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7850053 prefixEnd_7850053 := by exact prefixLift 7850053
  have htrace : WordTrace (prefixWord ++ tailWord_7850053) baseStart_7850053 baseEnd_7850053 := by
    simpa [prefixWord, tailWord_7850053, baseEnd_7850053] using wordTrace_append hprefix tailTrace_7850053
  have hstable : (prefixWord ++ tailWord_7850053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7850053).length < 2 ^ (prefixWord ++ tailWord_7850053).sum := by decide
  have hdescent : baseEnd_7850053 < baseStart_7850053 := by decide
  rcases family_descends (prefixWord ++ tailWord_7850053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7850063 : List Nat := [1, 1, 2, 1, 1, 2, 2, 3, 2, 2, 6]
def baseStart_7850063 : Nat := 118140960795 + 7850063 * 2 ^ 59
def prefixEnd_7850063 : Nat := 4983230072969 + 3 ^ 40 * 7850063 * 2
def baseEnd_7850063 : Nat := 4030855487075625326110723

theorem tailTrace_7850063 : CollatzResearch.WordTrace tailWord_7850063 prefixEnd_7850063 4030855487075625326110723 := by
  unfold tailWord_7850063
  simp only [CollatzResearch.WordTrace]
  refine ⟨286315319359569909868202843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190876879573046606578801895 286315319359569909868202843)
  ·
    refine ⟨429472979039354864802304265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286315319359569909868202843 429472979039354864802304265)
    ·
      refine ⟨322104734279516148601728199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 429472979039354864802304265 322104734279516148601728199)
      ·
        refine ⟨483157101419274222902592299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322104734279516148601728199 483157101419274222902592299)
        ·
          refine ⟨724735652128911334353888449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 483157101419274222902592299 724735652128911334353888449)
          ·
            refine ⟨543551739096683500765416337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 724735652128911334353888449 543551739096683500765416337)
            ·
              refine ⟨407663804322512625574062253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 543551739096683500765416337 407663804322512625574062253)
              ·
                refine ⟨152873926620942234590273345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 407663804322512625574062253 152873926620942234590273345)
                ·
                  refine ⟨114655444965706675942705009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 152873926620942234590273345 114655444965706675942705009)
                  ·
                    refine ⟨85991583724280006957028757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 114655444965706675942705009 85991583724280006957028757)
                    ·
                      refine ⟨4030855487075625326110723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85991583724280006957028757 4030855487075625326110723)
                      ·
                        rfl

theorem cell23_7850063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 2, 2, 6].length) (baseStart_7850063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7850063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7850063 prefixEnd_7850063 := by exact prefixLift 7850063
  have htrace : WordTrace (prefixWord ++ tailWord_7850063) baseStart_7850063 baseEnd_7850063 := by
    simpa [prefixWord, tailWord_7850063, baseEnd_7850063] using wordTrace_append hprefix tailTrace_7850063
  have hstable : (prefixWord ++ tailWord_7850063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7850063).length < 2 ^ (prefixWord ++ tailWord_7850063).sum := by decide
  have hdescent : baseEnd_7850063 < baseStart_7850063 := by decide
  rcases family_descends (prefixWord ++ tailWord_7850063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7850077 : List Nat := [1, 4, 4, 1, 1, 2, 1, 9]
def baseStart_7850077 : Nat := 118140960795 + 7850077 * 2 ^ 59
def prefixEnd_7850077 : Nat := 4983230072969 + 3 ^ 40 * 7850077 * 2
def baseEnd_7850077 : Nat := 149291210214992158197617

theorem tailTrace_7850077 : CollatzResearch.WordTrace tailWord_7850077 prefixEnd_7850077 149291210214992158197617 := by
  unfold tailWord_7850077
  simp only [CollatzResearch.WordTrace]
  refine ⟨286315829981519190259212485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190877219987679460172808323 286315829981519190259212485)
  ·
    refine ⟨53684218121534848173602341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 286315829981519190259212485 53684218121534848173602341)
    ·
      refine ⟨10065790897787784032550439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53684218121534848173602341 10065790897787784032550439)
      ·
        refine ⟨15098686346681676048825659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10065790897787784032550439 15098686346681676048825659)
        ·
          refine ⟨22648029520022514073238489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15098686346681676048825659 22648029520022514073238489)
          ·
            refine ⟨16986022140016885554928867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22648029520022514073238489 16986022140016885554928867)
            ·
              refine ⟨25479033210025328332393301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16986022140016885554928867 25479033210025328332393301)
              ·
                refine ⟨149291210214992158197617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25479033210025328332393301 149291210214992158197617)
                ·
                  rfl

theorem cell23_7850077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 9].length) (baseStart_7850077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7850077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7850077 prefixEnd_7850077 := by exact prefixLift 7850077
  have htrace : WordTrace (prefixWord ++ tailWord_7850077) baseStart_7850077 baseEnd_7850077 := by
    simpa [prefixWord, tailWord_7850077, baseEnd_7850077] using wordTrace_append hprefix tailTrace_7850077
  have hstable : (prefixWord ++ tailWord_7850077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7850077).length < 2 ^ (prefixWord ++ tailWord_7850077).sum := by decide
  have hdescent : baseEnd_7850077 < baseStart_7850077 := by decide
  rcases family_descends (prefixWord ++ tailWord_7850077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7850087 : List Nat := [1, 1, 5, 1, 1, 2, 1, 1, 6, 1, 3]
def baseStart_7850087 : Nat := 118140960795 + 7850087 * 2 ^ 59
def prefixEnd_7850087 : Nat := 4983230072969 + 3 ^ 40 * 7850087 * 2
def baseEnd_7850087 : Nat := 4030867810611333232210613

theorem tailTrace_7850087 : CollatzResearch.WordTrace tailWord_7850087 prefixEnd_7850087 4030867810611333232210613 := by
  unfold tailWord_7850087
  simp only [CollatzResearch.WordTrace]
  refine ⟨286316194711482961967076515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190877463140988641311384343 286316194711482961967076515)
  ·
    refine ⟨429474292067224442950614773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286316194711482961967076515 429474292067224442950614773)
    ·
      refine ⟨40263214881302291526620135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 429474292067224442950614773 40263214881302291526620135)
      ·
        refine ⟨60394822321953437289930203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40263214881302291526620135 60394822321953437289930203)
        ·
          refine ⟨90592233482930155934895305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60394822321953437289930203 90592233482930155934895305)
          ·
            refine ⟨67944175112197616951171479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90592233482930155934895305 67944175112197616951171479)
            ·
              refine ⟨101916262668296425426757219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67944175112197616951171479 101916262668296425426757219)
              ·
                refine ⟨152874394002444638140135829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101916262668296425426757219 152874394002444638140135829)
                ·
                  refine ⟨7165987218864592412818867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 152874394002444638140135829 7165987218864592412818867)
                  ·
                    refine ⟨10748980828296888619228301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7165987218864592412818867 10748980828296888619228301)
                    ·
                      refine ⟨4030867810611333232210613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10748980828296888619228301 4030867810611333232210613)
                      ·
                        rfl

theorem cell23_7850087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 1, 6, 1, 3].length) (baseStart_7850087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7850087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7850087 prefixEnd_7850087 := by exact prefixLift 7850087
  have htrace : WordTrace (prefixWord ++ tailWord_7850087) baseStart_7850087 baseEnd_7850087 := by
    simpa [prefixWord, tailWord_7850087, baseEnd_7850087] using wordTrace_append hprefix tailTrace_7850087
  have hstable : (prefixWord ++ tailWord_7850087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7850087).length < 2 ^ (prefixWord ++ tailWord_7850087).sum := by decide
  have hdescent : baseEnd_7850087 < baseStart_7850087 := by decide
  rcases family_descends (prefixWord ++ tailWord_7850087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7850144 : List Nat := [2, 1, 1, 4, 2, 3, 1, 2, 1, 4, 2]
def baseStart_7850144 : Nat := 118140960795 + 7850144 * 2 ^ 59
def prefixEnd_7850144 : Nat := 4983230072969 + 3 ^ 40 * 7850144 * 2
def baseEnd_7850144 : Nat := 4030897079008639509197851

theorem tailTrace_7850144 : CollatzResearch.WordTrace tailWord_7850144 prefixEnd_7850144 4030897079008639509197851 := by
  unfold tailWord_7850144
  simp only [CollatzResearch.WordTrace]
  refine ⟨143159136836138230350950743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190878849114850973801267657 143159136836138230350950743)
  ·
    refine ⟨214738705254207345526426115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143159136836138230350950743 214738705254207345526426115)
    ·
      refine ⟨322108057881311018289639173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214738705254207345526426115 322108057881311018289639173)
      ·
        refine ⟨60395260852745815929307345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 322108057881311018289639173 60395260852745815929307345)
        ·
          refine ⟨45296445639559361946980509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60395260852745815929307345 45296445639559361946980509)
          ·
            refine ⟨16986167114834760730117691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45296445639559361946980509 16986167114834760730117691)
            ·
              refine ⟨25479250672252141095176537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16986167114834760730117691 25479250672252141095176537)
              ·
                refine ⟨19109438004189105821382403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25479250672252141095176537 19109438004189105821382403)
                ·
                  refine ⟨28664157006283658732073605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19109438004189105821382403 28664157006283658732073605)
                  ·
                    refine ⟨5374529438678186012263801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28664157006283658732073605 5374529438678186012263801)
                    ·
                      refine ⟨4030897079008639509197851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5374529438678186012263801 4030897079008639509197851)
                      ·
                        rfl

theorem cell23_7850144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 2, 1, 4, 2].length) (baseStart_7850144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7850144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7850144 prefixEnd_7850144 := by exact prefixLift 7850144
  have htrace : WordTrace (prefixWord ++ tailWord_7850144) baseStart_7850144 baseEnd_7850144 := by
    simpa [prefixWord, tailWord_7850144, baseEnd_7850144] using wordTrace_append hprefix tailTrace_7850144
  have hstable : (prefixWord ++ tailWord_7850144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7850144).length < 2 ^ (prefixWord ++ tailWord_7850144).sum := by decide
  have hdescent : baseEnd_7850144 < baseStart_7850144 := by decide
  rcases family_descends (prefixWord ++ tailWord_7850144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7850148 : List Nat := [2, 3, 1, 2, 4, 1, 3, 1, 1, 3, 2]
def baseStart_7850148 : Nat := 118140960795 + 7850148 * 2 ^ 59
def prefixEnd_7850148 : Nat := 4983230072969 + 3 ^ 40 * 7850148 * 2
def baseEnd_7850148 : Nat := 4030899132931257493547833

theorem tailTrace_7850148 : CollatzResearch.WordTrace tailWord_7850148 prefixEnd_7850148 4030899132931257493547833 := by
  unfold tailWord_7850148
  simp only [CollatzResearch.WordTrace]
  refine ⟨143159209782130984692523549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190878946376174646256698065 143159209782130984692523549)
  ·
    refine ⟨53684703668299119259696331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143159209782130984692523549 53684703668299119259696331)
    ·
      refine ⟨80527055502448678889544497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53684703668299119259696331 80527055502448678889544497)
      ·
        refine ⟨60395291626836509167158373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80527055502448678889544497 60395291626836509167158373)
        ·
          refine ⟨11324117180031845468842195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60395291626836509167158373 11324117180031845468842195)
          ·
            refine ⟨16986175770047768203263293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11324117180031845468842195 16986175770047768203263293)
            ·
              refine ⟨6369815913767913076223735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16986175770047768203263293 6369815913767913076223735)
              ·
                refine ⟨9554723870651869614335603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6369815913767913076223735 9554723870651869614335603)
                ·
                  refine ⟨14332085805977804421503405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9554723870651869614335603 14332085805977804421503405)
                  ·
                    refine ⟨5374532177241676658063777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14332085805977804421503405 5374532177241676658063777)
                    ·
                      refine ⟨4030899132931257493547833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5374532177241676658063777 4030899132931257493547833)
                      ·
                        rfl

theorem cell23_7850148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 3, 1, 1, 3, 2].length) (baseStart_7850148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7850148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7850148 prefixEnd_7850148 := by exact prefixLift 7850148
  have htrace : WordTrace (prefixWord ++ tailWord_7850148) baseStart_7850148 baseEnd_7850148 := by
    simpa [prefixWord, tailWord_7850148, baseEnd_7850148] using wordTrace_append hprefix tailTrace_7850148
  have hstable : (prefixWord ++ tailWord_7850148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7850148).length < 2 ^ (prefixWord ++ tailWord_7850148).sum := by decide
  have hdescent : baseEnd_7850148 < baseStart_7850148 := by decide
  rcases family_descends (prefixWord ++ tailWord_7850148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7850174 : List Nat := [4, 2, 1, 1, 4, 1, 1, 1, 2, 2, 4]
def baseStart_7850174 : Nat := 118140960795 + 7850174 * 2 ^ 59
def prefixEnd_7850174 : Nat := 4983230072969 + 3 ^ 40 * 7850174 * 2
def baseEnd_7850174 : Nat := 4030912483428274391822713

theorem tailTrace_7850174 : CollatzResearch.WordTrace tailWord_7850174 prefixEnd_7850174 4030912483428274391822713 := by
  unfold tailWord_7850174
  simp only [CollatzResearch.WordTrace]
  refine ⟨35789920982770971978186697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 190879578574778517216995717 35789920982770971978186697)
  ·
    refine ⟨26842440737078228983640023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35789920982770971978186697 26842440737078228983640023)
    ·
      refine ⟨40263661105617343475460035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26842440737078228983640023 40263661105617343475460035)
      ·
        refine ⟨60395491658426015213190053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40263661105617343475460035 60395491658426015213190053)
        ·
          refine ⟨11324154685954877852473135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60395491658426015213190053 11324154685954877852473135)
          ·
            refine ⟨16986232028932316778709703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11324154685954877852473135 16986232028932316778709703)
            ·
              refine ⟨25479348043398475168064555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16986232028932316778709703 25479348043398475168064555)
              ·
                refine ⟨38219022065097712752096833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25479348043398475168064555 38219022065097712752096833)
                ·
                  refine ⟨28664266548823284564072625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38219022065097712752096833 28664266548823284564072625)
                  ·
                    refine ⟨21498199911617463423054469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28664266548823284564072625 21498199911617463423054469)
                    ·
                      refine ⟨4030912483428274391822713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21498199911617463423054469 4030912483428274391822713)
                      ·
                        rfl

theorem cell23_7850174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 1, 2, 2, 4].length) (baseStart_7850174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7850174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7850174 prefixEnd_7850174 := by exact prefixLift 7850174
  have htrace : WordTrace (prefixWord ++ tailWord_7850174) baseStart_7850174 baseEnd_7850174 := by
    simpa [prefixWord, tailWord_7850174, baseEnd_7850174] using wordTrace_append hprefix tailTrace_7850174
  have hstable : (prefixWord ++ tailWord_7850174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7850174).length < 2 ^ (prefixWord ++ tailWord_7850174).sum := by decide
  have hdescent : baseEnd_7850174 < baseStart_7850174 := by decide
  rcases family_descends (prefixWord ++ tailWord_7850174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7850178 : List Nat := [3, 5, 1, 1, 1, 1, 1, 3, 1, 4, 2]
def baseStart_7850178 : Nat := 118140960795 + 7850178 * 2 ^ 59
def prefixEnd_7850178 : Nat := 4983230072969 + 3 ^ 40 * 7850178 * 2
def baseEnd_7850178 : Nat := 4030914537350892376172695

theorem tailTrace_7850178 : CollatzResearch.WordTrace tailWord_7850178 prefixEnd_7850178 4030914537350892376172695 := by
  unfold tailWord_7850178
  simp only [CollatzResearch.WordTrace]
  refine ⟨71579878438538321127159797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190879675836102189672426125 71579878438538321127159797)
  ·
    refine ⟨6710613603612967605671231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 71579878438538321127159797 6710613603612967605671231)
    ·
      refine ⟨10065920405419451408506847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6710613603612967605671231 10065920405419451408506847)
      ·
        refine ⟨15098880608129177112760271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10065920405419451408506847 15098880608129177112760271)
        ·
          refine ⟨22648320912193765669140407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15098880608129177112760271 22648320912193765669140407)
          ·
            refine ⟨33972481368290648503710611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22648320912193765669140407 33972481368290648503710611)
            ·
              refine ⟨50958722052435972755565917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33972481368290648503710611 50958722052435972755565917)
              ·
                refine ⟨19109520769663489783337219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50958722052435972755565917 19109520769663489783337219)
                ·
                  refine ⟨28664281154495234675005829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19109520769663489783337219 28664281154495234675005829)
                  ·
                    refine ⟨5374552716467856501563593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28664281154495234675005829 5374552716467856501563593)
                    ·
                      refine ⟨4030914537350892376172695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5374552716467856501563593 4030914537350892376172695)
                      ·
                        rfl

theorem cell23_7850178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 3, 1, 4, 2].length) (baseStart_7850178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7850178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7850178 prefixEnd_7850178 := by exact prefixLift 7850178
  have htrace : WordTrace (prefixWord ++ tailWord_7850178) baseStart_7850178 baseEnd_7850178 := by
    simpa [prefixWord, tailWord_7850178, baseEnd_7850178] using wordTrace_append hprefix tailTrace_7850178
  have hstable : (prefixWord ++ tailWord_7850178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7850178).length < 2 ^ (prefixWord ++ tailWord_7850178).sum := by decide
  have hdescent : baseEnd_7850178 < baseStart_7850178 := by decide
  rcases family_descends (prefixWord ++ tailWord_7850178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7850187 : List Nat := [1, 1, 1, 1, 3, 2, 3, 2, 2, 5, 2]
def baseStart_7850187 : Nat := 118140960795 + 7850187 * 2 ^ 59
def prefixEnd_7850187 : Nat := 4983230072969 + 3 ^ 40 * 7850187 * 2
def baseEnd_7850187 : Nat := 4030919158676782840960153

theorem tailTrace_7850187 : CollatzResearch.WordTrace tailWord_7850187 prefixEnd_7850187 4030919158676782840960153 := by
  unfold tailWord_7850187
  simp only [CollatzResearch.WordTrace]
  refine ⟨286319842011120679045716815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190879894674080452697144543 286319842011120679045716815)
  ·
    refine ⟨429479763016681018568575223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286319842011120679045716815 429479763016681018568575223)
    ·
      refine ⟨644219644525021527852862835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 429479763016681018568575223 644219644525021527852862835)
      ·
        refine ⟨966329466787532291779294253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 644219644525021527852862835 966329466787532291779294253)
        ·
          refine ⟨362373550045324609417235345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 966329466787532291779294253 362373550045324609417235345)
          ·
            refine ⟨271780162533993457062926509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 362373550045324609417235345 271780162533993457062926509)
            ·
              refine ⟨101917560950247546398597441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 271780162533993457062926509 101917560950247546398597441)
              ·
                refine ⟨76438170712685659798948081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101917560950247546398597441 76438170712685659798948081)
                ·
                  refine ⟨57328628034514244849211061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76438170712685659798948081 57328628034514244849211061)
                  ·
                    refine ⟨5374558878235710454613537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57328628034514244849211061 5374558878235710454613537)
                    ·
                      refine ⟨4030919158676782840960153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5374558878235710454613537 4030919158676782840960153)
                      ·
                        rfl

theorem cell23_7850187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 2, 2, 5, 2].length) (baseStart_7850187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7850187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7850187 prefixEnd_7850187 := by exact prefixLift 7850187
  have htrace : WordTrace (prefixWord ++ tailWord_7850187) baseStart_7850187 baseEnd_7850187 := by
    simpa [prefixWord, tailWord_7850187, baseEnd_7850187] using wordTrace_append hprefix tailTrace_7850187
  have hstable : (prefixWord ++ tailWord_7850187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7850187).length < 2 ^ (prefixWord ++ tailWord_7850187).sum := by decide
  have hdescent : baseEnd_7850187 < baseStart_7850187 := by decide
  rcases family_descends (prefixWord ++ tailWord_7850187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7850217 : List Nat := [1, 2, 1, 1, 1, 2, 2, 2, 3, 6, 2]
def baseStart_7850217 : Nat := 118140960795 + 7850217 * 2 ^ 59
def prefixEnd_7850217 : Nat := 4983230072969 + 3 ^ 40 * 7850217 * 2
def baseEnd_7850217 : Nat := 4030934563096417723585015

theorem tailTrace_7850217 : CollatzResearch.WordTrace tailWord_7850217 prefixEnd_7850217 4030934563096417723585015 := by
  unfold tailWord_7850217
  simp only [CollatzResearch.WordTrace]
  refine ⟨286320936201011994169308905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190880624134007996112872603 286320936201011994169308905)
  ·
    refine ⟨214740702150758995626981679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286320936201011994169308905 214740702150758995626981679)
    ·
      refine ⟨322111053226138493440472519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214740702150758995626981679 322111053226138493440472519)
      ·
        refine ⟨483166579839207740160708779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322111053226138493440472519 483166579839207740160708779)
        ·
          refine ⟨724749869758811610241063169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 483166579839207740160708779 724749869758811610241063169)
          ·
            refine ⟨543562402319108707680797377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 724749869758811610241063169 543562402319108707680797377)
            ·
              refine ⟨407671801739331530760598033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 543562402319108707680797377 407671801739331530760598033)
              ·
                refine ⟨305753851304498648070448525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 407671801739331530760598033 305753851304498648070448525)
                ·
                  refine ⟨114657694239186993026418197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 305753851304498648070448525 114657694239186993026418197)
                  ·
                    refine ⟨5374579417461890298113353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 114657694239186993026418197 5374579417461890298113353)
                    ·
                      refine ⟨4030934563096417723585015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5374579417461890298113353 4030934563096417723585015)
                      ·
                        rfl

theorem cell23_7850217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 3, 6, 2].length) (baseStart_7850217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7850217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7850217 prefixEnd_7850217 := by exact prefixLift 7850217
  have htrace : WordTrace (prefixWord ++ tailWord_7850217) baseStart_7850217 baseEnd_7850217 := by
    simpa [prefixWord, tailWord_7850217, baseEnd_7850217] using wordTrace_append hprefix tailTrace_7850217
  have hstable : (prefixWord ++ tailWord_7850217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7850217).length < 2 ^ (prefixWord ++ tailWord_7850217).sum := by decide
  have hdescent : baseEnd_7850217 < baseStart_7850217 := by decide
  rcases family_descends (prefixWord ++ tailWord_7850217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7850234 : List Nat := [3, 1, 1, 1, 1, 5, 2, 1, 2, 4, 2]
def baseStart_7850234 : Nat := 118140960795 + 7850234 * 2 ^ 59
def prefixEnd_7850234 : Nat := 4983230072969 + 3 ^ 40 * 7850234 * 2
def baseEnd_7850234 : Nat := 4030943292267544157072437

theorem tailTrace_7850234 : CollatzResearch.WordTrace tailWord_7850234 prefixEnd_7850234 4030943292267544157072437 := by
  unfold tailWord_7850234
  simp only [CollatzResearch.WordTrace]
  refine ⟨71580389060487601518169439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190881037494633604048451837 71580389060487601518169439)
  ·
    refine ⟨107370583590731402277254159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71580389060487601518169439 107370583590731402277254159)
    ·
      refine ⟨161055875386097103415881239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107370583590731402277254159 161055875386097103415881239)
      ·
        refine ⟨241583813079145655123821859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161055875386097103415881239 241583813079145655123821859)
        ·
          refine ⟨362375719618718482685732789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241583813079145655123821859 362375719618718482685732789)
          ·
            refine ⟨33972723714254857751787449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 362375719618718482685732789 33972723714254857751787449)
            ·
              refine ⟨25479542785691143313840587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33972723714254857751787449 25479542785691143313840587)
              ·
                refine ⟨38219314178536714970760881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25479542785691143313840587 38219314178536714970760881)
                ·
                  refine ⟨28664485633902536228070661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38219314178536714970760881 28664485633902536228070661)
                  ·
                    refine ⟨5374591056356725542763249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28664485633902536228070661 5374591056356725542763249)
                    ·
                      refine ⟨4030943292267544157072437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5374591056356725542763249 4030943292267544157072437)
                      ·
                        rfl

theorem cell23_7850234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 1, 2, 4, 2].length) (baseStart_7850234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7850234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7850234 prefixEnd_7850234 := by exact prefixLift 7850234
  have htrace : WordTrace (prefixWord ++ tailWord_7850234) baseStart_7850234 baseEnd_7850234 := by
    simpa [prefixWord, tailWord_7850234, baseEnd_7850234] using wordTrace_append hprefix tailTrace_7850234
  have hstable : (prefixWord ++ tailWord_7850234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7850234).length < 2 ^ (prefixWord ++ tailWord_7850234).sum := by decide
  have hdescent : baseEnd_7850234 < baseStart_7850234 := by decide
  rcases family_descends (prefixWord ++ tailWord_7850234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7850254 : List Nat := [4, 1, 1, 2, 1, 2, 2, 3, 2, 2, 3]
def baseStart_7850254 : Nat := 118140960795 + 7850254 * 2 ^ 59
def prefixEnd_7850254 : Nat := 4983230072969 + 3 ^ 40 * 7850254 * 2
def baseEnd_7850254 : Nat := 4030953561880634078822345

theorem tailTrace_7850254 : CollatzResearch.WordTrace tailWord_7850254 prefixEnd_7850254 4030953561880634078822345 := by
  unfold tailWord_7850254
  simp only [CollatzResearch.WordTrace]
  refine ⟨35790285712734743686050727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 190881523801251966325603877 35790285712734743686050727)
  ·
    refine ⟨53685428569102115529076091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35790285712734743686050727 53685428569102115529076091)
    ·
      refine ⟨80528142853653173293614137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53685428569102115529076091 80528142853653173293614137)
      ·
        refine ⟨60396107140239879970210603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80528142853653173293614137 60396107140239879970210603)
        ·
          refine ⟨90594160710359819955315905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60396107140239879970210603 90594160710359819955315905)
          ·
            refine ⟨67945620532769864966486929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90594160710359819955315905 67945620532769864966486929)
            ·
              refine ⟨50959215399577398724865197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67945620532769864966486929 50959215399577398724865197)
              ·
                refine ⟨19109705774841524521824449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50959215399577398724865197 19109705774841524521824449)
                ·
                  refine ⟨14332279331131143391368337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19109705774841524521824449 14332279331131143391368337)
                  ·
                    refine ⟨10749209498348357543526253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14332279331131143391368337 10749209498348357543526253)
                    ·
                      refine ⟨4030953561880634078822345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10749209498348357543526253 4030953561880634078822345)
                      ·
                        rfl

theorem cell23_7850254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 3, 2, 2, 3].length) (baseStart_7850254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7850254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7850254 prefixEnd_7850254 := by exact prefixLift 7850254
  have htrace : WordTrace (prefixWord ++ tailWord_7850254) baseStart_7850254 baseEnd_7850254 := by
    simpa [prefixWord, tailWord_7850254, baseEnd_7850254] using wordTrace_append hprefix tailTrace_7850254
  have hstable : (prefixWord ++ tailWord_7850254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7850254).length < 2 ^ (prefixWord ++ tailWord_7850254).sum := by decide
  have hdescent : baseEnd_7850254 < baseStart_7850254 := by decide
  rcases family_descends (prefixWord ++ tailWord_7850254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7850261 : List Nat := [1, 3, 2, 1, 2, 1, 5, 3, 1, 4]
def baseStart_7850261 : Nat := 118140960795 + 7850261 * 2 ^ 59
def prefixEnd_7850261 : Nat := 4983230072969 + 3 ^ 40 * 7850261 * 2
def baseEnd_7850261 : Nat := 1343652385415071850478271

theorem tailTrace_7850261 : CollatzResearch.WordTrace tailWord_7850261 prefixEnd_7850261 1343652385415071850478271 := by
  unfold tailWord_7850261
  simp only [CollatzResearch.WordTrace]
  refine ⟨286322541012852589683910637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190881694008568393122607091 286322541012852589683910637)
  ·
    refine ⟨107370952879819721131466489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 286322541012852589683910637 107370952879819721131466489)
    ·
      refine ⟨80528214659864790848599867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107370952879819721131466489 80528214659864790848599867)
      ·
        refine ⟨120792321989797186272899801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80528214659864790848599867 120792321989797186272899801)
        ·
          refine ⟨90594241492347889704674851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120792321989797186272899801 90594241492347889704674851)
          ·
            refine ⟨135891362238521834557012277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90594241492347889704674851 135891362238521834557012277)
            ·
              refine ⟨12739815209861421989719901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 135891362238521834557012277 12739815209861421989719901)
              ·
                refine ⟨4777430703698033246144963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12739815209861421989719901 4777430703698033246144963)
                ·
                  refine ⟨7166146055547049869217445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4777430703698033246144963 7166146055547049869217445)
                  ·
                    refine ⟨1343652385415071850478271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7166146055547049869217445 1343652385415071850478271)
                    ·
                      rfl

theorem cell23_7850261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 5, 3, 1, 4].length) (baseStart_7850261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7850261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7850261 prefixEnd_7850261 := by exact prefixLift 7850261
  have htrace : WordTrace (prefixWord ++ tailWord_7850261) baseStart_7850261 baseEnd_7850261 := by
    simpa [prefixWord, tailWord_7850261, baseEnd_7850261] using wordTrace_append hprefix tailTrace_7850261
  have hstable : (prefixWord ++ tailWord_7850261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7850261).length < 2 ^ (prefixWord ++ tailWord_7850261).sum := by decide
  have hdescent : baseEnd_7850261 < baseStart_7850261 := by decide
  rcases family_descends (prefixWord ++ tailWord_7850261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7850311 : List Nat := [1, 1, 4, 1, 2, 2, 4, 1, 2, 3, 2]
def baseStart_7850311 : Nat := 118140960795 + 7850311 * 2 ^ 59
def prefixEnd_7850311 : Nat := 4983230072969 + 3 ^ 40 * 7850311 * 2
def baseEnd_7850311 : Nat := 4030982830277940355809583

theorem tailTrace_7850311 : CollatzResearch.WordTrace tailWord_7850311 prefixEnd_7850311 4030982830277940355809583 := by
  unfold tailWord_7850311
  simp only [CollatzResearch.WordTrace]
  refine ⟨286324364662671448223230787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190882909775114298815487191 286324364662671448223230787)
  ·
    refine ⟨429486546994007172334846181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286324364662671448223230787 429486546994007172334846181)
    ·
      refine ⟨80528727561376344812783659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 429486546994007172334846181 80528727561376344812783659)
      ·
        refine ⟨120793091342064517219175489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80528727561376344812783659 120793091342064517219175489)
        ·
          refine ⟨90594818506548387914381617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120793091342064517219175489 90594818506548387914381617)
          ·
            refine ⟨67946113879911290935786213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90594818506548387914381617 67946113879911290935786213)
            ·
              refine ⟨12739896352483367050459915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67946113879911290935786213 12739896352483367050459915)
              ·
                refine ⟨19109844528725050575689873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12739896352483367050459915 19109844528725050575689873)
                ·
                  refine ⟨14332383396543787931767405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19109844528725050575689873 14332383396543787931767405)
                  ·
                    refine ⟨5374643773703920474412777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14332383396543787931767405 5374643773703920474412777)
                    ·
                      refine ⟨4030982830277940355809583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5374643773703920474412777 4030982830277940355809583)
                      ·
                        rfl

theorem cell23_7850311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 4, 1, 2, 3, 2].length) (baseStart_7850311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7850311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7850311 prefixEnd_7850311 := by exact prefixLift 7850311
  have htrace : WordTrace (prefixWord ++ tailWord_7850311) baseStart_7850311 baseEnd_7850311 := by
    simpa [prefixWord, tailWord_7850311, baseEnd_7850311] using wordTrace_append hprefix tailTrace_7850311
  have hstable : (prefixWord ++ tailWord_7850311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7850311).length < 2 ^ (prefixWord ++ tailWord_7850311).sum := by decide
  have hdescent : baseEnd_7850311 < baseStart_7850311 := by decide
  rcases family_descends (prefixWord ++ tailWord_7850311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7850321 : List Nat := [1, 2, 2, 1, 4, 3, 3, 1, 1, 5]
def baseStart_7850321 : Nat := 118140960795 + 7850321 * 2 ^ 59
def prefixEnd_7850321 : Nat := 4983230072969 + 3 ^ 40 * 7850321 * 2
def baseEnd_7850321 : Nat := 1343662655028161772228179

theorem tailTrace_7850321 : CollatzResearch.WordTrace tailWord_7850321 prefixEnd_7850321 1343662655028161772228179 := by
  unfold tailWord_7850321
  simp only [CollatzResearch.WordTrace]
  refine ⟨286324729392635219931094817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190883152928423479954063211 286324729392635219931094817)
  ·
    refine ⟨214743547044476414948321113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286324729392635219931094817 214743547044476414948321113)
    ·
      refine ⟨161057660283357311211240835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214743547044476414948321113 161057660283357311211240835)
      ·
        refine ⟨241586490425035966816861253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161057660283357311211240835 241586490425035966816861253)
        ·
          refine ⟨45297466954694243778161485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 241586490425035966816861253 45297466954694243778161485)
          ·
            refine ⟨16986550108010341416810557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45297466954694243778161485 16986550108010341416810557)
            ·
              refine ⟨6369956290503878031303959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16986550108010341416810557 6369956290503878031303959)
              ·
                refine ⟨9554934435755817046955939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6369956290503878031303959 9554934435755817046955939)
                ·
                  refine ⟨14332401653633725570433909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9554934435755817046955939 14332401653633725570433909)
                  ·
                    refine ⟨1343662655028161772228179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14332401653633725570433909 1343662655028161772228179)
                    ·
                      rfl

theorem cell23_7850321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 3, 1, 1, 5].length) (baseStart_7850321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7850321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7850321 prefixEnd_7850321 := by exact prefixLift 7850321
  have htrace : WordTrace (prefixWord ++ tailWord_7850321) baseStart_7850321 baseEnd_7850321 := by
    simpa [prefixWord, tailWord_7850321, baseEnd_7850321] using wordTrace_append hprefix tailTrace_7850321
  have hstable : (prefixWord ++ tailWord_7850321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7850321).length < 2 ^ (prefixWord ++ tailWord_7850321).sum := by decide
  have hdescent : baseEnd_7850321 < baseStart_7850321 := by decide
  rcases family_descends (prefixWord ++ tailWord_7850321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7850354 : List Nat := [3, 2, 1, 2, 1, 3, 1, 3, 1, 2, 4]
def baseStart_7850354 : Nat := 118140960795 + 7850354 * 2 ^ 59
def prefixEnd_7850354 : Nat := 4983230072969 + 3 ^ 40 * 7850354 * 2
def baseEnd_7850354 : Nat := 4031004909946083687571885

theorem tailTrace_7850354 : CollatzResearch.WordTrace tailWord_7850354 prefixEnd_7850354 4031004909946083687571885 := by
  unfold tailWord_7850354
  simp only [CollatzResearch.WordTrace]
  refine ⟨71581483250378916641761529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190883955334343777711364077 71581483250378916641761529)
  ·
    refine ⟨53686112437784187481321147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71581483250378916641761529 53686112437784187481321147)
    ·
      refine ⟨80529168656676281221981721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53686112437784187481321147 80529168656676281221981721)
      ·
        refine ⟨60396876492507210916486291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80529168656676281221981721 60396876492507210916486291)
        ·
          refine ⟨90595314738760816374729437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60396876492507210916486291 90595314738760816374729437)
          ·
            refine ⟨33973243027035306140523539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90595314738760816374729437 33973243027035306140523539)
            ·
              refine ⟨50959864540552959210785309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33973243027035306140523539 50959864540552959210785309)
              ·
                refine ⟨19109949202707359704044491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50959864540552959210785309 19109949202707359704044491)
                ·
                  refine ⟨28664923804061039556066737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19109949202707359704044491 28664923804061039556066737)
                  ·
                    refine ⟨21498692853045779667050053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28664923804061039556066737 21498692853045779667050053)
                    ·
                      refine ⟨4031004909946083687571885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21498692853045779667050053 4031004909946083687571885)
                      ·
                        rfl

theorem cell23_7850354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 3, 1, 2, 4].length) (baseStart_7850354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7850354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7850354 prefixEnd_7850354 := by exact prefixLift 7850354
  have htrace : WordTrace (prefixWord ++ tailWord_7850354) baseStart_7850354 baseEnd_7850354 := by
    simpa [prefixWord, tailWord_7850354, baseEnd_7850354] using wordTrace_append hprefix tailTrace_7850354
  have hstable : (prefixWord ++ tailWord_7850354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7850354).length < 2 ^ (prefixWord ++ tailWord_7850354).sum := by decide
  have hdescent : baseEnd_7850354 < baseStart_7850354 := by decide
  rcases family_descends (prefixWord ++ tailWord_7850354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7850375 : List Nat := [1, 1, 4, 2, 2, 1, 4, 3, 1, 2, 2]
def baseStart_7850375 : Nat := 118140960795 + 7850375 * 2 ^ 59
def prefixEnd_7850375 : Nat := 4983230072969 + 3 ^ 40 * 7850375 * 2
def baseEnd_7850375 : Nat := 4031015693039828105409289

theorem tailTrace_7850375 : CollatzResearch.WordTrace tailWord_7850375 prefixEnd_7850375 4031015693039828105409289 := by
  unfold tailWord_7850375
  simp only [CollatzResearch.WordTrace]
  refine ⟨286326698934439587153560579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190884465956293058102373719 286326698934439587153560579)
  ·
    refine ⟨429490048401659380730340869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286326698934439587153560579 429490048401659380730340869)
    ·
      refine ⟨80529384075311133886938913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 429490048401659380730340869 80529384075311133886938913)
      ·
        refine ⟨60397038056483350415204185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80529384075311133886938913 60397038056483350415204185)
        ·
          refine ⟨45297778542362512811403139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60397038056483350415204185 45297778542362512811403139)
          ·
            refine ⟨67946667813543769217104709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45297778542362512811403139 67946667813543769217104709)
            ·
              refine ⟨12740000215039456728207133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67946667813543769217104709 12740000215039456728207133)
              ·
                refine ⟨4777500080639796273077675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12740000215039456728207133 4777500080639796273077675)
                ·
                  refine ⟨7166250120959694409616513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4777500080639796273077675 7166250120959694409616513)
                  ·
                    refine ⟨5374687590719770807212385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7166250120959694409616513 5374687590719770807212385)
                    ·
                      refine ⟨4031015693039828105409289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5374687590719770807212385 4031015693039828105409289)
                      ·
                        rfl

theorem cell23_7850375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 4, 3, 1, 2, 2].length) (baseStart_7850375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7850375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7850375 prefixEnd_7850375 := by exact prefixLift 7850375
  have htrace : WordTrace (prefixWord ++ tailWord_7850375) baseStart_7850375 baseEnd_7850375 := by
    simpa [prefixWord, tailWord_7850375, baseEnd_7850375] using wordTrace_append hprefix tailTrace_7850375
  have hstable : (prefixWord ++ tailWord_7850375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7850375).length < 2 ^ (prefixWord ++ tailWord_7850375).sum := by decide
  have hdescent : baseEnd_7850375 < baseStart_7850375 := by decide
  rcases family_descends (prefixWord ++ tailWord_7850375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7850408 : List Nat := [2, 1, 6, 1, 1, 1, 3, 1, 1, 3, 3]
def baseStart_7850408 : Nat := 118140960795 + 7850408 * 2 ^ 59
def prefixEnd_7850408 : Nat := 4983230072969 + 3 ^ 40 * 7850408 * 2
def baseEnd_7850408 : Nat := 4031032637901426476296637

theorem tailTrace_7850408 : CollatzResearch.WordTrace tailWord_7850408 prefixEnd_7850408 4031032637901426476296637 := by
  unfold tailWord_7850408
  simp only [CollatzResearch.WordTrace]
  refine ⟨143163951271660016894755939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190885268362213355859674585 143163951271660016894755939)
  ·
    refine ⟨214745926907490025342133909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143163951271660016894755939 214745926907490025342133909)
    ·
      refine ⟨10066215323788594937912527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 214745926907490025342133909 10066215323788594937912527)
      ·
        refine ⟨15099322985682892406868791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10066215323788594937912527 15099322985682892406868791)
        ·
          refine ⟨22648984478524338610303187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15099322985682892406868791 22648984478524338610303187)
          ·
            refine ⟨33973476717786507915454781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22648984478524338610303187 33973476717786507915454781)
            ·
              refine ⟨12740053769169940468295543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33973476717786507915454781 12740053769169940468295543)
              ·
                refine ⟨19110080653754910702443315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12740053769169940468295543 19110080653754910702443315)
                ·
                  refine ⟨28665120980632366053664973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19110080653754910702443315 28665120980632366053664973)
                  ·
                    refine ⟨10749420367737137270124365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28665120980632366053664973 10749420367737137270124365)
                    ·
                      refine ⟨4031032637901426476296637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10749420367737137270124365 4031032637901426476296637)
                      ·
                        rfl

theorem cell23_7850408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_7850408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7850408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7850408 prefixEnd_7850408 := by exact prefixLift 7850408
  have htrace : WordTrace (prefixWord ++ tailWord_7850408) baseStart_7850408 baseEnd_7850408 := by
    simpa [prefixWord, tailWord_7850408, baseEnd_7850408] using wordTrace_append hprefix tailTrace_7850408
  have hstable : (prefixWord ++ tailWord_7850408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7850408).length < 2 ^ (prefixWord ++ tailWord_7850408).sum := by decide
  have hdescent : baseEnd_7850408 < baseStart_7850408 := by decide
  rcases family_descends (prefixWord ++ tailWord_7850408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7850418 : List Nat := [3, 2, 1, 1, 1, 1, 6, 2, 1, 3, 2]
def baseStart_7850418 : Nat := 118140960795 + 7850418 * 2 ^ 59
def prefixEnd_7850418 : Nat := 4983230072969 + 3 ^ 40 * 7850418 * 2
def baseEnd_7850418 : Nat := 4031037772707971437171591

theorem tailTrace_7850418 : CollatzResearch.WordTrace tailWord_7850418 prefixEnd_7850418 4031037772707971437171591 := by
  unfold tailWord_7850418
  simp only [CollatzResearch.WordTrace]
  refine ⟨71582066818320951374343977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190885511515522536998250605 71582066818320951374343977)
  ·
    refine ⟨53686550113740713530757983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71582066818320951374343977 53686550113740713530757983)
    ·
      refine ⟨80529825170611070296136975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53686550113740713530757983 80529825170611070296136975)
      ·
        refine ⟨120794737755916605444205463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80529825170611070296136975 120794737755916605444205463)
        ·
          refine ⟨181192106633874908166308195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120794737755916605444205463 181192106633874908166308195)
          ·
            refine ⟨271788159950812362249462293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181192106633874908166308195 271788159950812362249462293)
            ·
              refine ⟨12740069997694329480443545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 271788159950812362249462293 12740069997694329480443545)
              ·
                refine ⟨9555052498270747110332659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12740069997694329480443545 9555052498270747110332659)
                ·
                  refine ⟨14332578747406120665498989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9555052498270747110332659 14332578747406120665498989)
                  ·
                    refine ⟨5374717030277295249562121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14332578747406120665498989 5374717030277295249562121)
                    ·
                      refine ⟨4031037772707971437171591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5374717030277295249562121 4031037772707971437171591)
                      ·
                        rfl

theorem cell23_7850418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 6, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 6, 2, 1, 3, 2].length) (baseStart_7850418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7850418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7850418 prefixEnd_7850418 := by exact prefixLift 7850418
  have htrace : WordTrace (prefixWord ++ tailWord_7850418) baseStart_7850418 baseEnd_7850418 := by
    simpa [prefixWord, tailWord_7850418, baseEnd_7850418] using wordTrace_append hprefix tailTrace_7850418
  have hstable : (prefixWord ++ tailWord_7850418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7850418).length < 2 ^ (prefixWord ++ tailWord_7850418).sum := by decide
  have hdescent : baseEnd_7850418 < baseStart_7850418 := by decide
  rcases family_descends (prefixWord ++ tailWord_7850418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7850447 : List Nat := [1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 9]
def baseStart_7850447 : Nat := 118140960795 + 7850447 * 2 ^ 59
def prefixEnd_7850447 : Nat := 4983230072969 + 3 ^ 40 * 7850447 * 2
def baseEnd_7850447 : Nat := 4031052663646951823708957

theorem tailTrace_7850447 : CollatzResearch.WordTrace tailWord_7850447 prefixEnd_7850447 4031052663646951823708957 := by
  unfold tailWord_7850447
  simp only [CollatzResearch.WordTrace]
  refine ⟨286329324990178743450181595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190886216660119162300121063 286329324990178743450181595)
  ·
    refine ⟨429493987485268115175272393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286329324990178743450181595 429493987485268115175272393)
    ·
      refine ⟨322120490613951086381454295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 429493987485268115175272393 322120490613951086381454295)
      ·
        refine ⟨483180735920926629572181443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322120490613951086381454295 483180735920926629572181443)
        ·
          refine ⟨724771103881389944358272165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 483180735920926629572181443 724771103881389944358272165)
          ·
            refine ⟨135894581977760614567176031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 724771103881389944358272165 135894581977760614567176031)
            ·
              refine ⟨203841872966640921850764047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135894581977760614567176031 203841872966640921850764047)
              ·
                refine ⟨305762809449961382776146071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 203841872966640921850764047 305762809449961382776146071)
                ·
                  refine ⟨458644214174942074164219107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 305762809449961382776146071 458644214174942074164219107)
                  ·
                    refine ⟨687966321262413111246328661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 458644214174942074164219107 687966321262413111246328661)
                    ·
                      refine ⟨4031052663646951823708957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 687966321262413111246328661 4031052663646951823708957)
                      ·
                        rfl

theorem cell23_7850447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 9].length) (baseStart_7850447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7850447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7850447 prefixEnd_7850447 := by exact prefixLift 7850447
  have htrace : WordTrace (prefixWord ++ tailWord_7850447) baseStart_7850447 baseEnd_7850447 := by
    simpa [prefixWord, tailWord_7850447, baseEnd_7850447] using wordTrace_append hprefix tailTrace_7850447
  have hstable : (prefixWord ++ tailWord_7850447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7850447).length < 2 ^ (prefixWord ++ tailWord_7850447).sum := by decide
  have hdescent : baseEnd_7850447 < baseStart_7850447 := by decide
  rcases family_descends (prefixWord ++ tailWord_7850447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7850464 : List Nat := [2, 1, 1, 3, 1, 1, 4, 1, 1, 5, 3]
def baseStart_7850464 : Nat := 118140960795 + 7850464 * 2 ^ 59
def prefixEnd_7850464 : Nat := 4983230072969 + 3 ^ 40 * 7850464 * 2
def baseEnd_7850464 : Nat := 4031061392818078257196379

theorem tailTrace_7850464 : CollatzResearch.WordTrace tailWord_7850464 prefixEnd_7850464 4031061392818078257196379 := by
  unfold tailWord_7850464
  simp only [CollatzResearch.WordTrace]
  refine ⟨143164972515558577676775223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190886630020744770235700297 143164972515558577676775223)
  ·
    refine ⟨214747458773337866515162835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143164972515558577676775223 214747458773337866515162835)
    ·
      refine ⟨322121188160006799772744253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214747458773337866515162835 322121188160006799772744253)
      ·
        refine ⟨120795445560002549914779095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 322121188160006799772744253 120795445560002549914779095)
        ·
          refine ⟨181193168340003824872168643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120795445560002549914779095 181193168340003824872168643)
          ·
            refine ⟨271789752510005737308252965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181193168340003824872168643 271789752510005737308252965)
            ·
              refine ⟨50960578595626075745297431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 271789752510005737308252965 50960578595626075745297431)
              ·
                refine ⟨76440867893439113617946147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50960578595626075745297431 76440867893439113617946147)
                ·
                  refine ⟨114661301840158670426919221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76440867893439113617946147 114661301840158670426919221)
                  ·
                    refine ⟨10749497047514875352523677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 114661301840158670426919221 10749497047514875352523677)
                    ·
                      refine ⟨4031061392818078257196379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10749497047514875352523677 4031061392818078257196379)
                      ·
                        rfl

theorem cell23_7850464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 1, 1, 5, 3].length) (baseStart_7850464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7850464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7850464 prefixEnd_7850464 := by exact prefixLift 7850464
  have htrace : WordTrace (prefixWord ++ tailWord_7850464) baseStart_7850464 baseEnd_7850464 := by
    simpa [prefixWord, tailWord_7850464, baseEnd_7850464] using wordTrace_append hprefix tailTrace_7850464
  have hstable : (prefixWord ++ tailWord_7850464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7850464).length < 2 ^ (prefixWord ++ tailWord_7850464).sum := by decide
  have hdescent : baseEnd_7850464 < baseStart_7850464 := by decide
  rcases family_descends (prefixWord ++ tailWord_7850464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7850504 : List Nat := [2, 1, 3, 2, 1, 1, 1, 2, 3, 3, 4]
def baseStart_7850504 : Nat := 118140960795 + 7850504 * 2 ^ 59
def prefixEnd_7850504 : Nat := 4983230072969 + 3 ^ 40 * 7850504 * 2
def baseEnd_7850504 : Nat := 4031081932044258100696195

theorem tailTrace_7850504 : CollatzResearch.WordTrace tailWord_7850504 prefixEnd_7850504 4031081932044258100696195 := by
  unfold tailWord_7850504
  simp only [CollatzResearch.WordTrace]
  refine ⟨143165701975486121092503283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190887602633981494790004377 143165701975486121092503283)
  ·
    refine ⟨214748552963229181638754925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143165701975486121092503283 214748552963229181638754925)
    ·
      refine ⟨80530707361210943114533097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214748552963229181638754925 80530707361210943114533097)
      ·
        refine ⟨60398030520908207335899823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80530707361210943114533097 60398030520908207335899823)
        ·
          refine ⟨90597045781362311003849735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60398030520908207335899823 90597045781362311003849735)
          ·
            refine ⟨135895568672043466505774603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90597045781362311003849735 135895568672043466505774603)
            ·
              refine ⟨203843353008065199758661905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135895568672043466505774603 203843353008065199758661905)
              ·
                refine ⟨152882514756048899818996429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 203843353008065199758661905 152882514756048899818996429)
                ·
                  refine ⟨57330943033518337432123661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 152882514756048899818996429 57330943033518337432123661)
                  ·
                    refine ⟨21499103637569376537046373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57330943033518337432123661 21499103637569376537046373)
                    ·
                      refine ⟨4031081932044258100696195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21499103637569376537046373 4031081932044258100696195)
                      ·
                        rfl

theorem cell23_7850504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 2, 3, 3, 4].length) (baseStart_7850504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7850504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7850504 prefixEnd_7850504 := by exact prefixLift 7850504
  have htrace : WordTrace (prefixWord ++ tailWord_7850504) baseStart_7850504 baseEnd_7850504 := by
    simpa [prefixWord, tailWord_7850504, baseEnd_7850504] using wordTrace_append hprefix tailTrace_7850504
  have hstable : (prefixWord ++ tailWord_7850504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7850504).length < 2 ^ (prefixWord ++ tailWord_7850504).sum := by decide
  have hdescent : baseEnd_7850504 < baseStart_7850504 := by decide
  rcases family_descends (prefixWord ++ tailWord_7850504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7850521 : List Nat := [1, 2, 1, 2, 1, 1, 2, 5, 2, 4, 2]
def baseStart_7850521 : Nat := 118140960795 + 7850521 * 2 ^ 59
def prefixEnd_7850521 : Nat := 4983230072969 + 3 ^ 40 * 7850521 * 2
def baseEnd_7850521 : Nat := 4031090661215384534183617

theorem tailTrace_7850521 : CollatzResearch.WordTrace tailWord_7850521 prefixEnd_7850521 4031090661215384534183617 := by
  unfold tailWord_7850521
  simp only [CollatzResearch.WordTrace]
  refine ⟨286332023991910654088375417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190888015994607102725583611 286332023991910654088375417)
  ·
    refine ⟨214749017993932990566281563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286332023991910654088375417 214749017993932990566281563)
    ·
      refine ⟨322123526990899485849422345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214749017993932990566281563 322123526990899485849422345)
      ·
        refine ⟨241592645243174614387066759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 322123526990899485849422345 241592645243174614387066759)
        ·
          refine ⟨362388967864761921580600139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241592645243174614387066759 362388967864761921580600139)
          ·
            refine ⟨543583451797142882370900209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 362388967864761921580600139 543583451797142882370900209)
            ·
              refine ⟨407687588847857161778175157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 543583451797142882370900209 407687588847857161778175157)
              ·
                refine ⟨38220711454486608916703921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 407687588847857161778175157 38220711454486608916703921)
                ·
                  refine ⟨28665533590864956687527941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38220711454486608916703921 28665533590864956687527941)
                  ·
                    refine ⟨5374787548287179378911489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28665533590864956687527941 5374787548287179378911489)
                    ·
                      refine ⟨4031090661215384534183617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5374787548287179378911489 4031090661215384534183617)
                      ·
                        rfl

theorem cell23_7850521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 5, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 5, 2, 4, 2].length) (baseStart_7850521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7850521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7850521 prefixEnd_7850521 := by exact prefixLift 7850521
  have htrace : WordTrace (prefixWord ++ tailWord_7850521) baseStart_7850521 baseEnd_7850521 := by
    simpa [prefixWord, tailWord_7850521, baseEnd_7850521] using wordTrace_append hprefix tailTrace_7850521
  have hstable : (prefixWord ++ tailWord_7850521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7850521).length < 2 ^ (prefixWord ++ tailWord_7850521).sum := by decide
  have hdescent : baseEnd_7850521 < baseStart_7850521 := by decide
  rcases family_descends (prefixWord ++ tailWord_7850521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7850531 : List Nat := [1, 1, 1, 4, 4, 1, 1, 1, 5, 4]
def baseStart_7850531 : Nat := 118140960795 + 7850531 * 2 ^ 59
def prefixEnd_7850531 : Nat := 4983230072969 + 3 ^ 40 * 7850531 * 2
def baseEnd_7850531 : Nat := 1343698598673976498352857

theorem tailTrace_7850531 : CollatzResearch.WordTrace tailWord_7850531 prefixEnd_7850531 1343698598673976498352857 := by
  unfold tailWord_7850531
  simp only [CollatzResearch.WordTrace]
  refine ⟨286332388721874425796239447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190888259147916283864159631 286332388721874425796239447)
  ·
    refine ⟨429498583082811638694359171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286332388721874425796239447 429498583082811638694359171)
    ·
      refine ⟨644247874624217458041538757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 429498583082811638694359171 644247874624217458041538757)
      ·
        refine ⟨120796476492040773382788517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 644247874624217458041538757 120796476492040773382788517)
        ·
          refine ⟨22649339342257645009272847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 120796476492040773382788517 22649339342257645009272847)
          ·
            refine ⟨33974009013386467513909271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22649339342257645009272847 33974009013386467513909271)
            ·
              refine ⟨50961013520079701270863907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33974009013386467513909271 50961013520079701270863907)
              ·
                refine ⟨76441520280119551906295861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50961013520079701270863907 76441520280119551906295861)
                ·
                  refine ⟨7166392526261207991215237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 76441520280119551906295861 7166392526261207991215237)
                  ·
                    refine ⟨1343698598673976498352857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7166392526261207991215237 1343698598673976498352857)
                    ·
                      rfl

theorem cell23_7850531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 1, 5, 4].length) (baseStart_7850531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7850531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7850531 prefixEnd_7850531 := by exact prefixLift 7850531
  have htrace : WordTrace (prefixWord ++ tailWord_7850531) baseStart_7850531 baseEnd_7850531 := by
    simpa [prefixWord, tailWord_7850531, baseEnd_7850531] using wordTrace_append hprefix tailTrace_7850531
  have hstable : (prefixWord ++ tailWord_7850531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7850531).length < 2 ^ (prefixWord ++ tailWord_7850531).sum := by decide
  have hdescent : baseEnd_7850531 < baseStart_7850531 := by decide
  rcases family_descends (prefixWord ++ tailWord_7850531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7850538 : List Nat := [3, 1, 4, 1, 1, 2, 3, 1, 2, 1, 4]
def baseStart_7850538 : Nat := 118140960795 + 7850538 * 2 ^ 59
def prefixEnd_7850538 : Nat := 4983230072969 + 3 ^ 40 * 7850538 * 2
def baseEnd_7850538 : Nat := 4031099390386510967671039

theorem tailTrace_7850538 : CollatzResearch.WordTrace tailWord_7850538 prefixEnd_7850538 4031099390386510967671039 := by
  unfold tailWord_7850538
  simp only [CollatzResearch.WordTrace]
  refine ⟨71583161008212266497936067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190888429355232710661162845 71583161008212266497936067)
  ·
    refine ⟨107374741512318399746904101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71583161008212266497936067 107374741512318399746904101)
    ·
      refine ⟨20132764033559699952544519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107374741512318399746904101 20132764033559699952544519)
      ·
        refine ⟨30199146050339549928816779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20132764033559699952544519 30199146050339549928816779)
        ·
          refine ⟨45298719075509324893225169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30199146050339549928816779 45298719075509324893225169)
          ·
            refine ⟨33974039306631993669918877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45298719075509324893225169 33974039306631993669918877)
            ·
              refine ⟨12740264739986997626219579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33974039306631993669918877 12740264739986997626219579)
              ·
                refine ⟨19110397109980496439329369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12740264739986997626219579 19110397109980496439329369)
                ·
                  refine ⟨14332797832485372329497027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19110397109980496439329369 14332797832485372329497027)
                  ·
                    refine ⟨21499196748728058494245541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14332797832485372329497027 21499196748728058494245541)
                    ·
                      refine ⟨4031099390386510967671039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21499196748728058494245541 4031099390386510967671039)
                      ·
                        rfl

theorem cell23_7850538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 3, 1, 2, 1, 4].length) (baseStart_7850538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7850538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7850538 prefixEnd_7850538 := by exact prefixLift 7850538
  have htrace : WordTrace (prefixWord ++ tailWord_7850538) baseStart_7850538 baseEnd_7850538 := by
    simpa [prefixWord, tailWord_7850538, baseEnd_7850538] using wordTrace_append hprefix tailTrace_7850538
  have hstable : (prefixWord ++ tailWord_7850538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7850538).length < 2 ^ (prefixWord ++ tailWord_7850538).sum := by decide
  have hdescent : baseEnd_7850538 < baseStart_7850538 := by decide
  rcases family_descends (prefixWord ++ tailWord_7850538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7850561 : List Nat := [1, 2, 5, 1, 1, 3, 1, 1, 8]
def baseStart_7850561 : Nat := 118140960795 + 7850561 * 2 ^ 59
def prefixEnd_7850561 : Nat := 4983230072969 + 3 ^ 40 * 7850561 * 2
def baseEnd_7850561 : Nat := 447901244493507153075937

theorem tailTrace_7850561 : CollatzResearch.WordTrace tailWord_7850561 prefixEnd_7850561 447901244493507153075937 := by
  unfold tailWord_7850561
  simp only [CollatzResearch.WordTrace]
  refine ⟨286333482911765740919831537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190888988607843827279887691 286333482911765740919831537)
  ·
    refine ⟨214750112183824305689873653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286333482911765740919831537 214750112183824305689873653)
    ·
      refine ⟨20132823017233528658425655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 214750112183824305689873653 20132823017233528658425655)
      ·
        refine ⟨30199234525850292987638483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20132823017233528658425655 30199234525850292987638483)
        ·
          refine ⟨45298851788775439481457725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30199234525850292987638483 45298851788775439481457725)
          ·
            refine ⟨16987069420790789805546647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45298851788775439481457725 16987069420790789805546647)
            ·
              refine ⟨25480604131186184708319971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16987069420790789805546647 25480604131186184708319971)
              ·
                refine ⟨38220906196779277062479957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25480604131186184708319971 38220906196779277062479957)
                ·
                  refine ⟨447901244493507153075937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38220906196779277062479957 447901244493507153075937)
                  ·
                    rfl

theorem cell23_7850561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 1, 8].length) (baseStart_7850561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7850561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7850561 prefixEnd_7850561 := by exact prefixLift 7850561
  have htrace : WordTrace (prefixWord ++ tailWord_7850561) baseStart_7850561 baseEnd_7850561 := by
    simpa [prefixWord, tailWord_7850561, baseEnd_7850561] using wordTrace_append hprefix tailTrace_7850561
  have hstable : (prefixWord ++ tailWord_7850561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7850561).length < 2 ^ (prefixWord ++ tailWord_7850561).sum := by decide
  have hdescent : baseEnd_7850561 < baseStart_7850561 := by decide
  rcases family_descends (prefixWord ++ tailWord_7850561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7850578 : List Nat := [3, 2, 2, 1, 2, 1, 5, 1, 6]
def baseStart_7850578 : Nat := 118140960795 + 7850578 * 2 ^ 59
def prefixEnd_7850578 : Nat := 4983230072969 + 3 ^ 40 * 7850578 * 2
def baseEnd_7850578 : Nat := 447902214401410090130095

theorem tailTrace_7850578 : CollatzResearch.WordTrace tailWord_7850578 prefixEnd_7850578 447902214401410090130095 := by
  unfold tailWord_7850578
  simp only [CollatzResearch.WordTrace]
  refine ⟨71583525738176038205800097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190889401968469435215466925 71583525738176038205800097)
  ·
    refine ⟨53687644303632028654350073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71583525738176038205800097 53687644303632028654350073)
    ·
      refine ⟨40265733227724021490762555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53687644303632028654350073 40265733227724021490762555)
      ·
        refine ⟨60398599841586032236143833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40265733227724021490762555 60398599841586032236143833)
        ·
          refine ⟨45298949881189524177107875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60398599841586032236143833 45298949881189524177107875)
          ·
            refine ⟨67948424821784286265661813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45298949881189524177107875 67948424821784286265661813)
            ·
              refine ⟨6370164827042276837405795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67948424821784286265661813 6370164827042276837405795)
              ·
                refine ⟨9555247240563415256108693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6370164827042276837405795 9555247240563415256108693)
                ·
                  refine ⟨447902214401410090130095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9555247240563415256108693 447902214401410090130095)
                  ·
                    rfl

theorem cell23_7850578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 5, 1, 6].length) (baseStart_7850578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7850578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7850578 prefixEnd_7850578 := by exact prefixLift 7850578
  have htrace : WordTrace (prefixWord ++ tailWord_7850578) baseStart_7850578 baseEnd_7850578 := by
    simpa [prefixWord, tailWord_7850578, baseEnd_7850578] using wordTrace_append hprefix tailTrace_7850578
  have hstable : (prefixWord ++ tailWord_7850578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7850578).length < 2 ^ (prefixWord ++ tailWord_7850578).sum := by decide
  have hdescent : baseEnd_7850578 < baseStart_7850578 := by decide
  rcases family_descends (prefixWord ++ tailWord_7850578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7850584 : List Nat := [2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 7]
def baseStart_7850584 : Nat := 118140960795 + 7850584 * 2 ^ 59
def prefixEnd_7850584 : Nat := 4983230072969 + 3 ^ 40 * 7850584 * 2
def baseEnd_7850584 : Nat := 4031123010496617787695827

theorem tailTrace_7850584 : CollatzResearch.WordTrace tailWord_7850584 prefixEnd_7850584 4031123010496617787695827 := by
  unfold tailWord_7850584
  simp only [CollatzResearch.WordTrace]
  refine ⟨143167160895341207923959403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190889547860454943898612537 143167160895341207923959403)
  ·
    refine ⟨214750741343011811885939105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143167160895341207923959403 214750741343011811885939105)
    ·
      refine ⟨161063056007258858914454329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214750741343011811885939105 161063056007258858914454329)
      ·
        refine ⟨120797292005444144185840747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161063056007258858914454329 120797292005444144185840747)
        ·
          refine ⟨181195938008166216278761121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120797292005444144185840747 181195938008166216278761121)
          ·
            refine ⟨135896953506124662209070841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181195938008166216278761121 135896953506124662209070841)
            ·
              refine ⟨101922715129593496656803131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135896953506124662209070841 101922715129593496656803131)
              ·
                refine ⟨152884072694390244985204697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101922715129593496656803131 152884072694390244985204697)
                ·
                  refine ⟨114663054520792683738903523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 152884072694390244985204697 114663054520792683738903523)
                  ·
                    refine ⟨171994581781189025608355285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 114663054520792683738903523 171994581781189025608355285)
                    ·
                      refine ⟨4031123010496617787695827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 171994581781189025608355285 4031123010496617787695827)
                      ·
                        rfl

theorem cell23_7850584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 7].length) (baseStart_7850584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7850584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7850584 prefixEnd_7850584 := by exact prefixLift 7850584
  have htrace : WordTrace (prefixWord ++ tailWord_7850584) baseStart_7850584 baseEnd_7850584 := by
    simpa [prefixWord, tailWord_7850584, baseEnd_7850584] using wordTrace_append hprefix tailTrace_7850584
  have hstable : (prefixWord ++ tailWord_7850584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7850584).length < 2 ^ (prefixWord ++ tailWord_7850584).sum := by decide
  have hdescent : baseEnd_7850584 < baseStart_7850584 := by decide
  rcases family_descends (prefixWord ++ tailWord_7850584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7850631 : List Nat := [1, 1, 4, 2, 1, 2, 1, 4, 1, 1, 5]
def baseStart_7850631 : Nat := 118140960795 + 7850631 * 2 ^ 59
def prefixEnd_7850631 : Nat := 4983230072969 + 3 ^ 40 * 7850631 * 2
def baseEnd_7850631 : Nat := 4031147144087379103808111

theorem tailTrace_7850631 : CollatzResearch.WordTrace tailWord_7850631 prefixEnd_7850631 4031147144087379103808111 := by
  unfold tailWord_7850631
  simp only [CollatzResearch.WordTrace]
  refine ⟨286336036021512142874879747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190890690681008095249919831 286336036021512142874879747)
  ·
    refine ⟨429504054032268214312319621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286336036021512142874879747 429504054032268214312319621)
    ·
      refine ⟨80532010131050290183559929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 429504054032268214312319621 80532010131050290183559929)
      ·
        refine ⟨60399007598287717637669947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80532010131050290183559929 60399007598287717637669947)
        ·
          refine ⟨90598511397431576456504921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60399007598287717637669947 90598511397431576456504921)
          ·
            refine ⟨67948883548073682342378691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90598511397431576456504921 67948883548073682342378691)
            ·
              refine ⟨101923325322110523513568037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67948883548073682342378691 101923325322110523513568037)
              ·
                refine ⟨19110623497895723158794007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 101923325322110523513568037 19110623497895723158794007)
                ·
                  refine ⟨28665935246843584738191011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19110623497895723158794007 28665935246843584738191011)
                  ·
                    refine ⟨42998902870265377107286517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28665935246843584738191011 42998902870265377107286517)
                    ·
                      refine ⟨4031147144087379103808111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42998902870265377107286517 4031147144087379103808111)
                      ·
                        rfl

theorem cell23_7850631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 4, 1, 1, 5].length) (baseStart_7850631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7850631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7850631 prefixEnd_7850631 := by exact prefixLift 7850631
  have htrace : WordTrace (prefixWord ++ tailWord_7850631) baseStart_7850631 baseEnd_7850631 := by
    simpa [prefixWord, tailWord_7850631, baseEnd_7850631] using wordTrace_append hprefix tailTrace_7850631
  have hstable : (prefixWord ++ tailWord_7850631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7850631).length < 2 ^ (prefixWord ++ tailWord_7850631).sum := by decide
  have hdescent : baseEnd_7850631 < baseStart_7850631 := by decide
  rcases family_descends (prefixWord ++ tailWord_7850631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7850648 : List Nat := [2, 1, 2, 4, 1, 1, 3, 1, 3, 2, 3]
def baseStart_7850648 : Nat := 118140960795 + 7850648 * 2 ^ 59
def prefixEnd_7850648 : Nat := 4983230072969 + 3 ^ 40 * 7850648 * 2
def baseEnd_7850648 : Nat := 4031155873258505537295533

theorem tailTrace_7850648 : CollatzResearch.WordTrace tailWord_7850648 prefixEnd_7850648 4031155873258505537295533 := by
  unfold tailWord_7850648
  simp only [CollatzResearch.WordTrace]
  refine ⟨143168328031225277389124299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190891104041633703185499065 143168328031225277389124299)
  ·
    refine ⟨214752492046837916083686449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143168328031225277389124299 214752492046837916083686449)
    ·
      refine ⟨161064369035128437062764837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214752492046837916083686449 161064369035128437062764837)
      ·
        refine ⟨30199569194086581949268407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 161064369035128437062764837 30199569194086581949268407)
        ·
          refine ⟨45299353791129872923902611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30199569194086581949268407 45299353791129872923902611)
          ·
            refine ⟨67949030686694809385853917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45299353791129872923902611 67949030686694809385853917)
            ·
              refine ⟨25480886507510553519695219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67949030686694809385853917 25480886507510553519695219)
              ·
                refine ⟨38221329761265830279542829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25480886507510553519695219 38221329761265830279542829)
                ·
                  refine ⟨14332998660474686354828561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38221329761265830279542829 14332998660474686354828561)
                  ·
                    refine ⟨10749748995356014766121421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14332998660474686354828561 10749748995356014766121421)
                    ·
                      refine ⟨4031155873258505537295533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10749748995356014766121421 4031155873258505537295533)
                      ·
                        rfl

theorem cell23_7850648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 1, 3, 2, 3].length) (baseStart_7850648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7850648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7850648 prefixEnd_7850648 := by exact prefixLift 7850648
  have htrace : WordTrace (prefixWord ++ tailWord_7850648) baseStart_7850648 baseEnd_7850648 := by
    simpa [prefixWord, tailWord_7850648, baseEnd_7850648] using wordTrace_append hprefix tailTrace_7850648
  have hstable : (prefixWord ++ tailWord_7850648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7850648).length < 2 ^ (prefixWord ++ tailWord_7850648).sum := by decide
  have hdescent : baseEnd_7850648 < baseStart_7850648 := by decide
  rcases family_descends (prefixWord ++ tailWord_7850648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7850673 : List Nat := [1, 2, 2, 6, 2, 1, 2, 2, 1, 1, 3]
def baseStart_7850673 : Nat := 118140960795 + 7850673 * 2 ^ 59
def prefixEnd_7850673 : Nat := 4983230072969 + 3 ^ 40 * 7850673 * 2
def baseEnd_7850673 : Nat := 4031168710274867939482919

theorem tailTrace_7850673 : CollatzResearch.WordTrace tailWord_7850673 prefixEnd_7850673 4031168710274867939482919 := by
  unfold tailWord_7850673
  simp only [CollatzResearch.WordTrace]
  refine ⟨286337567887359984047908673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190891711924906656031939115 286337567887359984047908673)
  ·
    refine ⟨214753175915519988035931505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286337567887359984047908673 214753175915519988035931505)
    ·
      refine ⟨161064881936639991026948629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214753175915519988035931505 161064881936639991026948629)
      ·
        refine ⟨7549916340779999579388217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 161064881936639991026948629 7549916340779999579388217)
        ·
          refine ⟨5662437255584999684541163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7549916340779999579388217 5662437255584999684541163)
          ·
            refine ⟨8493655883377499526811745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5662437255584999684541163 8493655883377499526811745)
            ·
              refine ⟨6370241912533124645108809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8493655883377499526811745 6370241912533124645108809)
              ·
                refine ⟨4777681434399843483831607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6370241912533124645108809 4777681434399843483831607)
                ·
                  refine ⟨7166522151599765225747411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4777681434399843483831607 7166522151599765225747411)
                  ·
                    refine ⟨10749783227399647838621117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7166522151599765225747411 10749783227399647838621117)
                    ·
                      refine ⟨4031168710274867939482919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10749783227399647838621117 4031168710274867939482919)
                      ·
                        rfl

theorem cell23_7850673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 2, 2, 1, 1, 3].length) (baseStart_7850673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7850673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7850673 prefixEnd_7850673 := by exact prefixLift 7850673
  have htrace : WordTrace (prefixWord ++ tailWord_7850673) baseStart_7850673 baseEnd_7850673 := by
    simpa [prefixWord, tailWord_7850673, baseEnd_7850673] using wordTrace_append hprefix tailTrace_7850673
  have hstable : (prefixWord ++ tailWord_7850673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7850673).length < 2 ^ (prefixWord ++ tailWord_7850673).sum := by decide
  have hdescent : baseEnd_7850673 < baseStart_7850673 := by decide
  rcases family_descends (prefixWord ++ tailWord_7850673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7850679 : List Nat := [1, 1, 3, 1, 6, 1, 1, 4, 1, 2, 2]
def baseStart_7850679 : Nat := 118140960795 + 7850679 * 2 ^ 59
def prefixEnd_7850679 : Nat := 4983230072969 + 3 ^ 40 * 7850679 * 2
def baseEnd_7850679 : Nat := 4031171791158794916007891

theorem tailTrace_7850679 : CollatzResearch.WordTrace tailWord_7850679 prefixEnd_7850679 4031171791158794916007891 := by
  unfold tailWord_7850679
  simp only [CollatzResearch.WordTrace]
  refine ⟨286337786725338247072627091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190891857816892164715084727 286337786725338247072627091)
  ·
    refine ⟨429506680088007370608940637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286337786725338247072627091 429506680088007370608940637)
    ·
      refine ⟨161065005033002763978352739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 429506680088007370608940637 161065005033002763978352739)
      ·
        refine ⟨241597507549504145967529109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161065005033002763978352739 241597507549504145967529109)
        ·
          refine ⟨11324883166383006842227927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 241597507549504145967529109 11324883166383006842227927)
          ·
            refine ⟨16987324749574510263341891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11324883166383006842227927 16987324749574510263341891)
            ·
              refine ⟨25480987124361765395012837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16987324749574510263341891 25480987124361765395012837)
              ·
                refine ⟨4777685085817831011564907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25480987124361765395012837 4777685085817831011564907)
                ·
                  refine ⟨7166527628726746517347361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4777685085817831011564907 7166527628726746517347361)
                  ·
                    refine ⟨5374895721545059888010521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7166527628726746517347361 5374895721545059888010521)
                    ·
                      refine ⟨4031171791158794916007891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5374895721545059888010521 4031171791158794916007891)
                      ·
                        rfl

theorem cell23_7850679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 4, 1, 2, 2].length) (baseStart_7850679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7850679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7850679 prefixEnd_7850679 := by exact prefixLift 7850679
  have htrace : WordTrace (prefixWord ++ tailWord_7850679) baseStart_7850679 baseEnd_7850679 := by
    simpa [prefixWord, tailWord_7850679, baseEnd_7850679] using wordTrace_append hprefix tailTrace_7850679
  have hstable : (prefixWord ++ tailWord_7850679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7850679).length < 2 ^ (prefixWord ++ tailWord_7850679).sum := by decide
  have hdescent : baseEnd_7850679 < baseStart_7850679 := by decide
  rcases family_descends (prefixWord ++ tailWord_7850679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7850705 : List Nat := [1, 2, 2, 1, 2, 3, 2, 4, 1, 3, 2]
def baseStart_7850705 : Nat := 118140960795 + 7850705 * 2 ^ 59
def prefixEnd_7850705 : Nat := 4983230072969 + 3 ^ 40 * 7850705 * 2
def baseEnd_7850705 : Nat := 4031185141655811814282771

theorem tailTrace_7850705 : CollatzResearch.WordTrace tailWord_7850705 prefixEnd_7850705 4031185141655811814282771 := by
  unfold tailWord_7850705
  simp only [CollatzResearch.WordTrace]
  refine ⟨286338735023244053513073569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190892490015496035675382379 286338735023244053513073569)
  ·
    refine ⟨214754051267433040134805177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286338735023244053513073569 214754051267433040134805177)
    ·
      refine ⟨161065538450574780101103883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214754051267433040134805177 161065538450574780101103883)
      ·
        refine ⟨241598307675862170151655825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161065538450574780101103883 241598307675862170151655825)
        ·
          refine ⟨181198730756896627613741869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 241598307675862170151655825 181198730756896627613741869)
          ·
            refine ⟨67949524033836235355153201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 181198730756896627613741869 67949524033836235355153201)
            ·
              refine ⟨50962143025377176516364901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67949524033836235355153201 50962143025377176516364901)
              ·
                refine ⟨9555401817258220596818419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50962143025377176516364901 9555401817258220596818419)
                ·
                  refine ⟨14333102725887330895227629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9555401817258220596818419 14333102725887330895227629)
                  ·
                    refine ⟨5374913522207749085710361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14333102725887330895227629 5374913522207749085710361)
                    ·
                      refine ⟨4031185141655811814282771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5374913522207749085710361 4031185141655811814282771)
                      ·
                        rfl

theorem cell23_7850705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 4, 1, 3, 2].length) (baseStart_7850705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7850705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7850705 prefixEnd_7850705 := by exact prefixLift 7850705
  have htrace : WordTrace (prefixWord ++ tailWord_7850705) baseStart_7850705 baseEnd_7850705 := by
    simpa [prefixWord, tailWord_7850705, baseEnd_7850705] using wordTrace_append hprefix tailTrace_7850705
  have hstable : (prefixWord ++ tailWord_7850705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7850705).length < 2 ^ (prefixWord ++ tailWord_7850705).sum := by decide
  have hdescent : baseEnd_7850705 < baseStart_7850705 := by decide
  rcases family_descends (prefixWord ++ tailWord_7850705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7850748 : List Nat := [2, 2, 2, 1, 3, 2, 2, 1, 2, 2, 4]
def baseStart_7850748 : Nat := 118140960795 + 7850748 * 2 ^ 59
def prefixEnd_7850748 : Nat := 4983230072969 + 3 ^ 40 * 7850748 * 2
def baseEnd_7850748 : Nat := 4031207221323955146045073

theorem tailTrace_7850748 : CollatzResearch.WordTrace tailWord_7850748 prefixEnd_7850748 4031207221323955146045073 := by
  unfold tailWord_7850748
  simp only [CollatzResearch.WordTrace]
  refine ⟨143170151681044135928444449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190893535574725514571259265 143170151681044135928444449)
  ·
    refine ⟨107377613760783101946333337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143170151681044135928444449 107377613760783101946333337)
    ·
      refine ⟨80533210320587326459750003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107377613760783101946333337 80533210320587326459750003)
      ·
        refine ⟨120799815480880989689625005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80533210320587326459750003 120799815480880989689625005)
        ·
          refine ⟨45299930805330371133609377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120799815480880989689625005 45299930805330371133609377)
          ·
            refine ⟨33974948103997778350207033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45299930805330371133609377 33974948103997778350207033)
            ·
              refine ⟨25481211077998333762655275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33974948103997778350207033 25481211077998333762655275)
              ·
                refine ⟨38221816616997500643982913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25481211077998333762655275 38221816616997500643982913)
                ·
                  refine ⟨28666362462748125482987185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38221816616997500643982913 28666362462748125482987185)
                  ·
                    refine ⟨21499771847061094112240389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28666362462748125482987185 21499771847061094112240389)
                    ·
                      refine ⟨4031207221323955146045073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21499771847061094112240389 4031207221323955146045073)
                      ·
                        rfl

theorem cell23_7850748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 1, 2, 2, 4].length) (baseStart_7850748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7850748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7850748 prefixEnd_7850748 := by exact prefixLift 7850748
  have htrace : WordTrace (prefixWord ++ tailWord_7850748) baseStart_7850748 baseEnd_7850748 := by
    simpa [prefixWord, tailWord_7850748, baseEnd_7850748] using wordTrace_append hprefix tailTrace_7850748
  have hstable : (prefixWord ++ tailWord_7850748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7850748).length < 2 ^ (prefixWord ++ tailWord_7850748).sum := by decide
  have hdescent : baseEnd_7850748 < baseStart_7850748 := by decide
  rcases family_descends (prefixWord ++ tailWord_7850748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7850771 : List Nat := [1, 1, 1, 2, 1, 3, 3, 3, 1, 7]
def baseStart_7850771 : Nat := 118140960795 + 7850771 * 2 ^ 59
def prefixEnd_7850771 : Nat := 4983230072969 + 3 ^ 40 * 7850771 * 2
def baseEnd_7850771 : Nat := 1343739677126336185352489

theorem tailTrace_7850771 : CollatzResearch.WordTrace tailWord_7850771 prefixEnd_7850771 1343739677126336185352489 := by
  unfold tailWord_7850771
  simp only [CollatzResearch.WordTrace]
  refine ⟨286341142241004946784976167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190894094827336631189984111 286341142241004946784976167)
  ·
    refine ⟨429511713361507420177464251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286341142241004946784976167 429511713361507420177464251)
    ·
      refine ⟨644267570042261130266196377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 429511713361507420177464251 644267570042261130266196377)
      ·
        refine ⟨483200677531695847699647283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 644267570042261130266196377 483200677531695847699647283)
        ·
          refine ⟨724801016297543771549470925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 483200677531695847699647283 724801016297543771549470925)
          ·
            refine ⟨271800381111578914331051597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 724801016297543771549470925 271800381111578914331051597)
            ·
              refine ⟨101925142916842092874144349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 271800381111578914331051597 101925142916842092874144349)
              ·
                refine ⟨38221928593815784827804131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101925142916842092874144349 38221928593815784827804131)
                ·
                  refine ⟨57332892890723677241706197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38221928593815784827804131 57332892890723677241706197)
                  ·
                    refine ⟨1343739677126336185352489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57332892890723677241706197 1343739677126336185352489)
                    ·
                      rfl

theorem cell23_7850771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 3, 1, 7].length) (baseStart_7850771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7850771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7850771 prefixEnd_7850771 := by exact prefixLift 7850771
  have htrace : WordTrace (prefixWord ++ tailWord_7850771) baseStart_7850771 baseEnd_7850771 := by
    simpa [prefixWord, tailWord_7850771, baseEnd_7850771] using wordTrace_append hprefix tailTrace_7850771
  have hstable : (prefixWord ++ tailWord_7850771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7850771).length < 2 ^ (prefixWord ++ tailWord_7850771).sum := by decide
  have hdescent : baseEnd_7850771 < baseStart_7850771 := by decide
  rcases family_descends (prefixWord ++ tailWord_7850771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7850792 : List Nat := [2, 1, 5, 1, 1, 1, 5, 2, 5]
def baseStart_7850792 : Nat := 118140960795 + 7850792 * 2 ^ 59
def prefixEnd_7850792 : Nat := 4983230072969 + 3 ^ 40 * 7850792 * 2
def baseEnd_7850792 : Nat := 447914423830305885988319

theorem tailTrace_7850792 : CollatzResearch.WordTrace tailWord_7850792 prefixEnd_7850792 447914423830305885988319 := by
  unfold tailWord_7850792
  simp only [CollatzResearch.WordTrace]
  refine ⟨143170954086964433685745315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190894605449285911580993753 143170954086964433685745315)
  ·
    refine ⟨214756431130446650528617973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143170954086964433685745315 214756431130446650528617973)
    ·
      refine ⟨20133415418479373487057935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 214756431130446650528617973 20133415418479373487057935)
      ·
        refine ⟨30200123127719060230586903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20133415418479373487057935 30200123127719060230586903)
        ·
          refine ⟨45300184691578590345880355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30200123127719060230586903 45300184691578590345880355)
          ·
            refine ⟨67950277037367885518820533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45300184691578590345880355 67950277037367885518820533)
            ·
              refine ⟨6370338472253239267389425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67950277037367885518820533 6370338472253239267389425)
              ·
                refine ⟨4777753854189929450542069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6370338472253239267389425 4777753854189929450542069)
                ·
                  refine ⟨447914423830305885988319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4777753854189929450542069 447914423830305885988319)
                  ·
                    rfl

theorem cell23_7850792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 5, 2, 5].length) (baseStart_7850792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7850792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7850792 prefixEnd_7850792 := by exact prefixLift 7850792
  have htrace : WordTrace (prefixWord ++ tailWord_7850792) baseStart_7850792 baseEnd_7850792 := by
    simpa [prefixWord, tailWord_7850792, baseEnd_7850792] using wordTrace_append hprefix tailTrace_7850792
  have hstable : (prefixWord ++ tailWord_7850792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7850792).length < 2 ^ (prefixWord ++ tailWord_7850792).sum := by decide
  have hdescent : baseEnd_7850792 < baseStart_7850792 := by decide
  rcases family_descends (prefixWord ++ tailWord_7850792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7850808 : List Nat := [2, 1, 2, 1, 3, 2, 1, 2, 4, 1, 4]
def baseStart_7850808 : Nat := 118140960795 + 7850808 * 2 ^ 59
def prefixEnd_7850808 : Nat := 4983230072969 + 3 ^ 40 * 7850808 * 2
def baseEnd_7850808 : Nat := 4031238030163224911294797

theorem tailTrace_7850808 : CollatzResearch.WordTrace tailWord_7850808 prefixEnd_7850808 4031238030163224911294797 := by
  unfold tailWord_7850808
  simp only [CollatzResearch.WordTrace]
  refine ⟨143171245870935451052036539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190894994494580601402715385 143171245870935451052036539)
  ·
    refine ⟨214756868806403176578054809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143171245870935451052036539 214756868806403176578054809)
    ·
      refine ⟨161067651604802382433541107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214756868806403176578054809 161067651604802382433541107)
      ·
        refine ⟨241601477407203573650311661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161067651604802382433541107 241601477407203573650311661)
        ·
          refine ⟨90600554027701340118866873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 241601477407203573650311661 90600554027701340118866873)
          ·
            refine ⟨67950415520776005089150155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90600554027701340118866873 67950415520776005089150155)
            ·
              refine ⟨101925623281164007633725233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67950415520776005089150155 101925623281164007633725233)
              ·
                refine ⟨76444217460873005725293925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101925623281164007633725233 76444217460873005725293925)
                ·
                  refine ⟨14333290773913688573492611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76444217460873005725293925 14333290773913688573492611)
                  ·
                    refine ⟨21499936160870532860238917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14333290773913688573492611 21499936160870532860238917)
                    ·
                      refine ⟨4031238030163224911294797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21499936160870532860238917 4031238030163224911294797)
                      ·
                        rfl

theorem cell23_7850808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 2, 4, 1, 4].length) (baseStart_7850808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7850808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7850808 prefixEnd_7850808 := by exact prefixLift 7850808
  have htrace : WordTrace (prefixWord ++ tailWord_7850808) baseStart_7850808 baseEnd_7850808 := by
    simpa [prefixWord, tailWord_7850808, baseEnd_7850808] using wordTrace_append hprefix tailTrace_7850808
  have hstable : (prefixWord ++ tailWord_7850808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7850808).length < 2 ^ (prefixWord ++ tailWord_7850808).sum := by decide
  have hdescent : baseEnd_7850808 < baseStart_7850808 := by decide
  rcases family_descends (prefixWord ++ tailWord_7850808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7850825 : List Nat := [1, 2, 1, 1, 2, 6, 2, 1, 2, 1, 4]
def baseStart_7850825 : Nat := 118140960795 + 7850825 * 2 ^ 59
def prefixEnd_7850825 : Nat := 4983230072969 + 3 ^ 40 * 7850825 * 2
def baseEnd_7850825 : Nat := 4031246759334351344782219

theorem tailTrace_7850825 : CollatzResearch.WordTrace tailWord_7850825 prefixEnd_7850825 4031246759334351344782219 := by
  unfold tailWord_7850825
  simp only [CollatzResearch.WordTrace]
  refine ⟨286343111782809314007441929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190895407855206209338294619 286343111782809314007441929)
  ·
    refine ⟨214757333837106985505581447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286343111782809314007441929 214757333837106985505581447)
    ·
      refine ⟨322136000755660478258372171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214757333837106985505581447 322136000755660478258372171)
      ·
        refine ⟨483204001133490717387558257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322136000755660478258372171 483204001133490717387558257)
        ·
          refine ⟨362403000850118038040668693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 483204001133490717387558257 362403000850118038040668693)
          ·
            refine ⟨16987640664849283033156345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 362403000850118038040668693 16987640664849283033156345)
            ·
              refine ⟨12740730498636962274867259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16987640664849283033156345 12740730498636962274867259)
              ·
                refine ⟨19111095747955443412300889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12740730498636962274867259 19111095747955443412300889)
                ·
                  refine ⟨14333321810966582559225667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19111095747955443412300889 14333321810966582559225667)
                  ·
                    refine ⟨21499982716449873838838501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14333321810966582559225667 21499982716449873838838501)
                    ·
                      refine ⟨4031246759334351344782219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21499982716449873838838501 4031246759334351344782219)
                      ·
                        rfl

theorem cell23_7850825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 2, 1, 2, 1, 4].length) (baseStart_7850825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7850825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7850825 prefixEnd_7850825 := by exact prefixLift 7850825
  have htrace : WordTrace (prefixWord ++ tailWord_7850825) baseStart_7850825 baseEnd_7850825 := by
    simpa [prefixWord, tailWord_7850825, baseEnd_7850825] using wordTrace_append hprefix tailTrace_7850825
  have hstable : (prefixWord ++ tailWord_7850825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7850825).length < 2 ^ (prefixWord ++ tailWord_7850825).sum := by decide
  have hdescent : baseEnd_7850825 < baseStart_7850825 := by decide
  rcases family_descends (prefixWord ++ tailWord_7850825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7850875 : List Nat := [1, 1, 1, 1, 1, 5, 3, 1, 5, 1, 3]
def baseStart_7850875 : Nat := 118140960795 + 7850875 * 2 ^ 59
def prefixEnd_7850875 : Nat := 4983230072969 + 3 ^ 40 * 7850875 * 2
def baseEnd_7850875 : Nat := 4031272433367076149156989

theorem tailTrace_7850875 : CollatzResearch.WordTrace tailWord_7850875 prefixEnd_7850875 4031272433367076149156989 := by
  unfold tailWord_7850875
  simp only [CollatzResearch.WordTrace]
  refine ⟨286344935432628172546762079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190896623621752115031174719 286344935432628172546762079)
  ·
    refine ⟨429517403148942258820143119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286344935432628172546762079 429517403148942258820143119)
    ·
      refine ⟨644276104723413388230214679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 429517403148942258820143119 644276104723413388230214679)
      ·
        refine ⟨966414157085120082345322019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 644276104723413388230214679 966414157085120082345322019)
        ·
          refine ⟨1449621235627680123517983029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 966414157085120082345322019 1449621235627680123517983029)
          ·
            refine ⟨135901990840095011579810909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1449621235627680123517983029 135901990840095011579810909)
            ·
              refine ⟨50963246565035629342429091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135901990840095011579810909 50963246565035629342429091)
              ·
                refine ⟨76444869847553444013643637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50963246565035629342429091 76444869847553444013643637)
                ·
                  refine ⟨7166706548208135376279091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 76444869847553444013643637 7166706548208135376279091)
                  ·
                    refine ⟨10750059822312203064418637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7166706548208135376279091 10750059822312203064418637)
                    ·
                      refine ⟨4031272433367076149156989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10750059822312203064418637 4031272433367076149156989)
                      ·
                        rfl

theorem cell23_7850875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 1, 5, 1, 3].length) (baseStart_7850875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7850875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7850875 prefixEnd_7850875 := by exact prefixLift 7850875
  have htrace : WordTrace (prefixWord ++ tailWord_7850875) baseStart_7850875 baseEnd_7850875 := by
    simpa [prefixWord, tailWord_7850875, baseEnd_7850875] using wordTrace_append hprefix tailTrace_7850875
  have hstable : (prefixWord ++ tailWord_7850875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7850875).length < 2 ^ (prefixWord ++ tailWord_7850875).sum := by decide
  have hdescent : baseEnd_7850875 < baseStart_7850875 := by decide
  rcases family_descends (prefixWord ++ tailWord_7850875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7850909 : List Nat := [1, 4, 2, 1, 2, 1, 1, 6, 1, 1, 3]
def baseStart_7850909 : Nat := 118140960795 + 7850909 * 2 ^ 59
def prefixEnd_7850909 : Nat := 4983230072969 + 3 ^ 40 * 7850909 * 2
def baseEnd_7850909 : Nat := 4031289891709329016131833

theorem tailTrace_7850909 : CollatzResearch.WordTrace tailWord_7850909 prefixEnd_7850909 4031289891709329016131833 := by
  unfold tailWord_7850909
  simp only [CollatzResearch.WordTrace]
  refine ⟨286346175514504996353499781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190897450343003330902333187 286346175514504996353499781)
  ·
    refine ⟨53689907908969686816281209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 286346175514504996353499781 53689907908969686816281209)
    ·
      refine ⟨40267430931727265112210907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53689907908969686816281209 40267430931727265112210907)
      ·
        refine ⟨60401146397590897668316361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40267430931727265112210907 60401146397590897668316361)
        ·
          refine ⟨45300859798193173251237271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60401146397590897668316361 45300859798193173251237271)
          ·
            refine ⟨67951289697289759876855907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45300859798193173251237271 67951289697289759876855907)
            ·
              refine ⟨101926934545934639815283861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67951289697289759876855907 101926934545934639815283861)
              ·
                refine ⟨4777825056840686241341431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 101926934545934639815283861 4777825056840686241341431)
                ·
                  refine ⟨7166737585261029362012147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4777825056840686241341431 7166737585261029362012147)
                  ·
                    refine ⟨10750106377891544043018221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7166737585261029362012147 10750106377891544043018221)
                    ·
                      refine ⟨4031289891709329016131833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10750106377891544043018221 4031289891709329016131833)
                      ·
                        rfl

theorem cell23_7850909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 6, 1, 1, 3].length) (baseStart_7850909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7850909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7850909 prefixEnd_7850909 := by exact prefixLift 7850909
  have htrace : WordTrace (prefixWord ++ tailWord_7850909) baseStart_7850909 baseEnd_7850909 := by
    simpa [prefixWord, tailWord_7850909, baseEnd_7850909] using wordTrace_append hprefix tailTrace_7850909
  have hstable : (prefixWord ++ tailWord_7850909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7850909).length < 2 ^ (prefixWord ++ tailWord_7850909).sum := by decide
  have hdescent : baseEnd_7850909 < baseStart_7850909 := by decide
  rcases family_descends (prefixWord ++ tailWord_7850909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7850935 : List Nat := [1, 1, 3, 1, 3, 1, 2, 3, 3, 2, 3]
def baseStart_7850935 : Nat := 118140960795 + 7850935 * 2 ^ 59
def prefixEnd_7850935 : Nat := 4983230072969 + 3 ^ 40 * 7850935 * 2
def baseEnd_7850935 : Nat := 4031303242206345914406713

theorem tailTrace_7850935 : CollatzResearch.WordTrace tailWord_7850935 prefixEnd_7850935 4031303242206345914406713 := by
  unfold tailWord_7850935
  simp only [CollatzResearch.WordTrace]
  refine ⟨286347123812410802793946259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190898082541607201862630839 286347123812410802793946259)
  ·
    refine ⟨429520685718616204190919389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286347123812410802793946259 429520685718616204190919389)
    ·
      refine ⟨161070257144481076571594771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 429520685718616204190919389 161070257144481076571594771)
      ·
        refine ⟨241605385716721614857392157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161070257144481076571594771 241605385716721614857392157)
        ·
          refine ⟨90602019643770605571522059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 241605385716721614857392157 90602019643770605571522059)
          ·
            refine ⟨135903029465655908357283089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90602019643770605571522059 135903029465655908357283089)
            ·
              refine ⟨101927272099241931267962317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135903029465655908357283089 101927272099241931267962317)
              ·
                refine ⟨38222727037215724225485869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101927272099241931267962317 38222727037215724225485869)
                ·
                  refine ⟨14333522638955896584557201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38222727037215724225485869 14333522638955896584557201)
                  ·
                    refine ⟨10750141979216922438417901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14333522638955896584557201 10750141979216922438417901)
                    ·
                      refine ⟨4031303242206345914406713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10750141979216922438417901 4031303242206345914406713)
                      ·
                        rfl

theorem cell23_7850935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 3, 3, 2, 3].length) (baseStart_7850935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7850935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7850935 prefixEnd_7850935 := by exact prefixLift 7850935
  have htrace : WordTrace (prefixWord ++ tailWord_7850935) baseStart_7850935 baseEnd_7850935 := by
    simpa [prefixWord, tailWord_7850935, baseEnd_7850935] using wordTrace_append hprefix tailTrace_7850935
  have hstable : (prefixWord ++ tailWord_7850935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7850935).length < 2 ^ (prefixWord ++ tailWord_7850935).sum := by decide
  have hdescent : baseEnd_7850935 < baseStart_7850935 := by decide
  rcases family_descends (prefixWord ++ tailWord_7850935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7850938 : List Nat := [3, 1, 1, 1, 2, 1, 5, 9]
def baseStart_7850938 : Nat := 118140960795 + 7850938 * 2 ^ 59
def prefixEnd_7850938 : Nat := 4983230072969 + 3 ^ 40 * 7850938 * 2
def baseEnd_7850938 : Nat := 149307584542529977876637

theorem tailTrace_7850938 : CollatzResearch.WordTrace tailWord_7850938 prefixEnd_7850938 149307584542529977876637 := by
  unfold tailWord_7850938
  simp only [CollatzResearch.WordTrace]
  refine ⟨71586808307849983576576367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190898155487599956204203645 71586808307849983576576367)
  ·
    refine ⟨107380212461774975364864551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71586808307849983576576367 107380212461774975364864551)
    ·
      refine ⟨161070318692662463047296827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107380212461774975364864551 161070318692662463047296827)
      ·
        refine ⟨241605478038993694570945241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161070318692662463047296827 241605478038993694570945241)
        ·
          refine ⟨181204108529245270928208931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 241605478038993694570945241 181204108529245270928208931)
          ·
            refine ⟨271806162793867906392313397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181204108529245270928208931 271806162793867906392313397)
            ·
              refine ⟨25481827761925116224279381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 271806162793867906392313397 25481827761925116224279381)
              ·
                refine ⟨149307584542529977876637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25481827761925116224279381 149307584542529977876637)
                ·
                  rfl

theorem cell23_7850938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 9].length) (baseStart_7850938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7850938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7850938 prefixEnd_7850938 := by exact prefixLift 7850938
  have htrace : WordTrace (prefixWord ++ tailWord_7850938) baseStart_7850938 baseEnd_7850938 := by
    simpa [prefixWord, tailWord_7850938, baseEnd_7850938] using wordTrace_append hprefix tailTrace_7850938
  have hstable : (prefixWord ++ tailWord_7850938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7850938).length < 2 ^ (prefixWord ++ tailWord_7850938).sum := by decide
  have hdescent : baseEnd_7850938 < baseStart_7850938 := by decide
  rcases family_descends (prefixWord ++ tailWord_7850938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7850952 : List Nat := [2, 1, 3, 1, 5, 1, 2, 1, 1, 1, 5]
def baseStart_7850952 : Nat := 118140960795 + 7850952 * 2 ^ 59
def prefixEnd_7850952 : Nat := 4983230072969 + 3 ^ 40 * 7850952 * 2
def baseEnd_7850952 : Nat := 4031311971377472347894135

theorem tailTrace_7850952 : CollatzResearch.WordTrace tailWord_7850952 prefixEnd_7850952 4031311971377472347894135 := by
  unfold tailWord_7850952
  simp only [CollatzResearch.WordTrace]
  refine ⟨143173871926674607348657555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190898495902232809798210073 143173871926674607348657555)
  ·
    refine ⟨214760807890011911022986333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143173871926674607348657555 214760807890011911022986333)
    ·
      refine ⟨80535302958754466633619875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214760807890011911022986333 80535302958754466633619875)
      ·
        refine ⟨120802954438131699950429813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80535302958754466633619875 120802954438131699950429813)
        ·
          refine ⟨11325276978574846870352795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 120802954438131699950429813 11325276978574846870352795)
          ·
            refine ⟨16987915467862270305529193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11325276978574846870352795 16987915467862270305529193)
            ·
              refine ⟨12740936600896702729146895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16987915467862270305529193 12740936600896702729146895)
              ·
                refine ⟨19111404901345054093720343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12740936600896702729146895 19111404901345054093720343)
                ·
                  refine ⟨28667107352017581140580515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19111404901345054093720343 28667107352017581140580515)
                  ·
                    refine ⟨43000661028026371710870773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28667107352017581140580515 43000661028026371710870773)
                    ·
                      refine ⟨4031311971377472347894135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43000661028026371710870773 4031311971377472347894135)
                      ·
                        rfl

theorem cell23_7850952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 2, 1, 1, 1, 5].length) (baseStart_7850952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7850952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7850952 prefixEnd_7850952 := by exact prefixLift 7850952
  have htrace : WordTrace (prefixWord ++ tailWord_7850952) baseStart_7850952 baseEnd_7850952 := by
    simpa [prefixWord, tailWord_7850952, baseEnd_7850952] using wordTrace_append hprefix tailTrace_7850952
  have hstable : (prefixWord ++ tailWord_7850952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7850952).length < 2 ^ (prefixWord ++ tailWord_7850952).sum := by decide
  have hdescent : baseEnd_7850952 < baseStart_7850952 := by decide
  rcases family_descends (prefixWord ++ tailWord_7850952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7850988 : List Nat := [2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 10]
def baseStart_7850988 : Nat := 118140960795 + 7850988 * 2 ^ 59
def prefixEnd_7850988 : Nat := 4983230072969 + 3 ^ 40 * 7850988 * 2
def baseEnd_7850988 : Nat := 4031330456681034207043969

theorem tailTrace_7850988 : CollatzResearch.WordTrace tailWord_7850988 prefixEnd_7850988 4031330456681034207043969 := by
  unfold tailWord_7850988
  simp only [CollatzResearch.WordTrace]
  refine ⟨143174528440609396422812809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190899371254145861897083745 143174528440609396422812809)
  ·
    refine ⟨107380896330457047317109607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143174528440609396422812809 107380896330457047317109607)
    ·
      refine ⟨161071344495685570975664411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107380896330457047317109607 161071344495685570975664411)
      ·
        refine ⟨241607016743528356463496617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161071344495685570975664411 241607016743528356463496617)
        ·
          refine ⟨181205262557646267347622463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 241607016743528356463496617 181205262557646267347622463)
          ·
            refine ⟨271807893836469401021433695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181205262557646267347622463 271807893836469401021433695)
            ·
              refine ⟨407711840754704101532150543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 271807893836469401021433695 407711840754704101532150543)
              ·
                refine ⟨611567761132056152298225815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 407711840754704101532150543 611567761132056152298225815)
                ·
                  refine ⟨917351641698084228447338723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 611567761132056152298225815 917351641698084228447338723)
                  ·
                    refine ⟨1376027462547126342671008085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 917351641698084228447338723 1376027462547126342671008085)
                    ·
                      refine ⟨4031330456681034207043969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 1376027462547126342671008085 4031330456681034207043969)
                      ·
                        rfl

theorem cell23_7850988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 10].length) (baseStart_7850988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7850988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7850988 prefixEnd_7850988 := by exact prefixLift 7850988
  have htrace : WordTrace (prefixWord ++ tailWord_7850988) baseStart_7850988 baseEnd_7850988 := by
    simpa [prefixWord, tailWord_7850988, baseEnd_7850988] using wordTrace_append hprefix tailTrace_7850988
  have hstable : (prefixWord ++ tailWord_7850988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7850988).length < 2 ^ (prefixWord ++ tailWord_7850988).sum := by decide
  have hdescent : baseEnd_7850988 < baseStart_7850988 := by decide
  rcases family_descends (prefixWord ++ tailWord_7850988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7851015 : List Nat := [1, 1, 4, 3, 1, 1, 2, 2, 2, 6]
def baseStart_7851015 : Nat := 118140960795 + 7851015 * 2 ^ 59
def prefixEnd_7851015 : Nat := 4983230072969 + 3 ^ 40 * 7851015 * 2
def baseEnd_7851015 : Nat := 1343781440219568533802115

theorem tailTrace_7851015 : CollatzResearch.WordTrace tailWord_7851015 prefixEnd_7851015 1343781440219568533802115 := by
  unfold tailWord_7851015
  simp only [CollatzResearch.WordTrace]
  refine ⟨286350041652120976456858499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190900027768080650971238999 286350041652120976456858499)
  ·
    refine ⟨429525062478181464685287749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286350041652120976456858499 429525062478181464685287749)
    ·
      refine ⟨80535949214659024628491453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 429525062478181464685287749 80535949214659024628491453)
      ·
        refine ⟨30200980955497134235684295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80535949214659024628491453 30200980955497134235684295)
        ·
          refine ⟨45301471433245701353526443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30200980955497134235684295 45301471433245701353526443)
          ·
            refine ⟨67952207149868552030289665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45301471433245701353526443 67952207149868552030289665)
            ·
              refine ⟨50964155362401414022717249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67952207149868552030289665 50964155362401414022717249)
              ·
                refine ⟨38223116521801060517037937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50964155362401414022717249 38223116521801060517037937)
                ·
                  refine ⟨28667337391350795387778453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38223116521801060517037937 28667337391350795387778453)
                  ·
                    refine ⟨1343781440219568533802115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28667337391350795387778453 1343781440219568533802115)
                    ·
                      rfl

theorem cell23_7851015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 2, 2, 6].length) (baseStart_7851015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7851015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7851015 prefixEnd_7851015 := by exact prefixLift 7851015
  have htrace : WordTrace (prefixWord ++ tailWord_7851015) baseStart_7851015 baseEnd_7851015 := by
    simpa [prefixWord, tailWord_7851015, baseEnd_7851015] using wordTrace_append hprefix tailTrace_7851015
  have hstable : (prefixWord ++ tailWord_7851015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7851015).length < 2 ^ (prefixWord ++ tailWord_7851015).sum := by decide
  have hdescent : baseEnd_7851015 < baseStart_7851015 := by decide
  rcases family_descends (prefixWord ++ tailWord_7851015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7851039 : List Nat := [1, 1, 2, 4, 1, 4, 2, 1, 1, 4, 2]
def baseStart_7851039 : Nat := 118140960795 + 7851039 * 2 ^ 59
def prefixEnd_7851039 : Nat := 4983230072969 + 3 ^ 40 * 7851039 * 2
def baseEnd_7851039 : Nat := 4031356644194413507506235

theorem tailTrace_7851039 : CollatzResearch.WordTrace tailWord_7851039 prefixEnd_7851039 4031356644194413507506235 := by
  unfold tailWord_7851039
  simp only [CollatzResearch.WordTrace]
  refine ⟨286350917004034028555732171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190900611336022685703821447 286350917004034028555732171)
  ·
    refine ⟨429526375506051042833598257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286350917004034028555732171 429526375506051042833598257)
    ·
      refine ⟨322144781629538282125198693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 429526375506051042833598257 322144781629538282125198693)
      ·
        refine ⟨60402146555538427898474755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 322144781629538282125198693 60402146555538427898474755)
        ·
          refine ⟨90603219833307641847712133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60402146555538427898474755 90603219833307641847712133)
          ·
            refine ⟨16988103718745182846446025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90603219833307641847712133 16988103718745182846446025)
            ·
              refine ⟨12741077789058887134834519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16988103718745182846446025 12741077789058887134834519)
              ·
                refine ⟨19111616683588330702251779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12741077789058887134834519 19111616683588330702251779)
                ·
                  refine ⟨28667425025382496053377669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19111616683588330702251779 28667425025382496053377669)
                  ·
                    refine ⟨5375142192259218010008313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28667425025382496053377669 5375142192259218010008313)
                    ·
                      refine ⟨4031356644194413507506235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5375142192259218010008313 4031356644194413507506235)
                      ·
                        rfl

theorem cell23_7851039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 2, 1, 1, 4, 2].length) (baseStart_7851039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7851039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7851039 prefixEnd_7851039 := by exact prefixLift 7851039
  have htrace : WordTrace (prefixWord ++ tailWord_7851039) baseStart_7851039 baseEnd_7851039 := by
    simpa [prefixWord, tailWord_7851039, baseEnd_7851039] using wordTrace_append hprefix tailTrace_7851039
  have hstable : (prefixWord ++ tailWord_7851039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7851039).length < 2 ^ (prefixWord ++ tailWord_7851039).sum := by decide
  have hdescent : baseEnd_7851039 < baseStart_7851039 := by decide
  rcases family_descends (prefixWord ++ tailWord_7851039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7851045 : List Nat := [1, 3, 1, 2, 2, 2, 3, 2, 7]
def baseStart_7851045 : Nat := 118140960795 + 7851045 * 2 ^ 59
def prefixEnd_7851045 : Nat := 4983230072969 + 3 ^ 40 * 7851045 * 2
def baseEnd_7851045 : Nat := 447928858342037831559023

theorem tailTrace_7851045 : CollatzResearch.WordTrace tailWord_7851045 prefixEnd_7851045 447928858342037831559023 := by
  unfold tailWord_7851045
  simp only [CollatzResearch.WordTrace]
  refine ⟨286351135842012291580450589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190900757228008194386967059 286351135842012291580450589)
  ·
    refine ⟨107381675940754609342668971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 286351135842012291580450589 107381675940754609342668971)
    ·
      refine ⟨161072513911131914014003457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107381675940754609342668971 161072513911131914014003457)
      ·
        refine ⟨120804385433348935510502593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161072513911131914014003457 120804385433348935510502593)
        ·
          refine ⟨90603289075011701632876945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120804385433348935510502593 90603289075011701632876945)
          ·
            refine ⟨67952466806258776224657709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90603289075011701632876945 67952466806258776224657709)
            ·
              refine ⟨25482175052347041084246641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67952466806258776224657709 25482175052347041084246641)
              ·
                refine ⟨19111631289260280813184981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25482175052347041084246641 19111631289260280813184981)
                ·
                  refine ⟨447928858342037831559023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19111631289260280813184981 447928858342037831559023)
                  ·
                    rfl

theorem cell23_7851045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 2, 7].length) (baseStart_7851045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7851045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7851045 prefixEnd_7851045 := by exact prefixLift 7851045
  have htrace : WordTrace (prefixWord ++ tailWord_7851045) baseStart_7851045 baseEnd_7851045 := by
    simpa [prefixWord, tailWord_7851045, baseEnd_7851045] using wordTrace_append hprefix tailTrace_7851045
  have hstable : (prefixWord ++ tailWord_7851045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7851045).length < 2 ^ (prefixWord ++ tailWord_7851045).sum := by decide
  have hdescent : baseEnd_7851045 < baseStart_7851045 := by decide
  rcases family_descends (prefixWord ++ tailWord_7851045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7851060 : List Nat := [2, 5, 1, 2, 1, 3, 2, 1, 1, 3, 2]
def baseStart_7851060 : Nat := 118140960795 + 7851060 * 2 ^ 59
def prefixEnd_7851060 : Nat := 4983230072969 + 3 ^ 40 * 7851060 * 2
def baseEnd_7851060 : Nat := 4031367427288157925343639

theorem tailTrace_7851060 : CollatzResearch.WordTrace tailWord_7851060 prefixEnd_7851060 4031367427288157925343639 := by
  unfold tailWord_7851060
  simp only [CollatzResearch.WordTrace]
  refine ⟨143175841468478974571123317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190901121957971966094831089 143175841468478974571123317)
  ·
    refine ⟨13422735137669903866042811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 143175841468478974571123317 13422735137669903866042811)
    ·
      refine ⟨20134102706504855799064217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13422735137669903866042811 20134102706504855799064217)
      ·
        refine ⟨15100577029878641849298163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20134102706504855799064217 15100577029878641849298163)
        ·
          refine ⟨22650865544817962773947245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15100577029878641849298163 22650865544817962773947245)
          ·
            refine ⟨8494074579306736040230217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22650865544817962773947245 8494074579306736040230217)
            ·
              refine ⟨6370555934480052030172663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8494074579306736040230217 6370555934480052030172663)
              ·
                refine ⟨9555833901720078045258995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6370555934480052030172663 9555833901720078045258995)
                ·
                  refine ⟨14333750852580117067888493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9555833901720078045258995 14333750852580117067888493)
                  ·
                    refine ⟨5375156569717543900458185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14333750852580117067888493 5375156569717543900458185)
                    ·
                      refine ⟨4031367427288157925343639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5375156569717543900458185 4031367427288157925343639)
                      ·
                        rfl

theorem cell23_7851060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 2, 1, 1, 3, 2].length) (baseStart_7851060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7851060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7851060 prefixEnd_7851060 := by exact prefixLift 7851060
  have htrace : WordTrace (prefixWord ++ tailWord_7851060) baseStart_7851060 baseEnd_7851060 := by
    simpa [prefixWord, tailWord_7851060, baseEnd_7851060] using wordTrace_append hprefix tailTrace_7851060
  have hstable : (prefixWord ++ tailWord_7851060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7851060).length < 2 ^ (prefixWord ++ tailWord_7851060).sum := by decide
  have hdescent : baseEnd_7851060 < baseStart_7851060 := by decide
  rcases family_descends (prefixWord ++ tailWord_7851060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7851075 : List Nat := [1, 1, 1, 3, 1, 2, 4, 1, 4, 5]
def baseStart_7851075 : Nat := 118140960795 + 7851075 * 2 ^ 59
def prefixEnd_7851075 : Nat := 4983230072969 + 3 ^ 40 * 7851075 * 2
def baseEnd_7851075 : Nat := 1343791709832658455552023

theorem tailTrace_7851075 : CollatzResearch.WordTrace tailWord_7851075 prefixEnd_7851075 1343791709832658455552023 := by
  unfold tailWord_7851075
  simp only [CollatzResearch.WordTrace]
  refine ⟨286352230031903606704042679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190901486687935737802695119 286352230031903606704042679)
  ·
    refine ⟨429528345047855410056064019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286352230031903606704042679 429528345047855410056064019)
    ·
      refine ⟨644292517571783115084096029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 429528345047855410056064019 644292517571783115084096029)
      ·
        refine ⟨241609694089418668156536011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 644292517571783115084096029 241609694089418668156536011)
        ·
          refine ⟨362414541134128002234804017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241609694089418668156536011 362414541134128002234804017)
          ·
            refine ⟨271810905850596001676103013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 362414541134128002234804017 271810905850596001676103013)
            ·
              refine ⟨50964544846986750314269315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 271810905850596001676103013 50964544846986750314269315)
              ·
                refine ⟨76446817270480125471403973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50964544846986750314269315 76446817270480125471403973)
                ·
                  refine ⟨14333778238215023525888245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76446817270480125471403973 14333778238215023525888245)
                  ·
                    refine ⟨1343791709832658455552023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14333778238215023525888245 1343791709832658455552023)
                    ·
                      rfl

theorem cell23_7851075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 1, 4, 5].length) (baseStart_7851075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7851075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7851075 prefixEnd_7851075 := by exact prefixLift 7851075
  have htrace : WordTrace (prefixWord ++ tailWord_7851075) baseStart_7851075 baseEnd_7851075 := by
    simpa [prefixWord, tailWord_7851075, baseEnd_7851075] using wordTrace_append hprefix tailTrace_7851075
  have hstable : (prefixWord ++ tailWord_7851075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7851075).length < 2 ^ (prefixWord ++ tailWord_7851075).sum := by decide
  have hdescent : baseEnd_7851075 < baseStart_7851075 := by decide
  rcases family_descends (prefixWord ++ tailWord_7851075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7851082 : List Nat := [3, 1, 2, 1, 1, 2, 2, 1, 1, 7, 2]
def baseStart_7851082 : Nat := 118140960795 + 7851082 * 2 ^ 59
def prefixEnd_7851082 : Nat := 4983230072969 + 3 ^ 40 * 7851082 * 2
def baseEnd_7851082 : Nat := 4031378723862556839268537

theorem tailTrace_7851082 : CollatzResearch.WordTrace tailWord_7851082 prefixEnd_7851082 4031378723862556839268537 := by
  unfold tailWord_7851082
  simp only [CollatzResearch.WordTrace]
  refine ⟨71588121335719561724886875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190901656895252164599698333 71588121335719561724886875)
  ·
    refine ⟨107382182003579342587330313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71588121335719561724886875 107382182003579342587330313)
    ·
      refine ⟨80536636502684506940497735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107382182003579342587330313 80536636502684506940497735)
      ·
        refine ⟨120804954754026760410746603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80536636502684506940497735 120804954754026760410746603)
        ·
          refine ⟨181207432131040140616119905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120804954754026760410746603 181207432131040140616119905)
          ·
            refine ⟨135905574098280105462089929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181207432131040140616119905 135905574098280105462089929)
            ·
              refine ⟨101929180573710079096567447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135905574098280105462089929 101929180573710079096567447)
              ·
                refine ⟨152893770860565118644851171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101929180573710079096567447 152893770860565118644851171)
                ·
                  refine ⟨229340656290847677967276757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 152893770860565118644851171 229340656290847677967276757)
                  ·
                    refine ⟨5375171631816742452358049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 229340656290847677967276757 5375171631816742452358049)
                    ·
                      refine ⟨4031378723862556839268537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5375171631816742452358049 4031378723862556839268537)
                      ·
                        rfl

theorem cell23_7851082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 1, 1, 7, 2].length) (baseStart_7851082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7851082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7851082 prefixEnd_7851082 := by exact prefixLift 7851082
  have htrace : WordTrace (prefixWord ++ tailWord_7851082) baseStart_7851082 baseEnd_7851082 := by
    simpa [prefixWord, tailWord_7851082, baseEnd_7851082] using wordTrace_append hprefix tailTrace_7851082
  have hstable : (prefixWord ++ tailWord_7851082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7851082).length < 2 ^ (prefixWord ++ tailWord_7851082).sum := by decide
  have hdescent : baseEnd_7851082 < baseStart_7851082 := by decide
  rcases family_descends (prefixWord ++ tailWord_7851082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7851129 : List Nat := [1, 2, 1, 3, 5, 1, 1, 2, 2, 1, 4]
def baseStart_7851129 : Nat := 118140960795 + 7851129 * 2 ^ 59
def prefixEnd_7851129 : Nat := 4983230072969 + 3 ^ 40 * 7851129 * 2
def baseEnd_7851129 : Nat := 4031402857453318155380821

theorem tailTrace_7851129 : CollatzResearch.WordTrace tailWord_7851129 prefixEnd_7851129 4031402857453318155380821 := by
  unfold tailWord_7851129
  simp only [CollatzResearch.WordTrace]
  refine ⟨286354199573707973926508441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190902799715805315951005627 286354199573707973926508441)
  ·
    refine ⟨214765649680280980444881331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286354199573707973926508441 214765649680280980444881331)
    ·
      refine ⟨322148474520421470667321997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214765649680280980444881331 322148474520421470667321997)
      ·
        refine ⟨120805677945158051500245749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 322148474520421470667321997 120805677945158051500245749)
        ·
          refine ⟨11325532307358567328148039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 120805677945158051500245749 11325532307358567328148039)
          ·
            refine ⟨16988298461037850992222059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11325532307358567328148039 16988298461037850992222059)
            ·
              refine ⟨25482447691556776488333089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16988298461037850992222059 25482447691556776488333089)
              ·
                refine ⟨19111835768667582366249817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25482447691556776488333089 19111835768667582366249817)
                ·
                  refine ⟨14333876826500686774687363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19111835768667582366249817 14333876826500686774687363)
                  ·
                    refine ⟨21500815239751030162031045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14333876826500686774687363 21500815239751030162031045)
                    ·
                      refine ⟨4031402857453318155380821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21500815239751030162031045 4031402857453318155380821)
                      ·
                        rfl

theorem cell23_7851129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 2, 2, 1, 4].length) (baseStart_7851129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7851129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7851129 prefixEnd_7851129 := by exact prefixLift 7851129
  have htrace : WordTrace (prefixWord ++ tailWord_7851129) baseStart_7851129 baseEnd_7851129 := by
    simpa [prefixWord, tailWord_7851129, baseEnd_7851129] using wordTrace_append hprefix tailTrace_7851129
  have hstable : (prefixWord ++ tailWord_7851129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7851129).length < 2 ^ (prefixWord ++ tailWord_7851129).sum := by decide
  have hdescent : baseEnd_7851129 < baseStart_7851129 := by decide
  rcases family_descends (prefixWord ++ tailWord_7851129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7851155 : List Nat := [1, 1, 1, 2, 1, 2, 4, 2, 1, 2, 6]
def baseStart_7851155 : Nat := 118140960795 + 7851155 * 2 ^ 59
def prefixEnd_7851155 : Nat := 4983230072969 + 3 ^ 40 * 7851155 * 2
def baseEnd_7851155 : Nat := 4031416207950335053655701

theorem tailTrace_7851155 : CollatzResearch.WordTrace tailWord_7851155 prefixEnd_7851155 4031416207950335053655701 := by
  unfold tailWord_7851155
  simp only [CollatzResearch.WordTrace]
  refine ⟨286355147871613780366954919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190903431914409186911303279 286355147871613780366954919)
  ·
    refine ⟨429532721807420670550432379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286355147871613780366954919 429532721807420670550432379)
    ·
      refine ⟨644299082711131005825648569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 429532721807420670550432379 644299082711131005825648569)
      ·
        refine ⟨483224312033348254369236427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 644299082711131005825648569 483224312033348254369236427)
        ·
          refine ⟨724836468050022381553854641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 483224312033348254369236427 724836468050022381553854641)
          ·
            refine ⟨543627351037516786165390981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 724836468050022381553854641 543627351037516786165390981)
            ·
              refine ⟨101930128319534397406010809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 543627351037516786165390981 101930128319534397406010809)
              ·
                refine ⟨76447596239650798054508107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101930128319534397406010809 76447596239650798054508107)
                ·
                  refine ⟨114671394359476197081762161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76447596239650798054508107 114671394359476197081762161)
                  ·
                    refine ⟨86003545769607147811321621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 114671394359476197081762161 86003545769607147811321621)
                    ·
                      refine ⟨4031416207950335053655701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86003545769607147811321621 4031416207950335053655701)
                      ·
                        rfl

theorem cell23_7851155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 2, 1, 2, 6].length) (baseStart_7851155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7851155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7851155 prefixEnd_7851155 := by exact prefixLift 7851155
  have htrace : WordTrace (prefixWord ++ tailWord_7851155) baseStart_7851155 baseEnd_7851155 := by
    simpa [prefixWord, tailWord_7851155, baseEnd_7851155] using wordTrace_append hprefix tailTrace_7851155
  have hstable : (prefixWord ++ tailWord_7851155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7851155).length < 2 ^ (prefixWord ++ tailWord_7851155).sum := by decide
  have hdescent : baseEnd_7851155 < baseStart_7851155 := by decide
  rcases family_descends (prefixWord ++ tailWord_7851155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7851166 : List Nat := [4, 3, 1, 1, 2, 1, 1, 3, 2, 2, 3]
def baseStart_7851166 : Nat := 118140960795 + 7851166 * 2 ^ 59
def prefixEnd_7851166 : Nat := 4983230072969 + 3 ^ 40 * 7851166 * 2
def baseEnd_7851166 : Nat := 4031421856237534510618151

theorem tailTrace_7851166 : CollatzResearch.WordTrace tailWord_7851166 prefixEnd_7851166 4031421856237534510618151 := by
  unfold tailWord_7851166
  simp only [CollatzResearch.WordTrace]
  refine ⟨35794443634321741155700669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 190903699383049286163736901 35794443634321741155700669)
  ·
    refine ⟨13422916362870652933387751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35794443634321741155700669 13422916362870652933387751)
    ·
      refine ⟨20134374544305979400081627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13422916362870652933387751 20134374544305979400081627)
      ·
        refine ⟨30201561816458969100122441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20134374544305979400081627 30201561816458969100122441)
        ·
          refine ⟨22651171362344226825091831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30201561816458969100122441 22651171362344226825091831)
          ·
            refine ⟨33976757043516340237637747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22651171362344226825091831 33976757043516340237637747)
            ·
              refine ⟨50965135565274510356456621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33976757043516340237637747 50965135565274510356456621)
              ·
                refine ⟨19111925836977941383671233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50965135565274510356456621 19111925836977941383671233)
                ·
                  refine ⟨14333944377733456037753425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19111925836977941383671233 14333944377733456037753425)
                  ·
                    refine ⟨10750458283300092028315069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14333944377733456037753425 10750458283300092028315069)
                    ·
                      refine ⟨4031421856237534510618151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10750458283300092028315069 4031421856237534510618151)
                      ·
                        rfl

theorem cell23_7851166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 3, 2, 2, 3].length) (baseStart_7851166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7851166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7851166 prefixEnd_7851166 := by exact prefixLift 7851166
  have htrace : WordTrace (prefixWord ++ tailWord_7851166) baseStart_7851166 baseEnd_7851166 := by
    simpa [prefixWord, tailWord_7851166, baseEnd_7851166] using wordTrace_append hprefix tailTrace_7851166
  have hstable : (prefixWord ++ tailWord_7851166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7851166).length < 2 ^ (prefixWord ++ tailWord_7851166).sum := by decide
  have hdescent : baseEnd_7851166 < baseStart_7851166 := by decide
  rcases family_descends (prefixWord ++ tailWord_7851166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7851236 : List Nat := [2, 3, 1, 1, 1, 2, 6, 1, 1, 1, 4]
def baseStart_7851236 : Nat := 118140960795 + 7851236 * 2 ^ 59
def prefixEnd_7851236 : Nat := 4983230072969 + 3 ^ 40 * 7851236 * 2
def baseEnd_7851236 : Nat := 4031457799883349236742829

theorem tailTrace_7851236 : CollatzResearch.WordTrace tailWord_7851236 prefixEnd_7851236 4031457799883349236742829 := by
  unfold tailWord_7851236
  simp only [CollatzResearch.WordTrace]
  refine ⟨143179051092160165600326781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190905401456213554133769041 143179051092160165600326781)
  ·
    refine ⟨53692144159560062100122543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143179051092160165600326781 53692144159560062100122543)
    ·
      refine ⟨80538216239340093150183815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53692144159560062100122543 80538216239340093150183815)
      ·
        refine ⟨120807324359010139725275723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80538216239340093150183815 120807324359010139725275723)
        ·
          refine ⟨181210986538515209587913585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120807324359010139725275723 181210986538515209587913585)
          ·
            refine ⟨135908239903886407190935189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181210986538515209587913585 135908239903886407190935189)
            ·
              refine ⟨6370698745494675337075087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 135908239903886407190935189 6370698745494675337075087)
              ·
                refine ⟨9556048118242013005612631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6370698745494675337075087 9556048118242013005612631)
                ·
                  refine ⟨14334072177363019508418947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9556048118242013005612631 14334072177363019508418947)
                  ·
                    refine ⟨21501108266044529262628421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14334072177363019508418947 21501108266044529262628421)
                    ·
                      refine ⟨4031457799883349236742829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21501108266044529262628421 4031457799883349236742829)
                      ·
                        rfl

theorem cell23_7851236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 6, 1, 1, 1, 4].length) (baseStart_7851236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7851236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7851236 prefixEnd_7851236 := by exact prefixLift 7851236
  have htrace : WordTrace (prefixWord ++ tailWord_7851236) baseStart_7851236 baseEnd_7851236 := by
    simpa [prefixWord, tailWord_7851236, baseEnd_7851236] using wordTrace_append hprefix tailTrace_7851236
  have hstable : (prefixWord ++ tailWord_7851236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7851236).length < 2 ^ (prefixWord ++ tailWord_7851236).sum := by decide
  have hdescent : baseEnd_7851236 < baseStart_7851236 := by decide
  rcases family_descends (prefixWord ++ tailWord_7851236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7851242 : List Nat := [3, 1, 3, 1, 1, 4, 10]
def baseStart_7851242 : Nat := 118140960795 + 7851242 * 2 ^ 59
def prefixEnd_7851242 : Nat := 4983230072969 + 3 ^ 40 * 7851242 * 2
def baseEnd_7851242 : Nat := 49771121984781187818121

theorem tailTrace_7851242 : CollatzResearch.WordTrace tailWord_7851242 prefixEnd_7851242 49771121984781187818121 := by
  unfold tailWord_7851242
  simp only [CollatzResearch.WordTrace]
  refine ⟨71589580255574648556342995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190905547348199062816914653 71589580255574648556342995)
  ·
    refine ⟨107384370383361972834514493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71589580255574648556342995 107384370383361972834514493)
    ·
      refine ⟨40269138893760739812942935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107384370383361972834514493 40269138893760739812942935)
      ·
        refine ⟨60403708340641109719414403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40269138893760739812942935 60403708340641109719414403)
        ·
          refine ⟨90605562510961664579121605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60403708340641109719414403 90605562510961664579121605)
          ·
            refine ⟨16988542970805312108585301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90605562510961664579121605 16988542970805312108585301)
            ·
              refine ⟨49771121984781187818121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 16988542970805312108585301 49771121984781187818121)
              ·
                rfl

theorem cell23_7851242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 10].length) (baseStart_7851242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7851242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7851242 prefixEnd_7851242 := by exact prefixLift 7851242
  have htrace : WordTrace (prefixWord ++ tailWord_7851242) baseStart_7851242 baseEnd_7851242 := by
    simpa [prefixWord, tailWord_7851242, baseEnd_7851242] using wordTrace_append hprefix tailTrace_7851242
  have hstable : (prefixWord ++ tailWord_7851242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7851242).length < 2 ^ (prefixWord ++ tailWord_7851242).sum := by decide
  have hdescent : baseEnd_7851242 < baseStart_7851242 := by decide
  rcases family_descends (prefixWord ++ tailWord_7851242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7851246 : List Nat := [4, 1, 2, 1, 1, 1, 5, 2, 2, 4]
def baseStart_7851246 : Nat := 118140960795 + 7851246 * 2 ^ 59
def prefixEnd_7851246 : Nat := 4983230072969 + 3 ^ 40 * 7851246 * 2
def baseEnd_7851246 : Nat := 1343820978229964732539261

theorem tailTrace_7851246 : CollatzResearch.WordTrace tailWord_7851246 prefixEnd_7851246 1343820978229964732539261 := by
  unfold tailWord_7851246
  simp only [CollatzResearch.WordTrace]
  refine ⟨35794808364285512863564699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 190905644609522735272345061 35794808364285512863564699)
  ·
    refine ⟨53692212546428269295347049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35794808364285512863564699 53692212546428269295347049)
    ·
      refine ⟨40269159409821201971510287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53692212546428269295347049 40269159409821201971510287)
      ·
        refine ⟨60403739114731802957265431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40269159409821201971510287 60403739114731802957265431)
        ·
          refine ⟨90605608672097704435898147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60403739114731802957265431 90605608672097704435898147)
          ·
            refine ⟨135908413008146556653847221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90605608672097704435898147 135908413008146556653847221)
            ·
              refine ⟨12741413719513739686298177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 135908413008146556653847221 12741413719513739686298177)
              ·
                refine ⟨9556060289635304764723633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12741413719513739686298177 9556060289635304764723633)
                ·
                  refine ⟨7167045217226478573542725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9556060289635304764723633 7167045217226478573542725)
                  ·
                    refine ⟨1343820978229964732539261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7167045217226478573542725 1343820978229964732539261)
                    ·
                      rfl

theorem cell23_7851246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 5, 2, 2, 4].length) (baseStart_7851246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7851246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7851246 prefixEnd_7851246 := by exact prefixLift 7851246
  have htrace : WordTrace (prefixWord ++ tailWord_7851246) baseStart_7851246 baseEnd_7851246 := by
    simpa [prefixWord, tailWord_7851246, baseEnd_7851246] using wordTrace_append hprefix tailTrace_7851246
  have hstable : (prefixWord ++ tailWord_7851246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7851246).length < 2 ^ (prefixWord ++ tailWord_7851246).sum := by decide
  have hdescent : baseEnd_7851246 < baseStart_7851246 := by decide
  rcases family_descends (prefixWord ++ tailWord_7851246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7851266 : List Nat := [3, 4, 1, 1, 3, 1, 1, 1, 1, 1, 6]
def baseStart_7851266 : Nat := 118140960795 + 7851266 * 2 ^ 59
def prefixEnd_7851266 : Nat := 4983230072969 + 3 ^ 40 * 7851266 * 2
def baseEnd_7851266 : Nat := 4031473204302984119367691

theorem tailTrace_7851266 : CollatzResearch.WordTrace tailWord_7851266 prefixEnd_7851266 4031473204302984119367691 := by
  unfold tailWord_7851266
  simp only [CollatzResearch.WordTrace]
  refine ⟨71589799093552911581061413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190906130916141097549497101 71589799093552911581061413)
  ·
    refine ⟨13423087330041170921449015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71589799093552911581061413 13423087330041170921449015)
    ·
      refine ⟨20134630995061756382173523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13423087330041170921449015 20134630995061756382173523)
      ·
        refine ⟨30201946492592634573260285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20134630995061756382173523 30201946492592634573260285)
        ·
          refine ⟨11325729934722237964972607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30201946492592634573260285 11325729934722237964972607)
          ·
            refine ⟨16988594902083356947458911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11325729934722237964972607 16988594902083356947458911)
            ·
              refine ⟨25482892353125035421188367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16988594902083356947458911 25482892353125035421188367)
              ·
                refine ⟨38224338529687553131782551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25482892353125035421188367 38224338529687553131782551)
                ·
                  refine ⟨57336507794531329697673827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38224338529687553131782551 57336507794531329697673827)
                  ·
                    refine ⟨86004761691796994546510741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57336507794531329697673827 86004761691796994546510741)
                    ·
                      refine ⟨4031473204302984119367691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86004761691796994546510741 4031473204302984119367691)
                      ·
                        rfl

theorem cell23_7851266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 1, 1, 1, 6].length) (baseStart_7851266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7851266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7851266 prefixEnd_7851266 := by exact prefixLift 7851266
  have htrace : WordTrace (prefixWord ++ tailWord_7851266) baseStart_7851266 baseEnd_7851266 := by
    simpa [prefixWord, tailWord_7851266, baseEnd_7851266] using wordTrace_append hprefix tailTrace_7851266
  have hstable : (prefixWord ++ tailWord_7851266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7851266).length < 2 ^ (prefixWord ++ tailWord_7851266).sum := by decide
  have hdescent : baseEnd_7851266 < baseStart_7851266 := by decide
  rcases family_descends (prefixWord ++ tailWord_7851266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7851312 : List Nat := [2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 5]
def baseStart_7851312 : Nat := 118140960795 + 7851312 * 2 ^ 59
def prefixEnd_7851312 : Nat := 4983230072969 + 3 ^ 40 * 7851312 * 2
def baseEnd_7851312 : Nat := 4031496824413090939392479

theorem tailTrace_7851312 : CollatzResearch.WordTrace tailWord_7851312 prefixEnd_7851312 4031496824413090939392479 := by
  unfold tailWord_7851312
  simp only [CollatzResearch.WordTrace]
  refine ⟨143180437066022498090210095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190907249421363330786946793 143180437066022498090210095)
  ·
    refine ⟨214770655599033747135315143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143180437066022498090210095 214770655599033747135315143)
    ·
      refine ⟨322155983398550620702972715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214770655599033747135315143 322155983398550620702972715)
      ·
        refine ⟨483233975097825931054459073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322155983398550620702972715 483233975097825931054459073)
        ·
          refine ⟨362425481323369448290844305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 483233975097825931054459073 362425481323369448290844305)
          ·
            refine ⟨271819110992527086218133229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 362425481323369448290844305 271819110992527086218133229)
            ·
              refine ⟨101932166622197657331799961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 271819110992527086218133229 101932166622197657331799961)
              ·
                refine ⟨76449124966648242998849971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101932166622197657331799961 76449124966648242998849971)
                ·
                  refine ⟨114673687449972364498274957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76449124966648242998849971 114673687449972364498274957)
                  ·
                    refine ⟨43002632793739636686853109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 114673687449972364498274957 43002632793739636686853109)
                    ·
                      refine ⟨4031496824413090939392479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43002632793739636686853109 4031496824413090939392479)
                      ·
                        rfl

theorem cell23_7851312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 5].length) (baseStart_7851312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7851312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7851312 prefixEnd_7851312 := by exact prefixLift 7851312
  have htrace : WordTrace (prefixWord ++ tailWord_7851312) baseStart_7851312 baseEnd_7851312 := by
    simpa [prefixWord, tailWord_7851312, baseEnd_7851312] using wordTrace_append hprefix tailTrace_7851312
  have hstable : (prefixWord ++ tailWord_7851312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7851312).length < 2 ^ (prefixWord ++ tailWord_7851312).sum := by decide
  have hdescent : baseEnd_7851312 < baseStart_7851312 := by decide
  rcases family_descends (prefixWord ++ tailWord_7851312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7851359 : List Nat := [1, 1, 2, 3, 1, 2, 1, 4, 2, 3, 3]
def baseStart_7851359 : Nat := 118140960795 + 7851359 * 2 ^ 59
def prefixEnd_7851359 : Nat := 4983230072969 + 3 ^ 40 * 7851359 * 2
def baseEnd_7851359 : Nat := 4031520958003852255504763

theorem tailTrace_7851359 : CollatzResearch.WordTrace tailWord_7851359 prefixEnd_7851359 4031520958003852255504763 := by
  unfold tailWord_7851359
  simp only [CollatzResearch.WordTrace]
  refine ⟨286362588362874723207381131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190908392241916482138254087 286362588362874723207381131)
  ·
    refine ⟨429543882544312084811071697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286362588362874723207381131 429543882544312084811071697)
    ·
      refine ⟨322157911908234063608303773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 429543882544312084811071697 322157911908234063608303773)
      ·
        refine ⟨120809216965587773853113915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 322157911908234063608303773 120809216965587773853113915)
        ·
          refine ⟨181213825448381660779670873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120809216965587773853113915 181213825448381660779670873)
          ·
            refine ⟨135910369086286245584753155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181213825448381660779670873 135910369086286245584753155)
            ·
              refine ⟨203865553629429368377129733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135910369086286245584753155 203865553629429368377129733)
              ·
                refine ⟨38224791305518006570711825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 203865553629429368377129733 38224791305518006570711825)
                ·
                  refine ⟨28668593479138504928033869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38224791305518006570711825 28668593479138504928033869)
                  ·
                    refine ⟨10750722554676939348012701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28668593479138504928033869 10750722554676939348012701)
                    ·
                      refine ⟨4031520958003852255504763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10750722554676939348012701 4031520958003852255504763)
                      ·
                        rfl

theorem cell23_7851359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 4, 2, 3, 3].length) (baseStart_7851359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7851359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7851359 prefixEnd_7851359 := by exact prefixLift 7851359
  have htrace : WordTrace (prefixWord ++ tailWord_7851359) baseStart_7851359 baseEnd_7851359 := by
    simpa [prefixWord, tailWord_7851359, baseEnd_7851359] using wordTrace_append hprefix tailTrace_7851359
  have hstable : (prefixWord ++ tailWord_7851359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7851359).length < 2 ^ (prefixWord ++ tailWord_7851359).sum := by decide
  have hdescent : baseEnd_7851359 < baseStart_7851359 := by decide
  rcases family_descends (prefixWord ++ tailWord_7851359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7851360 : List Nat := [2, 1, 1, 3, 4, 2, 2, 2, 2, 2, 2]
def baseStart_7851360 : Nat := 118140960795 + 7851360 * 2 ^ 59
def prefixEnd_7851360 : Nat := 4983230072969 + 3 ^ 40 * 7851360 * 2
def baseEnd_7851360 : Nat := 4031521471484506751592259

theorem tailTrace_7851360 : CollatzResearch.WordTrace tailWord_7851360 prefixEnd_7851360 4031521471484506751592259 := by
  unfold tailWord_7851360
  simp only [CollatzResearch.WordTrace]
  refine ⟨143181312417935550189083767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190908416557247400252111689 143181312417935550189083767)
  ·
    refine ⟨214771968626903325283625651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143181312417935550189083767 214771968626903325283625651)
    ·
      refine ⟨322157952940354987925438477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214771968626903325283625651 322157952940354987925438477)
      ·
        refine ⟨120809232352633120472039429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 322157952940354987925438477 120809232352633120472039429)
        ·
          refine ⟨22651731066118710088507393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 120809232352633120472039429 22651731066118710088507393)
          ·
            refine ⟨16988798299589032566380545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22651731066118710088507393 16988798299589032566380545)
            ·
              refine ⟨12741598724691774424785409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16988798299589032566380545 12741598724691774424785409)
              ·
                refine ⟨9556199043518830818589057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12741598724691774424785409 9556199043518830818589057)
                ·
                  refine ⟨7167149282639123113941793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9556199043518830818589057 7167149282639123113941793)
                  ·
                    refine ⟨5375361961979342335456345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7167149282639123113941793 5375361961979342335456345)
                    ·
                      refine ⟨4031521471484506751592259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5375361961979342335456345 4031521471484506751592259)
                      ·
                        rfl

theorem cell23_7851360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 2, 2, 2, 2, 2].length) (baseStart_7851360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7851360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7851360 prefixEnd_7851360 := by exact prefixLift 7851360
  have htrace : WordTrace (prefixWord ++ tailWord_7851360) baseStart_7851360 baseEnd_7851360 := by
    simpa [prefixWord, tailWord_7851360, baseEnd_7851360] using wordTrace_append hprefix tailTrace_7851360
  have hstable : (prefixWord ++ tailWord_7851360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7851360).length < 2 ^ (prefixWord ++ tailWord_7851360).sum := by decide
  have hdescent : baseEnd_7851360 < baseStart_7851360 := by decide
  rcases family_descends (prefixWord ++ tailWord_7851360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7851396 : List Nat := [2, 3, 2, 1, 1, 3, 3, 1, 2, 5]
def baseStart_7851396 : Nat := 118140960795 + 7851396 * 2 ^ 59
def prefixEnd_7851396 : Nat := 4983230072969 + 3 ^ 40 * 7851396 * 2
def baseEnd_7851396 : Nat := 1343846652262689536914031

theorem tailTrace_7851396 : CollatzResearch.WordTrace tailWord_7851396 prefixEnd_7851396 1343846652262689536914031 := by
  unfold tailWord_7851396
  simp only [CollatzResearch.WordTrace]
  refine ⟨143181968931870339263239021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190909291909160452350985361 143181968931870339263239021)
  ·
    refine ⟨53693238349451377223714633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143181968931870339263239021 53693238349451377223714633)
    ·
      refine ⟨40269928762088532917785975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53693238349451377223714633 40269928762088532917785975)
      ·
        refine ⟨60404893143132799376678963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40269928762088532917785975 60404893143132799376678963)
        ·
          refine ⟨90607339714699199065018445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60404893143132799376678963 90607339714699199065018445)
          ·
            refine ⟨33977752393012199649381917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90607339714699199065018445 33977752393012199649381917)
            ·
              refine ⟨12741657147379574868518219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33977752393012199649381917 12741657147379574868518219)
              ·
                refine ⟨19112485721069362302777329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12741657147379574868518219 19112485721069362302777329)
                ·
                  refine ⟨14334364290802021727082997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19112485721069362302777329 14334364290802021727082997)
                  ·
                    refine ⟨1343846652262689536914031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14334364290802021727082997 1343846652262689536914031)
                    ·
                      rfl

theorem cell23_7851396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 3, 1, 2, 5].length) (baseStart_7851396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7851396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7851396 prefixEnd_7851396 := by exact prefixLift 7851396
  have htrace : WordTrace (prefixWord ++ tailWord_7851396) baseStart_7851396 baseEnd_7851396 := by
    simpa [prefixWord, tailWord_7851396, baseEnd_7851396] using wordTrace_append hprefix tailTrace_7851396
  have hstable : (prefixWord ++ tailWord_7851396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7851396).length < 2 ^ (prefixWord ++ tailWord_7851396).sum := by decide
  have hdescent : baseEnd_7851396 < baseStart_7851396 := by decide
  rcases family_descends (prefixWord ++ tailWord_7851396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7851439 : List Nat := [1, 1, 2, 1, 2, 2, 1, 7, 6]
def baseStart_7851439 : Nat := 118140960795 + 7851439 * 2 ^ 59
def prefixEnd_7851439 : Nat := 4983230072969 + 3 ^ 40 * 7851439 * 2
def baseEnd_7851439 : Nat := 447951337384023549167155

theorem tailTrace_7851439 : CollatzResearch.WordTrace tailWord_7851439 prefixEnd_7851439 447951337384023549167155 := by
  unfold tailWord_7851439
  simp only [CollatzResearch.WordTrace]
  refine ⟨286365506202584896870293371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190910337468389931246862247 286365506202584896870293371)
  ·
    refine ⟨429548259303877345305440057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286365506202584896870293371 429548259303877345305440057)
    ·
      refine ⟨322161194477908008979080043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 429548259303877345305440057 322161194477908008979080043)
      ·
        refine ⟨483241791716862013468620065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322161194477908008979080043 483241791716862013468620065)
        ·
          refine ⟨362431343787646510101465049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 483241791716862013468620065 362431343787646510101465049)
          ·
            refine ⟨271823507840734882576098787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 362431343787646510101465049 271823507840734882576098787)
            ·
              refine ⟨407735261761102323864148181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 271823507840734882576098787 407735261761102323864148181)
              ·
                refine ⟨9556295197525835715565973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 407735261761102323864148181 9556295197525835715565973)
                ·
                  refine ⟨447951337384023549167155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9556295197525835715565973 447951337384023549167155)
                  ·
                    rfl

theorem cell23_7851439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 7, 6].length) (baseStart_7851439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7851439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7851439 prefixEnd_7851439 := by exact prefixLift 7851439
  have htrace : WordTrace (prefixWord ++ tailWord_7851439) baseStart_7851439 baseEnd_7851439 := by
    simpa [prefixWord, tailWord_7851439, baseEnd_7851439] using wordTrace_append hprefix tailTrace_7851439
  have hstable : (prefixWord ++ tailWord_7851439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7851439).length < 2 ^ (prefixWord ++ tailWord_7851439).sum := by decide
  have hdescent : baseEnd_7851439 < baseStart_7851439 := by decide
  rcases family_descends (prefixWord ++ tailWord_7851439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7851510 : List Nat := [5, 1, 1, 1, 2, 2, 1, 3, 2, 3, 2]
def baseStart_7851510 : Nat := 118140960795 + 7851510 * 2 ^ 59
def prefixEnd_7851510 : Nat := 4983230072969 + 3 ^ 40 * 7851510 * 2
def baseEnd_7851510 : Nat := 4031598493582681164716569

theorem tailTrace_7851510 : CollatzResearch.WordTrace tailWord_7851510 prefixEnd_7851510 4031598493582681164716569 := by
  unfold tailWord_7851510
  simp only [CollatzResearch.WordTrace]
  refine ⟨17898005986582979749757999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 190912063856885117330751989 17898005986582979749757999)
  ·
    refine ⟨26847008979874469624636999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17898005986582979749757999 26847008979874469624636999)
    ·
      refine ⟨40270513469811704436955499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26847008979874469624636999 40270513469811704436955499)
      ·
        refine ⟨60405770204717556655433249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40270513469811704436955499 60405770204717556655433249)
        ·
          refine ⟨45304327653538167491574937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60405770204717556655433249 45304327653538167491574937)
          ·
            refine ⟨33978245740153625618681203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45304327653538167491574937 33978245740153625618681203)
            ·
              refine ⟨50967368610230438428021805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33978245740153625618681203 50967368610230438428021805)
              ·
                refine ⟨19112763228836414410508177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50967368610230438428021805 19112763228836414410508177)
                ·
                  refine ⟨14334572421627310807881133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19112763228836414410508177 14334572421627310807881133)
                  ·
                    refine ⟨5375464658110241552955425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14334572421627310807881133 5375464658110241552955425)
                    ·
                      refine ⟨4031598493582681164716569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5375464658110241552955425 4031598493582681164716569)
                      ·
                        rfl

theorem cell23_7851510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 3, 2, 3, 2].length) (baseStart_7851510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7851510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7851510 prefixEnd_7851510 := by exact prefixLift 7851510
  have htrace : WordTrace (prefixWord ++ tailWord_7851510) baseStart_7851510 baseEnd_7851510 := by
    simpa [prefixWord, tailWord_7851510, baseEnd_7851510] using wordTrace_append hprefix tailTrace_7851510
  have hstable : (prefixWord ++ tailWord_7851510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7851510).length < 2 ^ (prefixWord ++ tailWord_7851510).sum := by decide
  have hdescent : baseEnd_7851510 < baseStart_7851510 := by decide
  rcases family_descends (prefixWord ++ tailWord_7851510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7851516 : List Nat := [2, 2, 2, 1, 2, 1, 2, 1, 6, 4]
def baseStart_7851516 : Nat := 118140960795 + 7851516 * 2 ^ 59
def prefixEnd_7851516 : Nat := 4983230072969 + 3 ^ 40 * 7851516 * 2
def baseEnd_7851516 : Nat := 1343867191488869380413847

theorem tailTrace_7851516 : CollatzResearch.WordTrace tailWord_7851516 prefixEnd_7851516 1343867191488869380413847 := by
  unfold tailWord_7851516
  simp only [CollatzResearch.WordTrace]
  refine ⟨143184157311652969510423201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190912209748870626013897601 143184157311652969510423201)
  ·
    refine ⟨107388117983739727132817401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143184157311652969510423201 107388117983739727132817401)
    ·
      refine ⟨80541088487804795349613051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107388117983739727132817401 80541088487804795349613051)
      ·
        refine ⟨120811632731707193024419577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80541088487804795349613051 120811632731707193024419577)
        ·
          refine ⟨90608724548780394768314683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120811632731707193024419577 90608724548780394768314683)
          ·
            refine ⟨135913086823170592152472025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90608724548780394768314683 135913086823170592152472025)
            ·
              refine ⟨101934815117377944114354019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135913086823170592152472025 101934815117377944114354019)
              ·
                refine ⟨152902222676066916171531029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101934815117377944114354019 152902222676066916171531029)
                ·
                  refine ⟨7167291687940636695540517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 152902222676066916171531029 7167291687940636695540517)
                  ·
                    refine ⟨1343867191488869380413847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7167291687940636695540517 1343867191488869380413847)
                    ·
                      rfl

theorem cell23_7851516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 1, 6, 4].length) (baseStart_7851516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7851516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7851516 prefixEnd_7851516 := by exact prefixLift 7851516
  have htrace : WordTrace (prefixWord ++ tailWord_7851516) baseStart_7851516 baseEnd_7851516 := by
    simpa [prefixWord, tailWord_7851516, baseEnd_7851516] using wordTrace_append hprefix tailTrace_7851516
  have hstable : (prefixWord ++ tailWord_7851516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7851516).length < 2 ^ (prefixWord ++ tailWord_7851516).sum := by decide
  have hdescent : baseEnd_7851516 < baseStart_7851516 := by decide
  rcases family_descends (prefixWord ++ tailWord_7851516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7851519 : List Nat := [1, 1, 2, 2, 1, 2, 2, 2, 3, 1, 6]
def baseStart_7851519 : Nat := 118140960795 + 7851519 * 2 ^ 59
def prefixEnd_7851519 : Nat := 4983230072969 + 3 ^ 40 * 7851519 * 2
def baseEnd_7851519 : Nat := 4031603114908571629504027

theorem tailTrace_7851519 : CollatzResearch.WordTrace tailWord_7851519 prefixEnd_7851519 4031603114908571629504027 := by
  unfold tailWord_7851519
  simp only [CollatzResearch.WordTrace]
  refine ⟨286368424042295070533205611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190912282694863380355470407 286368424042295070533205611)
  ·
    refine ⟨429552636063442605799808417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286368424042295070533205611 429552636063442605799808417)
    ·
      refine ⟨322164477047581954349856313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 429552636063442605799808417 322164477047581954349856313)
      ·
        refine ⟨241623357785686465762392235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 322164477047581954349856313 241623357785686465762392235)
        ·
          refine ⟨362435036678529698643588353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241623357785686465762392235 362435036678529698643588353)
          ·
            refine ⟨271826277508897273982691265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 362435036678529698643588353 271826277508897273982691265)
            ·
              refine ⟨203869708131672955487018449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 271826277508897273982691265 203869708131672955487018449)
              ·
                refine ⟨152902281098754716615263837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 203869708131672955487018449 152902281098754716615263837)
                ·
                  refine ⟨57338355412033018730723939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 152902281098754716615263837 57338355412033018730723939)
                  ·
                    refine ⟨86007533118049528096085909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57338355412033018730723939 86007533118049528096085909)
                    ·
                      refine ⟨4031603114908571629504027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86007533118049528096085909 4031603114908571629504027)
                      ·
                        rfl

theorem cell23_7851519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 3, 1, 6].length) (baseStart_7851519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7851519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7851519 prefixEnd_7851519 := by exact prefixLift 7851519
  have htrace : WordTrace (prefixWord ++ tailWord_7851519) baseStart_7851519 baseEnd_7851519 := by
    simpa [prefixWord, tailWord_7851519, baseEnd_7851519] using wordTrace_append hprefix tailTrace_7851519
  have hstable : (prefixWord ++ tailWord_7851519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7851519).length < 2 ^ (prefixWord ++ tailWord_7851519).sum := by decide
  have hdescent : baseEnd_7851519 < baseStart_7851519 := by decide
  rcases family_descends (prefixWord ++ tailWord_7851519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7851523 : List Nat := [1, 1, 1, 3, 2, 1, 2, 1, 7, 2, 2]
def baseStart_7851523 : Nat := 118140960795 + 7851523 * 2 ^ 59
def prefixEnd_7851523 : Nat := 4983230072969 + 3 ^ 40 * 7851523 * 2
def baseEnd_7851523 : Nat := 4031605168831189613854009

theorem tailTrace_7851523 : CollatzResearch.WordTrace tailWord_7851523 prefixEnd_7851523 4031605168831189613854009 := by
  unfold tailWord_7851523
  simp only [CollatzResearch.WordTrace]
  refine ⟨286368569934280579216351223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190912379956187052810900815 286368569934280579216351223)
  ·
    refine ⟨429552854901420868824526835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286368569934280579216351223 429552854901420868824526835)
    ·
      refine ⟨644329282352131303236790253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 429552854901420868824526835 644329282352131303236790253)
      ·
        refine ⟨241623480882049238713796345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 644329282352131303236790253 241623480882049238713796345)
        ·
          refine ⟨181217610661536929035347259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 241623480882049238713796345 181217610661536929035347259)
          ·
            refine ⟨271826415992305393553020889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181217610661536929035347259 271826415992305393553020889)
            ·
              refine ⟨203869811994229045164765667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 271826415992305393553020889 203869811994229045164765667)
              ·
                refine ⟨305804717991343567747148501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 203869811994229045164765667 305804717991343567747148501)
                ·
                  refine ⟨7167298077922114869073793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 305804717991343567747148501 7167298077922114869073793)
                  ·
                    refine ⟨5375473558441586151805345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7167298077922114869073793 5375473558441586151805345)
                    ·
                      refine ⟨4031605168831189613854009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5375473558441586151805345 4031605168831189613854009)
                      ·
                        rfl

theorem cell23_7851523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 7, 2, 2].length) (baseStart_7851523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7851523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7851523 prefixEnd_7851523 := by exact prefixLift 7851523
  have htrace : WordTrace (prefixWord ++ tailWord_7851523) baseStart_7851523 baseEnd_7851523 := by
    simpa [prefixWord, tailWord_7851523, baseEnd_7851523] using wordTrace_append hprefix tailTrace_7851523
  have hstable : (prefixWord ++ tailWord_7851523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7851523).length < 2 ^ (prefixWord ++ tailWord_7851523).sum := by decide
  have hdescent : baseEnd_7851523 < baseStart_7851523 := by decide
  rcases family_descends (prefixWord ++ tailWord_7851523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7851553 : List Nat := [1, 2, 3, 2, 2, 3, 2, 1, 1, 2, 4]
def baseStart_7851553 : Nat := 118140960795 + 7851553 * 2 ^ 59
def prefixEnd_7851553 : Nat := 4983230072969 + 3 ^ 40 * 7851553 * 2
def baseEnd_7851553 : Nat := 4031620573250824496478871

theorem tailTrace_7851553 : CollatzResearch.WordTrace tailWord_7851553 prefixEnd_7851553 4031620573250824496478871 := by
  unfold tailWord_7851553
  simp only [CollatzResearch.WordTrace]
  refine ⟨286369664124171894339943313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190913109416114596226628875 286369664124171894339943313)
  ·
    refine ⟨214777248093128920754957485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286369664124171894339943313 214777248093128920754957485)
    ·
      refine ⟨80541468034923345283109057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214777248093128920754957485 80541468034923345283109057)
      ·
        refine ⟨60406101026192508962331793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80541468034923345283109057 60406101026192508962331793)
        ·
          refine ⟨45304575769644381721748845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60406101026192508962331793 45304575769644381721748845)
          ·
            refine ⟨16989215913616643145655817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45304575769644381721748845 16989215913616643145655817)
            ·
              refine ⟨12741911935212482359241863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16989215913616643145655817 12741911935212482359241863)
              ·
                refine ⟨19112867902818723538862795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12741911935212482359241863 19112867902818723538862795)
                ·
                  refine ⟨28669301854228085308294193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19112867902818723538862795 28669301854228085308294193)
                  ·
                    refine ⟨21501976390671063981220645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28669301854228085308294193 21501976390671063981220645)
                    ·
                      refine ⟨4031620573250824496478871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21501976390671063981220645 4031620573250824496478871)
                      ·
                        rfl

theorem cell23_7851553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 2, 1, 1, 2, 4].length) (baseStart_7851553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7851553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7851553 prefixEnd_7851553 := by exact prefixLift 7851553
  have htrace : WordTrace (prefixWord ++ tailWord_7851553) baseStart_7851553 baseEnd_7851553 := by
    simpa [prefixWord, tailWord_7851553, baseEnd_7851553] using wordTrace_append hprefix tailTrace_7851553
  have hstable : (prefixWord ++ tailWord_7851553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7851553).length < 2 ^ (prefixWord ++ tailWord_7851553).sum := by decide
  have hdescent : baseEnd_7851553 < baseStart_7851553 := by decide
  rcases family_descends (prefixWord ++ tailWord_7851553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7851573 : List Nat := [1, 3, 3, 1, 1, 3, 2, 2, 1, 3, 3]
def baseStart_7851573 : Nat := 118140960795 + 7851573 * 2 ^ 59
def prefixEnd_7851573 : Nat := 4983230072969 + 3 ^ 40 * 7851573 * 2
def baseEnd_7851573 : Nat := 4031630842863914418228779

theorem tailTrace_7851573 : CollatzResearch.WordTrace tailWord_7851573 prefixEnd_7851573 4031630842863914418228779 := by
  unfold tailWord_7851573
  simp only [CollatzResearch.WordTrace]
  refine ⟨286370393584099437755671373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190913595722732958503780915 286370393584099437755671373)
  ·
    refine ⟨107388897594037289158376765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 286370393584099437755671373 107388897594037289158376765)
    ·
      refine ⟨40270836597763983434391287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107388897594037289158376765 40270836597763983434391287)
      ·
        refine ⟨60406254896645975151586931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40270836597763983434391287 60406254896645975151586931)
        ·
          refine ⟨90609382344968962727380397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60406254896645975151586931 90609382344968962727380397)
          ·
            refine ⟨33978518379363361022767649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90609382344968962727380397 33978518379363361022767649)
            ·
              refine ⟨25483888784522520767075737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33978518379363361022767649 25483888784522520767075737)
              ·
                refine ⟨19112916588391890575306803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25483888784522520767075737 19112916588391890575306803)
                ·
                  refine ⟨28669374882587835862960205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19112916588391890575306803 28669374882587835862960205)
                  ·
                    refine ⟨10751015580970438448610077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28669374882587835862960205 10751015580970438448610077)
                    ·
                      refine ⟨4031630842863914418228779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10751015580970438448610077 4031630842863914418228779)
                      ·
                        rfl

theorem cell23_7851573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 2, 1, 3, 3].length) (baseStart_7851573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7851573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7851573 prefixEnd_7851573 := by exact prefixLift 7851573
  have htrace : WordTrace (prefixWord ++ tailWord_7851573) baseStart_7851573 baseEnd_7851573 := by
    simpa [prefixWord, tailWord_7851573, baseEnd_7851573] using wordTrace_append hprefix tailTrace_7851573
  have hstable : (prefixWord ++ tailWord_7851573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7851573).length < 2 ^ (prefixWord ++ tailWord_7851573).sum := by decide
  have hdescent : baseEnd_7851573 < baseStart_7851573 := by decide
  rcases family_descends (prefixWord ++ tailWord_7851573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7851574 : List Nat := [5, 1, 2, 1, 3, 2, 2, 1, 1, 1, 4]
def baseStart_7851574 : Nat := 118140960795 + 7851574 * 2 ^ 59
def prefixEnd_7851574 : Nat := 4983230072969 + 3 ^ 40 * 7851574 * 2
def baseEnd_7851574 : Nat := 4031631356344568914316275

theorem tailTrace_7851574 : CollatzResearch.WordTrace tailWord_7851574 prefixEnd_7851574 4031631356344568914316275 := by
  unfold tailWord_7851574
  simp only [CollatzResearch.WordTrace]
  refine ⟨17898151878568488432903611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 190913620038063876617638517 17898151878568488432903611)
  ·
    refine ⟨26847227817852732649355417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17898151878568488432903611 26847227817852732649355417)
    ·
      refine ⟨20135420863389549487016563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26847227817852732649355417 20135420863389549487016563)
      ·
        refine ⟨30203131295084324230524845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20135420863389549487016563 30203131295084324230524845)
        ·
          refine ⟨11326174235656621586446817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30203131295084324230524845 11326174235656621586446817)
          ·
            refine ⟨8494630676742466189835113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11326174235656621586446817 8494630676742466189835113)
            ·
              refine ⟨6370973007556849642376335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8494630676742466189835113 6370973007556849642376335)
              ·
                refine ⟨9556459511335274463564503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6370973007556849642376335 9556459511335274463564503)
                ·
                  refine ⟨14334689267002911695346755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9556459511335274463564503 14334689267002911695346755)
                  ·
                    refine ⟨21502033900504367543020133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14334689267002911695346755 21502033900504367543020133)
                    ·
                      refine ⟨4031631356344568914316275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21502033900504367543020133 4031631356344568914316275)
                      ·
                        rfl

theorem cell23_7851574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 2, 1, 1, 1, 4].length) (baseStart_7851574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7851574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7851574 prefixEnd_7851574 := by exact prefixLift 7851574
  have htrace : WordTrace (prefixWord ++ tailWord_7851574) baseStart_7851574 baseEnd_7851574 := by
    simpa [prefixWord, tailWord_7851574, baseEnd_7851574] using wordTrace_append hprefix tailTrace_7851574
  have hstable : (prefixWord ++ tailWord_7851574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7851574).length < 2 ^ (prefixWord ++ tailWord_7851574).sum := by decide
  have hdescent : baseEnd_7851574 < baseStart_7851574 := by decide
  rcases family_descends (prefixWord ++ tailWord_7851574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7851577 : List Nat := [1, 2, 1, 5, 1, 4, 2, 1, 1, 2, 3]
def baseStart_7851577 : Nat := 118140960795 + 7851577 * 2 ^ 59
def prefixEnd_7851577 : Nat := 4983230072969 + 3 ^ 40 * 7851577 * 2
def baseEnd_7851577 : Nat := 4031632896786532402578761

theorem tailTrace_7851577 : CollatzResearch.WordTrace tailWord_7851577 prefixEnd_7851577 4031632896786532402578761 := by
  unfold tailWord_7851577
  simp only [CollatzResearch.WordTrace]
  refine ⟨286370539476084946438816985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190913692984056630959211323 286370539476084946438816985)
  ·
    refine ⟨214777904607063709829112739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286370539476084946438816985 214777904607063709829112739)
    ·
      refine ⟨322166856910595564743669109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214777904607063709829112739 322166856910595564743669109)
      ·
        refine ⟨30203142835368334194718979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 322166856910595564743669109 30203142835368334194718979)
        ·
          refine ⟨45304714253052501292078469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30203142835368334194718979 45304714253052501292078469)
          ·
            refine ⟨8494633922447343992264713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45304714253052501292078469 8494633922447343992264713)
            ·
              refine ⟨6370975441835507994198535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8494633922447343992264713 6370975441835507994198535)
              ·
                refine ⟨9556463162753261991297803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6370975441835507994198535 9556463162753261991297803)
                ·
                  refine ⟨14334694744129892986946705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9556463162753261991297803 14334694744129892986946705)
                  ·
                    refine ⟨10751021058097419740210029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14334694744129892986946705 10751021058097419740210029)
                    ·
                      refine ⟨4031632896786532402578761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10751021058097419740210029 4031632896786532402578761)
                      ·
                        rfl

theorem cell23_7851577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 2, 1, 1, 2, 3].length) (baseStart_7851577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7851577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7851577 prefixEnd_7851577 := by exact prefixLift 7851577
  have htrace : WordTrace (prefixWord ++ tailWord_7851577) baseStart_7851577 baseEnd_7851577 := by
    simpa [prefixWord, tailWord_7851577, baseEnd_7851577] using wordTrace_append hprefix tailTrace_7851577
  have hstable : (prefixWord ++ tailWord_7851577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7851577).length < 2 ^ (prefixWord ++ tailWord_7851577).sum := by decide
  have hdescent : baseEnd_7851577 < baseStart_7851577 := by decide
  rcases family_descends (prefixWord ++ tailWord_7851577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7851607 : List Nat := [1, 1, 3, 2, 2, 4, 3, 1, 2, 1, 3]
def baseStart_7851607 : Nat := 118140960795 + 7851607 * 2 ^ 59
def prefixEnd_7851607 : Nat := 4983230072969 + 3 ^ 40 * 7851607 * 2
def baseEnd_7851607 : Nat := 4031648301206167285203623

theorem tailTrace_7851607 : CollatzResearch.WordTrace tailWord_7851607 prefixEnd_7851607 4031648301206167285203623 := by
  unfold tailWord_7851607
  simp only [CollatzResearch.WordTrace]
  refine ⟨286371633665976261562409075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190914422443984174374939383 286371633665976261562409075)
  ·
    refine ⟨429557450498964392343613613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286371633665976261562409075 429557450498964392343613613)
    ·
      refine ⟨161084043937111647128855105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 429557450498964392343613613 161084043937111647128855105)
      ·
        refine ⟨120813032952833735346641329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161084043937111647128855105 120813032952833735346641329)
        ·
          refine ⟨90609774714625301509980997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120813032952833735346641329 90609774714625301509980997)
          ·
            refine ⟨16989332758992244033121437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90609774714625301509980997 16989332758992244033121437)
            ·
              refine ⟨6370999784622091512420539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16989332758992244033121437 6370999784622091512420539)
              ·
                refine ⟨9556499676933137268630809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6370999784622091512420539 9556499676933137268630809)
                ·
                  refine ⟨7167374757699852951473107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9556499676933137268630809 7167374757699852951473107)
                  ·
                    refine ⟨10751062136549779427209661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7167374757699852951473107 10751062136549779427209661)
                    ·
                      refine ⟨4031648301206167285203623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10751062136549779427209661 4031648301206167285203623)
                      ·
                        rfl

theorem cell23_7851607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 3, 1, 2, 1, 3].length) (baseStart_7851607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7851607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7851607 prefixEnd_7851607 := by exact prefixLift 7851607
  have htrace : WordTrace (prefixWord ++ tailWord_7851607) baseStart_7851607 baseEnd_7851607 := by
    simpa [prefixWord, tailWord_7851607, baseEnd_7851607] using wordTrace_append hprefix tailTrace_7851607
  have hstable : (prefixWord ++ tailWord_7851607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7851607).length < 2 ^ (prefixWord ++ tailWord_7851607).sum := by decide
  have hdescent : baseEnd_7851607 < baseStart_7851607 := by decide
  rcases family_descends (prefixWord ++ tailWord_7851607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7851616 : List Nat := [2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 5]
def baseStart_7851616 : Nat := 118140960795 + 7851616 * 2 ^ 59
def prefixEnd_7851616 : Nat := 4983230072969 + 3 ^ 40 * 7851616 * 2
def baseEnd_7851616 : Nat := 4031652922532057749991081

theorem tailTrace_7851616 : CollatzResearch.WordTrace tailWord_7851616 prefixEnd_7851616 4031652922532057749991081 := by
  unfold tailWord_7851616
  simp only [CollatzResearch.WordTrace]
  refine ⟨143185980961471828049743351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190914641281962437399657801 143185980961471828049743351)
  ·
    refine ⟨214778971442207742074615027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143185980961471828049743351 214778971442207742074615027)
    ·
      refine ⟨322168457163311613111922541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214778971442207742074615027 322168457163311613111922541)
      ·
        refine ⟨120813171436241854916970953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 322168457163311613111922541 120813171436241854916970953)
        ·
          refine ⟨90609878577181391187728215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120813171436241854916970953 90609878577181391187728215)
          ·
            refine ⟨135914817865772086781592323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90609878577181391187728215 135914817865772086781592323)
            ·
              refine ⟨203872226798658130172388485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135914817865772086781592323 203872226798658130172388485)
              ·
                refine ⟨38226042524748399407322841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 203872226798658130172388485 38226042524748399407322841)
                ·
                  refine ⟨28669531893561299555492131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38226042524748399407322841 28669531893561299555492131)
                  ·
                    refine ⟨43004297840341949333238197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28669531893561299555492131 43004297840341949333238197)
                    ·
                      refine ⟨4031652922532057749991081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43004297840341949333238197 4031652922532057749991081)
                      ·
                        rfl

theorem cell23_7851616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 5].length) (baseStart_7851616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7851616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7851616 prefixEnd_7851616 := by exact prefixLift 7851616
  have htrace : WordTrace (prefixWord ++ tailWord_7851616) baseStart_7851616 baseEnd_7851616 := by
    simpa [prefixWord, tailWord_7851616, baseEnd_7851616] using wordTrace_append hprefix tailTrace_7851616
  have hstable : (prefixWord ++ tailWord_7851616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7851616).length < 2 ^ (prefixWord ++ tailWord_7851616).sum := by decide
  have hdescent : baseEnd_7851616 < baseStart_7851616 := by decide
  rcases family_descends (prefixWord ++ tailWord_7851616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7851673 : List Nat := [1, 2, 1, 2, 1, 2, 2, 1, 4, 5, 2]
def baseStart_7851673 : Nat := 118140960795 + 7851673 * 2 ^ 59
def prefixEnd_7851673 : Nat := 4983230072969 + 3 ^ 40 * 7851673 * 2
def baseEnd_7851673 : Nat := 4031682190929364026978319

theorem tailTrace_7851673 : CollatzResearch.WordTrace tailWord_7851673 prefixEnd_7851673 4031682190929364026978319 := by
  unfold tailWord_7851673
  simp only [CollatzResearch.WordTrace]
  refine ⟨286374040883737154834311673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190916027255824769889541115 286374040883737154834311673)
  ·
    refine ⟨214780530662802866125733755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286374040883737154834311673 214780530662802866125733755)
    ·
      refine ⟨322170795994204299188600633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214780530662802866125733755 322170795994204299188600633)
      ·
        refine ⟨241628096995653224391450475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 322170795994204299188600633 241628096995653224391450475)
        ·
          refine ⟨362442145493479836587175713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241628096995653224391450475 362442145493479836587175713)
          ·
            refine ⟨271831609120109877440381785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 362442145493479836587175713 271831609120109877440381785)
            ·
              refine ⟨203873706840082408080286339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 271831609120109877440381785 203873706840082408080286339)
              ·
                refine ⟨305810560260123612120429509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 203873706840082408080286339 305810560260123612120429509)
                ·
                  refine ⟨57339480048773177272580533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 305810560260123612120429509 57339480048773177272580533)
                  ·
                    refine ⟨5375576254572485369304425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57339480048773177272580533 5375576254572485369304425)
                    ·
                      refine ⟨4031682190929364026978319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5375576254572485369304425 4031682190929364026978319)
                      ·
                        rfl

theorem cell23_7851673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 4, 5, 2].length) (baseStart_7851673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7851673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7851673 prefixEnd_7851673 := by exact prefixLift 7851673
  have htrace : WordTrace (prefixWord ++ tailWord_7851673) baseStart_7851673 baseEnd_7851673 := by
    simpa [prefixWord, tailWord_7851673, baseEnd_7851673] using wordTrace_append hprefix tailTrace_7851673
  have hstable : (prefixWord ++ tailWord_7851673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7851673).length < 2 ^ (prefixWord ++ tailWord_7851673).sum := by decide
  have hdescent : baseEnd_7851673 < baseStart_7851673 := by decide
  rcases family_descends (prefixWord ++ tailWord_7851673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7851683 : List Nat := [1, 1, 1, 4, 1, 1, 6, 1, 2, 5]
def baseStart_7851683 : Nat := 118140960795 + 7851683 * 2 ^ 59
def prefixEnd_7851683 : Nat := 4983230072969 + 3 ^ 40 * 7851683 * 2
def baseEnd_7851683 : Nat := 1343895775245302995951091

theorem tailTrace_7851683 : CollatzResearch.WordTrace tailWord_7851683 prefixEnd_7851683 1343895775245302995951091 := by
  unfold tailWord_7851683
  simp only [CollatzResearch.WordTrace]
  refine ⟨286374405613700926542175703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190916270409133951028117135 286374405613700926542175703)
  ·
    refine ⟨429561608420551389813263555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286374405613700926542175703 429561608420551389813263555)
    ·
      refine ⟨644342412630827084719895333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 429561608420551389813263555 644342412630827084719895333)
      ·
        refine ⟨120814202368280078384980375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 644342412630827084719895333 120814202368280078384980375)
        ·
          refine ⟨181221303552420117577470563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120814202368280078384980375 181221303552420117577470563)
          ·
            refine ⟨271831955328630176366205845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181221303552420117577470563 271831955328630176366205845)
            ·
              refine ⟨12742122906029539517165899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 271831955328630176366205845 12742122906029539517165899)
              ·
                refine ⟨19113184359044309275748849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12742122906029539517165899 19113184359044309275748849)
                ·
                  refine ⟨14334888269283231956811637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19113184359044309275748849 14334888269283231956811637)
                  ·
                    refine ⟨1343895775245302995951091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14334888269283231956811637 1343895775245302995951091)
                    ·
                      rfl

theorem cell23_7851683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 6, 1, 2, 5].length) (baseStart_7851683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7851683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7851683 prefixEnd_7851683 := by exact prefixLift 7851683
  have htrace : WordTrace (prefixWord ++ tailWord_7851683) baseStart_7851683 baseEnd_7851683 := by
    simpa [prefixWord, tailWord_7851683, baseEnd_7851683] using wordTrace_append hprefix tailTrace_7851683
  have hstable : (prefixWord ++ tailWord_7851683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7851683).length < 2 ^ (prefixWord ++ tailWord_7851683).sum := by decide
  have hdescent : baseEnd_7851683 < baseStart_7851683 := by decide
  rcases family_descends (prefixWord ++ tailWord_7851683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7851693 : List Nat := [1, 5, 2, 1, 1, 1, 1, 1, 3, 2, 5]
def baseStart_7851693 : Nat := 118140960795 + 7851693 * 2 ^ 59
def prefixEnd_7851693 : Nat := 4983230072969 + 3 ^ 40 * 7851693 * 2
def baseEnd_7851693 : Nat := 4031692460542453948728227

theorem tailTrace_7851693 : CollatzResearch.WordTrace tailWord_7851693 prefixEnd_7851693 4031692460542453948728227 := by
  unfold tailWord_7851693
  simp only [CollatzResearch.WordTrace]
  refine ⟨286374770343664698250039733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190916513562443132166693155 286374770343664698250039733)
  ·
    refine ⟨26847634719718565460941225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 286374770343664698250039733 26847634719718565460941225)
    ·
      refine ⟨20135726039788924095705919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26847634719718565460941225 20135726039788924095705919)
      ·
        refine ⟨30203589059683386143558879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20135726039788924095705919 30203589059683386143558879)
        ·
          refine ⟨45305383589525079215338319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30203589059683386143558879 45305383589525079215338319)
          ·
            refine ⟨67958075384287618823007479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45305383589525079215338319 67958075384287618823007479)
            ·
              refine ⟨101937113076431428234511219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67958075384287618823007479 101937113076431428234511219)
              ·
                refine ⟨152905669614647142351766829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101937113076431428234511219 152905669614647142351766829)
                ·
                  refine ⟨57339626105492678381912561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 152905669614647142351766829 57339626105492678381912561)
                  ·
                    refine ⟨43004719579119508786434421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57339626105492678381912561 43004719579119508786434421)
                    ·
                      refine ⟨4031692460542453948728227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43004719579119508786434421 4031692460542453948728227)
                      ·
                        rfl

theorem cell23_7851693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_7851693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7851693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7851693 prefixEnd_7851693 := by exact prefixLift 7851693
  have htrace : WordTrace (prefixWord ++ tailWord_7851693) baseStart_7851693 baseEnd_7851693 := by
    simpa [prefixWord, tailWord_7851693, baseEnd_7851693] using wordTrace_append hprefix tailTrace_7851693
  have hstable : (prefixWord ++ tailWord_7851693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7851693).length < 2 ^ (prefixWord ++ tailWord_7851693).sum := by decide
  have hdescent : baseEnd_7851693 < baseStart_7851693 := by decide
  rcases family_descends (prefixWord ++ tailWord_7851693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7851720 : List Nat := [2, 1, 3, 1, 2, 2, 3, 1, 2, 4, 2]
def baseStart_7851720 : Nat := 118140960795 + 7851720 * 2 ^ 59
def prefixEnd_7851720 : Nat := 4983230072969 + 3 ^ 40 * 7851720 * 2
def baseEnd_7851720 : Nat := 4031706324520125343090603

theorem tailTrace_7851720 : CollatzResearch.WordTrace tailWord_7851720 prefixEnd_7851720 4031706324520125343090603 := by
  unfold tailWord_7851720
  simp only [CollatzResearch.WordTrace]
  refine ⟨143187877557283440930636307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190917170076377921240848409 143187877557283440930636307)
  ·
    refine ⟨214781816335925161395954461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143187877557283440930636307 214781816335925161395954461)
    ·
      refine ⟨80543181125971935523482923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214781816335925161395954461 80543181125971935523482923)
      ·
        refine ⟨120814771688957903285224385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80543181125971935523482923 120814771688957903285224385)
        ·
          refine ⟨90611078766718427463918289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120814771688957903285224385 90611078766718427463918289)
          ·
            refine ⟨67958309075038820597938717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90611078766718427463918289 67958309075038820597938717)
            ·
              refine ⟨25484365903139557724227019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67958309075038820597938717 25484365903139557724227019)
              ·
                refine ⟨38226548854709336586340529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25484365903139557724227019 38226548854709336586340529)
                ·
                  refine ⟨28669911641032002439755397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38226548854709336586340529 28669911641032002439755397)
                  ·
                    refine ⟨5375608432693500457454137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28669911641032002439755397 5375608432693500457454137)
                    ·
                      refine ⟨4031706324520125343090603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5375608432693500457454137 4031706324520125343090603)
                      ·
                        rfl

theorem cell23_7851720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 1, 2, 4, 2].length) (baseStart_7851720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7851720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7851720 prefixEnd_7851720 := by exact prefixLift 7851720
  have htrace : WordTrace (prefixWord ++ tailWord_7851720) baseStart_7851720 baseEnd_7851720 := by
    simpa [prefixWord, tailWord_7851720, baseEnd_7851720] using wordTrace_append hprefix tailTrace_7851720
  have hstable : (prefixWord ++ tailWord_7851720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7851720).length < 2 ^ (prefixWord ++ tailWord_7851720).sum := by decide
  have hdescent : baseEnd_7851720 < baseStart_7851720 := by decide
  rcases family_descends (prefixWord ++ tailWord_7851720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7851723 : List Nat := [1, 1, 1, 1, 3, 2, 1, 4, 4, 2, 3]
def baseStart_7851723 : Nat := 118140960795 + 7851723 * 2 ^ 59
def prefixEnd_7851723 : Nat := 4983230072969 + 3 ^ 40 * 7851723 * 2
def baseEnd_7851723 : Nat := 4031707864962088831353089

theorem tailTrace_7851723 : CollatzResearch.WordTrace tailWord_7851723 prefixEnd_7851723 4031707864962088831353089 := by
  unfold tailWord_7851723
  simp only [CollatzResearch.WordTrace]
  refine ⟨286375864533556013373631823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190917243022370675582421215 286375864533556013373631823)
  ·
    refine ⟨429563796800334020060447735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286375864533556013373631823 429563796800334020060447735)
    ·
      refine ⟨644345695200501030090671603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 429563796800334020060447735 644345695200501030090671603)
      ·
        refine ⟨966518542800751545136007405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 644345695200501030090671603 966518542800751545136007405)
        ·
          refine ⟨362444453550281829426002777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 966518542800751545136007405 362444453550281829426002777)
          ·
            refine ⟨271833340162711372069502083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 362444453550281829426002777 271833340162711372069502083)
            ·
              refine ⟨407750010244067058104253125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 271833340162711372069502083 407750010244067058104253125)
              ·
                refine ⟨76453126920762573394547461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 407750010244067058104253125 76453126920762573394547461)
                ·
                  refine ⟨14334961297642982511477649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76453126920762573394547461 14334961297642982511477649)
                  ·
                    refine ⟨10751220973232236883608237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14334961297642982511477649 10751220973232236883608237)
                    ·
                      refine ⟨4031707864962088831353089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10751220973232236883608237 4031707864962088831353089)
                      ·
                        rfl

theorem cell23_7851723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 4, 4, 2, 3].length) (baseStart_7851723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7851723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7851723 prefixEnd_7851723 := by exact prefixLift 7851723
  have htrace : WordTrace (prefixWord ++ tailWord_7851723) baseStart_7851723 baseEnd_7851723 := by
    simpa [prefixWord, tailWord_7851723, baseEnd_7851723] using wordTrace_append hprefix tailTrace_7851723
  have hstable : (prefixWord ++ tailWord_7851723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7851723).length < 2 ^ (prefixWord ++ tailWord_7851723).sum := by decide
  have hdescent : baseEnd_7851723 < baseStart_7851723 := by decide
  rcases family_descends (prefixWord ++ tailWord_7851723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7851730 : List Nat := [3, 2, 2, 2, 2, 1, 1, 1, 5, 4]
def baseStart_7851730 : Nat := 118140960795 + 7851730 * 2 ^ 59
def prefixEnd_7851730 : Nat := 4983230072969 + 3 ^ 40 * 7851730 * 2
def baseEnd_7851730 : Nat := 1343903819775556767988519

theorem tailTrace_7851730 : CollatzResearch.WordTrace tailWord_7851730 prefixEnd_7851730 1343903819775556767988519 := by
  unfold tailWord_7851730
  simp only [CollatzResearch.WordTrace]
  refine ⟨71594029961132663392284161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190917413229687102379424429 71594029961132663392284161)
  ·
    refine ⟨53695522470849497544213121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71594029961132663392284161 53695522470849497544213121)
    ·
      refine ⟨40271641853137123158159841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53695522470849497544213121 40271641853137123158159841)
      ·
        refine ⟨30203731389852842368619881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40271641853137123158159841 30203731389852842368619881)
        ·
          refine ⟨22652798542389631776464911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30203731389852842368619881 22652798542389631776464911)
          ·
            refine ⟨33979197813584447664697367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22652798542389631776464911 33979197813584447664697367)
            ·
              refine ⟨50968796720376671497046051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33979197813584447664697367 50968796720376671497046051)
              ·
                refine ⟨76453195080565007245569077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50968796720376671497046051 76453195080565007245569077)
                ·
                  refine ⟨7167487038802969429272101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 76453195080565007245569077 7167487038802969429272101)
                  ·
                    refine ⟨1343903819775556767988519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7167487038802969429272101 1343903819775556767988519)
                    ·
                      rfl

theorem cell23_7851730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 1, 5, 4].length) (baseStart_7851730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7851730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7851730 prefixEnd_7851730 := by exact prefixLift 7851730
  have htrace : WordTrace (prefixWord ++ tailWord_7851730) baseStart_7851730 baseEnd_7851730 := by
    simpa [prefixWord, tailWord_7851730, baseEnd_7851730] using wordTrace_append hprefix tailTrace_7851730
  have hstable : (prefixWord ++ tailWord_7851730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7851730).length < 2 ^ (prefixWord ++ tailWord_7851730).sum := by decide
  have hdescent : baseEnd_7851730 < baseStart_7851730 := by decide
  rcases family_descends (prefixWord ++ tailWord_7851730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7851764 : List Nat := [2, 6, 1, 1, 1, 1, 1, 3, 3, 4]
def baseStart_7851764 : Nat := 118140960795 + 7851764 * 2 ^ 59
def prefixEnd_7851764 : Nat := 4983230072969 + 3 ^ 40 * 7851764 * 2
def baseEnd_7851764 : Nat := 1343909639222974390313467

theorem tailTrace_7851764 : CollatzResearch.WordTrace tailWord_7851764 prefixEnd_7851764 1343909639222974390313467 := by
  unfold tailWord_7851764
  simp only [CollatzResearch.WordTrace]
  refine ⟨143188679963203738687937173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190918239950938318250582897 143188679963203738687937173)
  ·
    refine ⟨6711969373275175250997055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 143188679963203738687937173 6711969373275175250997055)
    ·
      refine ⟨10067954059912762876495583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6711969373275175250997055 10067954059912762876495583)
      ·
        refine ⟨15101931089869144314743375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10067954059912762876495583 15101931089869144314743375)
        ·
          refine ⟨22652896634803716472115063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15101931089869144314743375 22652896634803716472115063)
          ·
            refine ⟨33979344952205574708172595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22652896634803716472115063 33979344952205574708172595)
            ·
              refine ⟨50969017428308362062258893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33979344952205574708172595 50969017428308362062258893)
              ·
                refine ⟨19113381535615635773347085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50969017428308362062258893 19113381535615635773347085)
                ·
                  refine ⟨7167518075855863415005157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19113381535615635773347085 7167518075855863415005157)
                  ·
                    refine ⟨1343909639222974390313467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7167518075855863415005157 1343909639222974390313467)
                    ·
                      rfl

theorem cell23_7851764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_7851764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7851764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7851764 prefixEnd_7851764 := by exact prefixLift 7851764
  have htrace : WordTrace (prefixWord ++ tailWord_7851764) baseStart_7851764 baseEnd_7851764 := by
    simpa [prefixWord, tailWord_7851764, baseEnd_7851764] using wordTrace_append hprefix tailTrace_7851764
  have hstable : (prefixWord ++ tailWord_7851764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7851764).length < 2 ^ (prefixWord ++ tailWord_7851764).sum := by decide
  have hdescent : baseEnd_7851764 < baseStart_7851764 := by decide
  rcases family_descends (prefixWord ++ tailWord_7851764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7851773 : List Nat := [1, 4, 1, 1, 1, 1, 2, 4, 3, 5]
def baseStart_7851773 : Nat := 118140960795 + 7851773 * 2 ^ 59
def prefixEnd_7851773 : Nat := 4983230072969 + 3 ^ 40 * 7851773 * 2
def baseEnd_7851773 : Nat := 1343911179664937878575953

theorem tailTrace_7851773 : CollatzResearch.WordTrace tailWord_7851773 prefixEnd_7851773 1343911179664937878575953 := by
  unfold tailWord_7851773
  simp only [CollatzResearch.WordTrace]
  refine ⟨286377688183374871912951973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190918458788916581275301315 286377688183374871912951973)
  ·
    refine ⟨53695816534382788483678495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 286377688183374871912951973 53695816534382788483678495)
    ·
      refine ⟨80543724801574182725517743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53695816534382788483678495 80543724801574182725517743)
      ·
        refine ⟨120815587202361274088276615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80543724801574182725517743 120815587202361274088276615)
        ·
          refine ⟨181223380803541911132414923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120815587202361274088276615 181223380803541911132414923)
          ·
            refine ⟨271835071205312866698622385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181223380803541911132414923 271835071205312866698622385)
            ·
              refine ⟨203876303403984650023966789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 271835071205312866698622385 203876303403984650023966789)
              ·
                refine ⟨38226806888247121879493773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 203876303403984650023966789 38226806888247121879493773)
                ·
                  refine ⟨14335052583092670704810165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38226806888247121879493773 14335052583092670704810165)
                  ·
                    refine ⟨1343911179664937878575953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14335052583092670704810165 1343911179664937878575953)
                    ·
                      rfl

theorem cell23_7851773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 4, 3, 5].length) (baseStart_7851773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7851773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7851773 prefixEnd_7851773 := by exact prefixLift 7851773
  have htrace : WordTrace (prefixWord ++ tailWord_7851773) baseStart_7851773 baseEnd_7851773 := by
    simpa [prefixWord, tailWord_7851773, baseEnd_7851773] using wordTrace_append hprefix tailTrace_7851773
  have hstable : (prefixWord ++ tailWord_7851773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7851773).length < 2 ^ (prefixWord ++ tailWord_7851773).sum := by decide
  have hdescent : baseEnd_7851773 < baseStart_7851773 := by decide
  rcases family_descends (prefixWord ++ tailWord_7851773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7851790 : List Nat := [4, 1, 1, 2, 1, 1, 3, 4, 1, 5]
def baseStart_7851790 : Nat := 118140960795 + 7851790 * 2 ^ 59
def prefixEnd_7851790 : Nat := 4983230072969 + 3 ^ 40 * 7851790 * 2
def baseEnd_7851790 : Nat := 1343914089388646689738427

theorem tailTrace_7851790 : CollatzResearch.WordTrace tailWord_7851790 prefixEnd_7851790 1343914089388646689738427 := by
  unfold tailWord_7851790
  simp only [CollatzResearch.WordTrace]
  refine ⟨35797288528039160477040103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 190918872149542189210880549 35797288528039160477040103)
  ·
    refine ⟨53695932792058740715560155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35797288528039160477040103 53695932792058740715560155)
    ·
      refine ⟨80543899188088111073340233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53695932792058740715560155 80543899188088111073340233)
      ·
        refine ⟨60407924391066083305005175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80543899188088111073340233 60407924391066083305005175)
        ·
          refine ⟨90611886586599124957507763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60407924391066083305005175 90611886586599124957507763)
          ·
            refine ⟨135917829879898687436261645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90611886586599124957507763 135917829879898687436261645)
            ·
              refine ⟨50969186204962007788598117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135917829879898687436261645 50969186204962007788598117)
              ·
                refine ⟨9556722413430376460362147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50969186204962007788598117 9556722413430376460362147)
                ·
                  refine ⟨14335083620145564690543221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9556722413430376460362147 14335083620145564690543221)
                  ·
                    refine ⟨1343914089388646689738427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14335083620145564690543221 1343914089388646689738427)
                    ·
                      rfl

theorem cell23_7851790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 4, 1, 5].length) (baseStart_7851790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7851790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7851790 prefixEnd_7851790 := by exact prefixLift 7851790
  have htrace : WordTrace (prefixWord ++ tailWord_7851790) baseStart_7851790 baseEnd_7851790 := by
    simpa [prefixWord, tailWord_7851790, baseEnd_7851790] using wordTrace_append hprefix tailTrace_7851790
  have hstable : (prefixWord ++ tailWord_7851790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7851790).length < 2 ^ (prefixWord ++ tailWord_7851790).sum := by decide
  have hdescent : baseEnd_7851790 < baseStart_7851790 := by decide
  rcases family_descends (prefixWord ++ tailWord_7851790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7851820 : List Nat := [2, 2, 1, 1, 1, 5, 2, 1, 4, 4]
def baseStart_7851820 : Nat := 118140960795 + 7851820 * 2 ^ 59
def prefixEnd_7851820 : Nat := 4983230072969 + 3 ^ 40 * 7851820 * 2
def baseEnd_7851820 : Nat := 1343919224195191650613381

theorem tailTrace_7851820 : CollatzResearch.WordTrace tailWord_7851820 prefixEnd_7851820 1343919224195191650613381 := by
  unfold tailWord_7851820
  simp only [CollatzResearch.WordTrace]
  refine ⟨143189701207102299469956457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190919601609469732626608609 143189701207102299469956457)
  ·
    refine ⟨107392275905326724602467343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143189701207102299469956457 107392275905326724602467343)
    ·
      refine ⟨161088413857990086903701015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107392275905326724602467343 161088413857990086903701015)
      ·
        refine ⟨241632620786985130355551523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161088413857990086903701015 241632620786985130355551523)
        ·
          refine ⟨362448931180477695533327285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241632620786985130355551523 362448931180477695533327285)
          ·
            refine ⟨33979587298169783956249433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 362448931180477695533327285 33979587298169783956249433)
            ·
              refine ⟨25484690473627337967187075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33979587298169783956249433 25484690473627337967187075)
              ·
                refine ⟨38227035710441006950780613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25484690473627337967187075 38227035710441006950780613)
                ·
                  refine ⟨7167569195707688803271365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38227035710441006950780613 7167569195707688803271365)
                  ·
                    refine ⟨1343919224195191650613381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7167569195707688803271365 1343919224195191650613381)
                    ·
                      rfl

theorem cell23_7851820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 4].length) (baseStart_7851820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7851820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7851820 prefixEnd_7851820 := by exact prefixLift 7851820
  have htrace : WordTrace (prefixWord ++ tailWord_7851820) baseStart_7851820 baseEnd_7851820 := by
    simpa [prefixWord, tailWord_7851820, baseEnd_7851820] using wordTrace_append hprefix tailTrace_7851820
  have hstable : (prefixWord ++ tailWord_7851820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7851820).length < 2 ^ (prefixWord ++ tailWord_7851820).sum := by decide
  have hdescent : baseEnd_7851820 < baseStart_7851820 := by decide
  rcases family_descends (prefixWord ++ tailWord_7851820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7851823 : List Nat := [1, 1, 2, 1, 2, 1, 2, 4, 3, 2, 4]
def baseStart_7851823 : Nat := 118140960795 + 7851823 * 2 ^ 59
def prefixEnd_7851823 : Nat := 4983230072969 + 3 ^ 40 * 7851823 * 2
def baseEnd_7851823 : Nat := 4031759213027538440102629

theorem tailTrace_7851823 : CollatzResearch.WordTrace tailWord_7851823 prefixEnd_7851823 4031759213027538440102629 := by
  unfold tailWord_7851823
  simp only [CollatzResearch.WordTrace]
  refine ⟨286379511833193730452272123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190919674555462486968181415 286379511833193730452272123)
  ·
    refine ⟨429569267749790595678408185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286379511833193730452272123 429569267749790595678408185)
    ·
      refine ⟨322176950812342946758806139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 429569267749790595678408185 322176950812342946758806139)
      ·
        refine ⟨483265426218514420138209209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322176950812342946758806139 483265426218514420138209209)
        ·
          refine ⟨362449069663885815103656907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 483265426218514420138209209 362449069663885815103656907)
          ·
            refine ⟨543673604495828722655485361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 362449069663885815103656907 543673604495828722655485361)
            ·
              refine ⟨407755203371871541991614021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 543673604495828722655485361 407755203371871541991614021)
              ·
                refine ⟨76454100632225914123427629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 407755203371871541991614021 76454100632225914123427629)
                ·
                  refine ⟨28670287737084717796285361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76454100632225914123427629 28670287737084717796285361)
                  ·
                    refine ⟨21502715802813538347214021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28670287737084717796285361 21502715802813538347214021)
                    ·
                      refine ⟨4031759213027538440102629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21502715802813538347214021 4031759213027538440102629)
                      ·
                        rfl

theorem cell23_7851823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 4, 3, 2, 4].length) (baseStart_7851823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7851823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7851823 prefixEnd_7851823 := by exact prefixLift 7851823
  have htrace : WordTrace (prefixWord ++ tailWord_7851823) baseStart_7851823 baseEnd_7851823 := by
    simpa [prefixWord, tailWord_7851823, baseEnd_7851823] using wordTrace_append hprefix tailTrace_7851823
  have hstable : (prefixWord ++ tailWord_7851823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7851823).length < 2 ^ (prefixWord ++ tailWord_7851823).sum := by decide
  have hdescent : baseEnd_7851823 < baseStart_7851823 := by decide
  rcases family_descends (prefixWord ++ tailWord_7851823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7851847 : List Nat := [1, 1, 4, 1, 2, 1, 5, 2, 1, 2, 3]
def baseStart_7851847 : Nat := 118140960795 + 7851847 * 2 ^ 59
def prefixEnd_7851847 : Nat := 4983230072969 + 3 ^ 40 * 7851847 * 2
def baseEnd_7851847 : Nat := 4031771536563246346202519

theorem tailTrace_7851847 : CollatzResearch.WordTrace tailWord_7851847 prefixEnd_7851847 4031771536563246346202519 := by
  unfold tailWord_7851847
  simp only [CollatzResearch.WordTrace]
  refine ⟨286380387185106782551145795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190920258123404521700763863 286380387185106782551145795)
  ·
    refine ⟨429570580777660173826718693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286380387185106782551145795 429570580777660173826718693)
    ·
      refine ⟨80544483895811282592509755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 429570580777660173826718693 80544483895811282592509755)
      ·
        refine ⟨120816725843716923888764633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80544483895811282592509755 120816725843716923888764633)
        ·
          refine ⟨90612544382787692916573475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120816725843716923888764633 90612544382787692916573475)
          ·
            refine ⟨135918816574181539374860213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90612544382787692916573475 135918816574181539374860213)
            ·
              refine ⟨12742389053829519316393145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 135918816574181539374860213 12742389053829519316393145)
              ·
                refine ⟨9556791790372139487294859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12742389053829519316393145 9556791790372139487294859)
                ·
                  refine ⟨14335187685558209230942289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9556791790372139487294859 14335187685558209230942289)
                  ·
                    refine ⟨10751390764168656923206717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14335187685558209230942289 10751390764168656923206717)
                    ·
                      refine ⟨4031771536563246346202519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10751390764168656923206717 4031771536563246346202519)
                      ·
                        rfl

theorem cell23_7851847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 5, 2, 1, 2, 3].length) (baseStart_7851847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7851847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7851847 prefixEnd_7851847 := by exact prefixLift 7851847
  have htrace : WordTrace (prefixWord ++ tailWord_7851847) baseStart_7851847 baseEnd_7851847 := by
    simpa [prefixWord, tailWord_7851847, baseEnd_7851847] using wordTrace_append hprefix tailTrace_7851847
  have hstable : (prefixWord ++ tailWord_7851847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7851847).length < 2 ^ (prefixWord ++ tailWord_7851847).sum := by decide
  have hdescent : baseEnd_7851847 < baseStart_7851847 := by decide
  rcases family_descends (prefixWord ++ tailWord_7851847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7851928 : List Nat := [2, 1, 2, 6, 1, 2, 1, 2, 2, 1, 3]
def baseStart_7851928 : Nat := 118140960795 + 7851928 * 2 ^ 59
def prefixEnd_7851928 : Nat := 4983230072969 + 3 ^ 40 * 7851928 * 2
def baseEnd_7851928 : Nat := 4031813128496260529289647

theorem tailTrace_7851928 : CollatzResearch.WordTrace tailWord_7851928 prefixEnd_7851928 4031813128496260529289647 := by
  unfold tailWord_7851928
  simp only [CollatzResearch.WordTrace]
  refine ⟨143191670748906666692422219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190922227665208888923229625 143191670748906666692422219)
  ·
    refine ⟨214787506123360000038633329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143191670748906666692422219 214787506123360000038633329)
    ·
      refine ⟨161090629592520000028974997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214787506123360000038633329 161090629592520000028974997)
      ·
        refine ⟨7551123262149375001358203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 161090629592520000028974997 7551123262149375001358203)
        ·
          refine ⟨11326684893224062502037305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7551123262149375001358203 11326684893224062502037305)
          ·
            refine ⟨8495013669918046876527979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11326684893224062502037305 8495013669918046876527979)
            ·
              refine ⟨12742520504877070314791969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8495013669918046876527979 12742520504877070314791969)
              ·
                refine ⟨9556890378657802736093977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12742520504877070314791969 9556890378657802736093977)
                ·
                  refine ⟨7167667783993352052070483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9556890378657802736093977 7167667783993352052070483)
                  ·
                    refine ⟨10751501675990028078105725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7167667783993352052070483 10751501675990028078105725)
                    ·
                      refine ⟨4031813128496260529289647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10751501675990028078105725 4031813128496260529289647)
                      ·
                        rfl

theorem cell23_7851928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_7851928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7851928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7851928 prefixEnd_7851928 := by exact prefixLift 7851928
  have htrace : WordTrace (prefixWord ++ tailWord_7851928) baseStart_7851928 baseEnd_7851928 := by
    simpa [prefixWord, tailWord_7851928, baseEnd_7851928] using wordTrace_append hprefix tailTrace_7851928
  have hstable : (prefixWord ++ tailWord_7851928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7851928).length < 2 ^ (prefixWord ++ tailWord_7851928).sum := by decide
  have hdescent : baseEnd_7851928 < baseStart_7851928 := by decide
  rcases family_descends (prefixWord ++ tailWord_7851928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7851940 : List Nat := [2, 3, 1, 2, 1, 3, 1, 3, 7]
def baseStart_7851940 : Nat := 118140960795 + 7851940 * 2 ^ 59
def prefixEnd_7851940 : Nat := 4983230072969 + 3 ^ 40 * 7851940 * 2
def baseEnd_7851940 : Nat := 447979921140457164704399

theorem tailTrace_7851940 : CollatzResearch.WordTrace tailWord_7851940 prefixEnd_7851940 447979921140457164704399 := by
  unfold tailWord_7851940
  simp only [CollatzResearch.WordTrace]
  refine ⟨143191889586884929717140637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190922519449179906289520849 143191889586884929717140637)
  ·
    refine ⟨53696958595081848643927739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143191889586884929717140637 53696958595081848643927739)
    ·
      refine ⟨80545437892622772965891609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53696958595081848643927739 80545437892622772965891609)
      ·
        refine ⟨60409078419467079724418707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80545437892622772965891609 60409078419467079724418707)
        ·
          refine ⟨90613617629200619586628061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60409078419467079724418707 90613617629200619586628061)
          ·
            refine ⟨33980106610950232344985523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90613617629200619586628061 33980106610950232344985523)
            ·
              refine ⟨50970159916425348517478285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33980106610950232344985523 50970159916425348517478285)
              ·
                refine ⟨19113809968659505694054357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50970159916425348517478285 19113809968659505694054357)
                ·
                  refine ⟨447979921140457164704399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19113809968659505694054357 447979921140457164704399)
                  ·
                    rfl

theorem cell23_7851940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 3, 7].length) (baseStart_7851940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7851940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7851940 prefixEnd_7851940 := by exact prefixLift 7851940
  have htrace : WordTrace (prefixWord ++ tailWord_7851940) baseStart_7851940 baseEnd_7851940 := by
    simpa [prefixWord, tailWord_7851940, baseEnd_7851940] using wordTrace_append hprefix tailTrace_7851940
  have hstable : (prefixWord ++ tailWord_7851940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7851940).length < 2 ^ (prefixWord ++ tailWord_7851940).sum := by decide
  have hdescent : baseEnd_7851940 < baseStart_7851940 := by decide
  rcases family_descends (prefixWord ++ tailWord_7851940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7851951 : List Nat := [1, 1, 2, 1, 2, 2, 7, 1, 2, 2, 2]
def baseStart_7851951 : Nat := 118140960795 + 7851951 * 2 ^ 59
def prefixEnd_7851951 : Nat := 4983230072969 + 3 ^ 40 * 7851951 * 2
def baseEnd_7851951 : Nat := 4031824938551313939302041

theorem tailTrace_7851951 : CollatzResearch.WordTrace tailWord_7851951 prefixEnd_7851951 4031824938551313939302041 := by
  unfold tailWord_7851951
  simp only [CollatzResearch.WordTrace]
  refine ⟨286384180376730008312931707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190922786917820005541954471 286384180376730008312931707)
  ·
    refine ⟨429576270565095012469397561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286384180376730008312931707 429576270565095012469397561)
    ·
      refine ⟨322182202923821259352048171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 429576270565095012469397561 322182202923821259352048171)
      ·
        refine ⟨483273304385731889028072257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322182202923821259352048171 483273304385731889028072257)
        ·
          refine ⟨362454978289298916771054193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 483273304385731889028072257 362454978289298916771054193)
          ·
            refine ⟨271841233716974187578290645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 362454978289298916771054193 271841233716974187578290645)
            ·
              refine ⟨6371278915241582521366187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 271841233716974187578290645 6371278915241582521366187)
              ·
                refine ⟨9556918372862373782049281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6371278915241582521366187 9556918372862373782049281)
                ·
                  refine ⟨7167688779646780336536961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9556918372862373782049281 7167688779646780336536961)
                  ·
                    refine ⟨5375766584735085252402721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7167688779646780336536961 5375766584735085252402721)
                    ·
                      refine ⟨4031824938551313939302041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5375766584735085252402721 4031824938551313939302041)
                      ·
                        rfl

theorem cell23_7851951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 7, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 7, 1, 2, 2, 2].length) (baseStart_7851951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7851951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7851951 prefixEnd_7851951 := by exact prefixLift 7851951
  have htrace : WordTrace (prefixWord ++ tailWord_7851951) baseStart_7851951 baseEnd_7851951 := by
    simpa [prefixWord, tailWord_7851951, baseEnd_7851951] using wordTrace_append hprefix tailTrace_7851951
  have hstable : (prefixWord ++ tailWord_7851951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7851951).length < 2 ^ (prefixWord ++ tailWord_7851951).sum := by decide
  have hdescent : baseEnd_7851951 < baseStart_7851951 := by decide
  rcases family_descends (prefixWord ++ tailWord_7851951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7852002 : List Nat := [3, 3, 3, 1, 2, 2, 2, 1, 2, 2, 2]
def baseStart_7852002 : Nat := 118140960795 + 7852002 * 2 ^ 59
def prefixEnd_7852002 : Nat := 4983230072969 + 3 ^ 40 * 7852002 * 2
def baseEnd_7852002 : Nat := 4031851126064693239764307

theorem tailTrace_7852002 : CollatzResearch.WordTrace tailWord_7852002 prefixEnd_7852002 4031851126064693239764307 := by
  unfold tailWord_7852002
  simp only [CollatzResearch.WordTrace]
  refine ⟨71596510124886311005759565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190924026999696829348692173 71596510124886311005759565)
  ·
    refine ⟨26848691296832366627159837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71596510124886311005759565 26848691296832366627159837)
    ·
      refine ⟨10068259236312137485184939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26848691296832366627159837 10068259236312137485184939)
      ·
        refine ⟨15102388854468206227777409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10068259236312137485184939 15102388854468206227777409)
        ·
          refine ⟨11326791640851154670833057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15102388854468206227777409 11326791640851154670833057)
          ·
            refine ⟨8495093730638366003124793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11326791640851154670833057 8495093730638366003124793)
            ·
              refine ⟨6371320297978774502343595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8495093730638366003124793 6371320297978774502343595)
              ·
                refine ⟨9556980446968161753515393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6371320297978774502343595 9556980446968161753515393)
                ·
                  refine ⟨7167735335226121315136545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9556980446968161753515393 7167735335226121315136545)
                  ·
                    refine ⟨5375801501419590986352409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7167735335226121315136545 5375801501419590986352409)
                    ·
                      refine ⟨4031851126064693239764307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5375801501419590986352409 4031851126064693239764307)
                      ·
                        rfl

theorem cell23_7852002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 2, 1, 2, 2, 2].length) (baseStart_7852002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7852002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7852002 prefixEnd_7852002 := by exact prefixLift 7852002
  have htrace : WordTrace (prefixWord ++ tailWord_7852002) baseStart_7852002 baseEnd_7852002 := by
    simpa [prefixWord, tailWord_7852002, baseEnd_7852002] using wordTrace_append hprefix tailTrace_7852002
  have hstable : (prefixWord ++ tailWord_7852002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7852002).length < 2 ^ (prefixWord ++ tailWord_7852002).sum := by decide
  have hdescent : baseEnd_7852002 < baseStart_7852002 := by decide
  rcases family_descends (prefixWord ++ tailWord_7852002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7852027 : List Nat := [1, 1, 1, 1, 1, 3, 5, 3, 2, 2, 3]
def baseStart_7852027 : Nat := 118140960795 + 7852027 * 2 ^ 59
def prefixEnd_7852027 : Nat := 4983230072969 + 3 ^ 40 * 7852027 * 2
def baseEnd_7852027 : Nat := 4031863963081055641951691

theorem tailTrace_7852027 : CollatzResearch.WordTrace tailWord_7852027 prefixEnd_7852027 4031863963081055641951691 := by
  unfold tailWord_7852027
  simp only [CollatzResearch.WordTrace]
  refine ⟨286386952324454673292698335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190924634882969782195132223 286386952324454673292698335)
  ·
    refine ⟨429580428486682009939047503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286386952324454673292698335 429580428486682009939047503)
    ·
      refine ⟨644370642730023014908571255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 429580428486682009939047503 644370642730023014908571255)
      ·
        refine ⟨966555964095034522362856883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 644370642730023014908571255 966555964095034522362856883)
        ·
          refine ⟨1449833946142551783544285325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 966555964095034522362856883 1449833946142551783544285325)
          ·
            refine ⟨543687729803456918829106997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1449833946142551783544285325 543687729803456918829106997)
            ·
              refine ⟨50970724669074086140228781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 543687729803456918829106997 50970724669074086140228781)
              ·
                refine ⟨19114021750902782302585793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50970724669074086140228781 19114021750902782302585793)
                ·
                  refine ⟨14335516313177086726939345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19114021750902782302585793 14335516313177086726939345)
                  ·
                    refine ⟨10751637234882815045204509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14335516313177086726939345 10751637234882815045204509)
                    ·
                      refine ⟨4031863963081055641951691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10751637234882815045204509 4031863963081055641951691)
                      ·
                        rfl

theorem cell23_7852027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 3, 2, 2, 3].length) (baseStart_7852027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7852027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7852027 prefixEnd_7852027 := by exact prefixLift 7852027
  have htrace : WordTrace (prefixWord ++ tailWord_7852027) baseStart_7852027 baseEnd_7852027 := by
    simpa [prefixWord, tailWord_7852027, baseEnd_7852027] using wordTrace_append hprefix tailTrace_7852027
  have hstable : (prefixWord ++ tailWord_7852027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7852027).length < 2 ^ (prefixWord ++ tailWord_7852027).sum := by decide
  have hdescent : baseEnd_7852027 < baseStart_7852027 := by decide
  rcases family_descends (prefixWord ++ tailWord_7852027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7852051 : List Nat := [1, 1, 1, 2, 1, 4, 6, 2, 1, 4]
def baseStart_7852051 : Nat := 118140960795 + 7852051 * 2 ^ 59
def prefixEnd_7852051 : Nat := 4983230072969 + 3 ^ 40 * 7852051 * 2
def baseEnd_7852051 : Nat := 1343958762205587849350527

theorem tailTrace_7852051 : CollatzResearch.WordTrace tailWord_7852051 prefixEnd_7852051 1343958762205587849350527 := by
  unfold tailWord_7852051
  simp only [CollatzResearch.WordTrace]
  refine ⟨286387827676367725391572007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190925218450911816927714671 286387827676367725391572007)
  ·
    refine ⟨429581741514551588087358011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286387827676367725391572007 429581741514551588087358011)
    ·
      refine ⟨644372612271827382131037017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 429581741514551588087358011 644372612271827382131037017)
      ·
        refine ⟨483279459203870536598277763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 644372612271827382131037017 483279459203870536598277763)
        ·
          refine ⟨724919188805805804897416645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 483279459203870536598277763 724919188805805804897416645)
          ·
            refine ⟨135922347901088588418265621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 724919188805805804897416645 135922347901088588418265621)
            ·
              refine ⟨6371360057863527582106201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 135922347901088588418265621 6371360057863527582106201)
              ·
                refine ⟨4778520043397645686579651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6371360057863527582106201 4778520043397645686579651)
                ·
                  refine ⟨7167780065096468529869477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4778520043397645686579651 7167780065096468529869477)
                  ·
                    refine ⟨1343958762205587849350527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7167780065096468529869477 1343958762205587849350527)
                    ·
                      rfl

theorem cell23_7852051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 6, 2, 1, 4].length) (baseStart_7852051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7852051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7852051 prefixEnd_7852051 := by exact prefixLift 7852051
  have htrace : WordTrace (prefixWord ++ tailWord_7852051) baseStart_7852051 baseEnd_7852051 := by
    simpa [prefixWord, tailWord_7852051, baseEnd_7852051] using wordTrace_append hprefix tailTrace_7852051
  have hstable : (prefixWord ++ tailWord_7852051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7852051).length < 2 ^ (prefixWord ++ tailWord_7852051).sum := by decide
  have hdescent : baseEnd_7852051 < baseStart_7852051 := by decide
  rcases family_descends (prefixWord ++ tailWord_7852051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7852107 : List Nat := [1, 1, 1, 1, 3, 1, 2, 5, 4, 4]
def baseStart_7852107 : Nat := 118140960795 + 7852107 * 2 ^ 59
def prefixEnd_7852107 : Nat := 4983230072969 + 3 ^ 40 * 7852107 * 2
def baseEnd_7852107 : Nat := 1343968347177805109650441

theorem tailTrace_7852107 : CollatzResearch.WordTrace tailWord_7852107 prefixEnd_7852107 1343968347177805109650441 := by
  unfold tailWord_7852107
  simp only [CollatzResearch.WordTrace]
  refine ⟨286389870164164846955610575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190926580109443231303740383 286389870164164846955610575)
  ·
    refine ⟨429584805246247270433415863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286389870164164846955610575 429584805246247270433415863)
    ·
      refine ⟨644377207869370905650123795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 429584805246247270433415863 644377207869370905650123795)
      ·
        refine ⟨966565811804056358475185693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 644377207869370905650123795 966565811804056358475185693)
        ·
          refine ⟨362462179426521134428194635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 966565811804056358475185693 362462179426521134428194635)
          ·
            refine ⟨543693269139781701642291953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 362462179426521134428194635 543693269139781701642291953)
            ·
              refine ⟨407769951854836276231718965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 543693269139781701642291953 407769951854836276231718965)
              ·
                refine ⟨38228432986390900896723653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 407769951854836276231718965 38228432986390900896723653)
                ·
                  refine ⟨7167831184948293918135685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38228432986390900896723653 7167831184948293918135685)
                  ·
                    refine ⟨1343968347177805109650441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7167831184948293918135685 1343968347177805109650441)
                    ·
                      rfl

theorem cell23_7852107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 5, 4, 4].length) (baseStart_7852107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7852107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7852107 prefixEnd_7852107 := by exact prefixLift 7852107
  have htrace : WordTrace (prefixWord ++ tailWord_7852107) baseStart_7852107 baseEnd_7852107 := by
    simpa [prefixWord, tailWord_7852107, baseEnd_7852107] using wordTrace_append hprefix tailTrace_7852107
  have hstable : (prefixWord ++ tailWord_7852107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7852107).length < 2 ^ (prefixWord ++ tailWord_7852107).sum := by decide
  have hdescent : baseEnd_7852107 < baseStart_7852107 := by decide
  rcases family_descends (prefixWord ++ tailWord_7852107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7852117 : List Nat := [1, 3, 2, 2, 1, 3, 1, 1, 3, 1, 5]
def baseStart_7852117 : Nat := 118140960795 + 7852117 * 2 ^ 59
def prefixEnd_7852117 : Nat := 4983230072969 + 3 ^ 40 * 7852117 * 2
def baseEnd_7852117 : Nat := 4031910176339960289826277

theorem tailTrace_7852117 : CollatzResearch.WordTrace tailWord_7852117 prefixEnd_7852117 4031910176339960289826277 := by
  unfold tailWord_7852117
  simp only [CollatzResearch.WordTrace]
  refine ⟨286390234894128618663474605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190926823262752412442316403 286390234894128618663474605)
  ·
    refine ⟨107396338085298231998802977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 286390234894128618663474605 107396338085298231998802977)
    ·
      refine ⟨80547253563973673999102233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107396338085298231998802977 80547253563973673999102233)
      ·
        refine ⟨60410440172980255499326675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80547253563973673999102233 60410440172980255499326675)
        ·
          refine ⟨90615660259470383248990013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60410440172980255499326675 90615660259470383248990013)
          ·
            refine ⟨33980872597301393718371255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90615660259470383248990013 33980872597301393718371255)
            ·
              refine ⟨50971308895952090577556883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33980872597301393718371255 50971308895952090577556883)
              ·
                refine ⟨76456963343928135866335325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50971308895952090577556883 76456963343928135866335325)
                ·
                  refine ⟨28671361253973050949875747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76456963343928135866335325 28671361253973050949875747)
                  ·
                    refine ⟨43007041880959576424813621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28671361253973050949875747 43007041880959576424813621)
                    ·
                      refine ⟨4031910176339960289826277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43007041880959576424813621 4031910176339960289826277)
                      ·
                        rfl

theorem cell23_7852117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 1, 3, 1, 5].length) (baseStart_7852117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7852117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7852117 prefixEnd_7852117 := by exact prefixLift 7852117
  have htrace : WordTrace (prefixWord ++ tailWord_7852117) baseStart_7852117 baseEnd_7852117 := by
    simpa [prefixWord, tailWord_7852117, baseEnd_7852117] using wordTrace_append hprefix tailTrace_7852117
  have hstable : (prefixWord ++ tailWord_7852117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7852117).length < 2 ^ (prefixWord ++ tailWord_7852117).sum := by decide
  have hdescent : baseEnd_7852117 < baseStart_7852117 := by decide
  rcases family_descends (prefixWord ++ tailWord_7852117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7852118 : List Nat := [5, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2]
def baseStart_7852118 : Nat := 118140960795 + 7852118 * 2 ^ 59
def prefixEnd_7852118 : Nat := 4983230072969 + 3 ^ 40 * 7852118 * 2
def baseEnd_7852118 : Nat := 4031910689820614785913773

theorem tailTrace_7852118 : CollatzResearch.WordTrace tailWord_7852118 prefixEnd_7852118 4031910689820614785913773 := by
  unfold tailWord_7852118
  simp only [CollatzResearch.WordTrace]
  refine ⟨17899391960445312239641313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 190926847578083330556174005 17899391960445312239641313)
  ·
    refine ⟨13424543970333984179730985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17899391960445312239641313 13424543970333984179730985)
    ·
      refine ⟨10068407977750488134798239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13424543970333984179730985 10068407977750488134798239)
      ·
        refine ⟨15102611966625732202197359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10068407977750488134798239 15102611966625732202197359)
        ·
          refine ⟨22653917949938598303296039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15102611966625732202197359 22653917949938598303296039)
          ·
            refine ⟨33980876924907897454944059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22653917949938598303296039 33980876924907897454944059)
            ·
              refine ⟨50971315387361846182416089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33980876924907897454944059 50971315387361846182416089)
              ·
                refine ⟨38228486540521384636812067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50971315387361846182416089 38228486540521384636812067)
                ·
                  refine ⟨57342729810782076955218101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38228486540521384636812067 57342729810782076955218101)
                  ·
                    refine ⟨5375880919760819714551697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57342729810782076955218101 5375880919760819714551697)
                    ·
                      refine ⟨4031910689820614785913773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5375880919760819714551697 4031910689820614785913773)
                      ·
                        rfl

theorem cell23_7852118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2].length) (baseStart_7852118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7852118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7852118 prefixEnd_7852118 := by exact prefixLift 7852118
  have htrace : WordTrace (prefixWord ++ tailWord_7852118) baseStart_7852118 baseEnd_7852118 := by
    simpa [prefixWord, tailWord_7852118, baseEnd_7852118] using wordTrace_append hprefix tailTrace_7852118
  have hstable : (prefixWord ++ tailWord_7852118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7852118).length < 2 ^ (prefixWord ++ tailWord_7852118).sum := by decide
  have hdescent : baseEnd_7852118 < baseStart_7852118 := by decide
  rcases family_descends (prefixWord ++ tailWord_7852118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7852124 : List Nat := [2, 2, 4, 1, 1, 2, 3, 1, 1, 6]
def baseStart_7852124 : Nat := 118140960795 + 7852124 * 2 ^ 59
def prefixEnd_7852124 : Nat := 4983230072969 + 3 ^ 40 * 7852124 * 2
def baseEnd_7852124 : Nat := 1343971256901513920812915

theorem tailTrace_7852124 : CollatzResearch.WordTrace tailWord_7852124 prefixEnd_7852124 1343971256901513920812915 := by
  unfold tailWord_7852124
  simp only [CollatzResearch.WordTrace]
  refine ⟨143195245102551629429489713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190926993470068839239319617 143195245102551629429489713)
  ·
    refine ⟨107396433826913722072117285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143195245102551629429489713 107396433826913722072117285)
    ·
      refine ⟨20136831342546322888521991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107396433826913722072117285 20136831342546322888521991)
      ·
        refine ⟨30205247013819484332782987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20136831342546322888521991 30205247013819484332782987)
        ·
          refine ⟨45307870520729226499174481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30205247013819484332782987 45307870520729226499174481)
          ·
            refine ⟨33980902890546919874380861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45307870520729226499174481 33980902890546919874380861)
            ·
              refine ⟨12742838583955094952892823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33980902890546919874380861 12742838583955094952892823)
              ·
                refine ⟨19114257875932642429339235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12742838583955094952892823 19114257875932642429339235)
                ·
                  refine ⟨28671386813898963644008853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19114257875932642429339235 28671386813898963644008853)
                  ·
                    refine ⟨1343971256901513920812915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28671386813898963644008853 1343971256901513920812915)
                    ·
                      rfl

theorem cell23_7852124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 3, 1, 1, 6].length) (baseStart_7852124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7852124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7852124 prefixEnd_7852124 := by exact prefixLift 7852124
  have htrace : WordTrace (prefixWord ++ tailWord_7852124) baseStart_7852124 baseEnd_7852124 := by
    simpa [prefixWord, tailWord_7852124, baseEnd_7852124] using wordTrace_append hprefix tailTrace_7852124
  have hstable : (prefixWord ++ tailWord_7852124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7852124).length < 2 ^ (prefixWord ++ tailWord_7852124).sum := by decide
  have hdescent : baseEnd_7852124 < baseStart_7852124 := by decide
  rcases family_descends (prefixWord ++ tailWord_7852124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7852127 : List Nat := [1, 1, 2, 3, 1, 1, 2, 5, 1, 2, 4]
def baseStart_7852127 : Nat := 118140960795 + 7852127 * 2 ^ 59
def prefixEnd_7852127 : Nat := 4983230072969 + 3 ^ 40 * 7852127 * 2
def baseEnd_7852127 : Nat := 4031915311146505250701231

theorem tailTrace_7852127 : CollatzResearch.WordTrace tailWord_7852127 prefixEnd_7852127 4031915311146505250701231 := by
  unfold tailWord_7852127
  simp only [CollatzResearch.WordTrace]
  refine ⟨286390599624092390371338635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190927066416061593580892423 286390599624092390371338635)
  ·
    refine ⟨429585899436138585557007953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286390599624092390371338635 429585899436138585557007953)
    ·
      refine ⟨322189424577103939167755965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 429585899436138585557007953 322189424577103939167755965)
      ·
        refine ⟨120821034216413977187908487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 322189424577103939167755965 120821034216413977187908487)
        ·
          refine ⟨181231551324620965781862731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120821034216413977187908487 181231551324620965781862731)
          ·
            refine ⟨271847326986931448672794097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181231551324620965781862731 271847326986931448672794097)
            ·
              refine ⟨203885495240198586504595573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 271847326986931448672794097 203885495240198586504595573)
              ·
                refine ⟨19114265178768617484805835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 203885495240198586504595573 19114265178768617484805835)
                ·
                  refine ⟨28671397768152926227208753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19114265178768617484805835 28671397768152926227208753)
                  ·
                    refine ⟨21503548326114694670406565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28671397768152926227208753 21503548326114694670406565)
                    ·
                      refine ⟨4031915311146505250701231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21503548326114694670406565 4031915311146505250701231)
                      ·
                        rfl

theorem cell23_7852127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 5, 1, 2, 4].length) (baseStart_7852127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7852127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7852127 prefixEnd_7852127 := by exact prefixLift 7852127
  have htrace : WordTrace (prefixWord ++ tailWord_7852127) baseStart_7852127 baseEnd_7852127 := by
    simpa [prefixWord, tailWord_7852127, baseEnd_7852127] using wordTrace_append hprefix tailTrace_7852127
  have hstable : (prefixWord ++ tailWord_7852127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7852127).length < 2 ^ (prefixWord ++ tailWord_7852127).sum := by decide
  have hdescent : baseEnd_7852127 < baseStart_7852127 := by decide
  rcases family_descends (prefixWord ++ tailWord_7852127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7852131 : List Nat := [1, 1, 1, 5, 1, 1, 4, 2, 3, 2, 2]
def baseStart_7852131 : Nat := 118140960795 + 7852131 * 2 ^ 59
def prefixEnd_7852131 : Nat := 4983230072969 + 3 ^ 40 * 7852131 * 2
def baseEnd_7852131 : Nat := 4031917365069123235051213

theorem tailTrace_7852131 : CollatzResearch.WordTrace tailWord_7852131 prefixEnd_7852131 4031917365069123235051213 := by
  unfold tailWord_7852131
  simp only [CollatzResearch.WordTrace]
  refine ⟨286390745516077899054484247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190927163677385266036322831 286390745516077899054484247)
  ·
    refine ⟨429586118274116848581726371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286390745516077899054484247 429586118274116848581726371)
    ·
      refine ⟨644379177411175272872589557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 429586118274116848581726371 644379177411175272872589557)
      ·
        refine ⟨60410547882297681831805271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 644379177411175272872589557 60410547882297681831805271)
        ·
          refine ⟨90615821823446522747707907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60410547882297681831805271 90615821823446522747707907)
          ·
            refine ⟨135923732735169784121561861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90615821823446522747707907 135923732735169784121561861)
            ·
              refine ⟨25485699887844334522792849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 135923732735169784121561861 25485699887844334522792849)
              ·
                refine ⟨19114274915883250892094637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25485699887844334522792849 19114274915883250892094637)
                ·
                  refine ⟨7167853093456219084535489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19114274915883250892094637 7167853093456219084535489)
                  ·
                    refine ⟨5375889820092164313401617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7167853093456219084535489 5375889820092164313401617)
                    ·
                      refine ⟨4031917365069123235051213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5375889820092164313401617 4031917365069123235051213)
                      ·
                        rfl

theorem cell23_7852131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 2, 3, 2, 2].length) (baseStart_7852131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7852131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7852131 prefixEnd_7852131 := by exact prefixLift 7852131
  have htrace : WordTrace (prefixWord ++ tailWord_7852131) baseStart_7852131 baseEnd_7852131 := by
    simpa [prefixWord, tailWord_7852131, baseEnd_7852131] using wordTrace_append hprefix tailTrace_7852131
  have hstable : (prefixWord ++ tailWord_7852131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7852131).length < 2 ^ (prefixWord ++ tailWord_7852131).sum := by decide
  have hdescent : baseEnd_7852131 < baseStart_7852131 := by decide
  rcases family_descends (prefixWord ++ tailWord_7852131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7852181 : List Nat := [1, 3, 2, 1, 1, 1, 5, 3, 2, 1, 3]
def baseStart_7852181 : Nat := 118140960795 + 7852181 * 2 ^ 59
def prefixEnd_7852181 : Nat := 4983230072969 + 3 ^ 40 * 7852181 * 2
def baseEnd_7852181 : Nat := 4031943039101848039425983

theorem tailTrace_7852181 : CollatzResearch.WordTrace tailWord_7852181 prefixEnd_7852181 4031943039101848039425983 := by
  unfold tailWord_7852181
  simp only [CollatzResearch.WordTrace]
  refine ⟨286392569165896757593804397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190928379443931171729202931 286392569165896757593804397)
  ·
    refine ⟨107397213437211284097676649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 286392569165896757593804397 107397213437211284097676649)
    ·
      refine ⟨80547910077908463073257487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107397213437211284097676649 80547910077908463073257487)
      ·
        refine ⟨120821865116862694609886231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80547910077908463073257487 120821865116862694609886231)
        ·
          refine ⟨181232797675294041914829347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120821865116862694609886231 181232797675294041914829347)
          ·
            refine ⟨271849196512941062872244021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181232797675294041914829347 271849196512941062872244021)
            ·
              refine ⟨25485862173088224644272877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 271849196512941062872244021 25485862173088224644272877)
              ·
                refine ⟨9557198314908084241602329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25485862173088224644272877 9557198314908084241602329)
                ·
                  refine ⟨7167898736181063181201747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9557198314908084241602329 7167898736181063181201747)
                  ·
                    refine ⟨10751848104271594771802621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7167898736181063181201747 10751848104271594771802621)
                    ·
                      refine ⟨4031943039101848039425983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10751848104271594771802621 4031943039101848039425983)
                      ·
                        rfl

theorem cell23_7852181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 3, 2, 1, 3].length) (baseStart_7852181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7852181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7852181 prefixEnd_7852181 := by exact prefixLift 7852181
  have htrace : WordTrace (prefixWord ++ tailWord_7852181) baseStart_7852181 baseEnd_7852181 := by
    simpa [prefixWord, tailWord_7852181, baseEnd_7852181] using wordTrace_append hprefix tailTrace_7852181
  have hstable : (prefixWord ++ tailWord_7852181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7852181).length < 2 ^ (prefixWord ++ tailWord_7852181).sum := by decide
  have hdescent : baseEnd_7852181 < baseStart_7852181 := by decide
  rcases family_descends (prefixWord ++ tailWord_7852181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7852182 : List Nat := [5, 3, 2, 1, 1, 1, 1, 1, 3, 1, 4]
def baseStart_7852182 : Nat := 118140960795 + 7852182 * 2 ^ 59
def prefixEnd_7852182 : Nat := 4983230072969 + 3 ^ 40 * 7852182 * 2
def baseEnd_7852182 : Nat := 4031943552582502535513479

theorem tailTrace_7852182 : CollatzResearch.WordTrace tailWord_7852182 prefixEnd_7852182 4031943552582502535513479 := by
  unfold tailWord_7852182
  simp only [CollatzResearch.WordTrace]
  refine ⟨17899537852430820922786925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 190928403759262089843060533 17899537852430820922786925)
  ·
    refine ⟨6712326694661557846045097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17899537852430820922786925 6712326694661557846045097)
    ·
      refine ⟨5034245020996168384533823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6712326694661557846045097 5034245020996168384533823)
      ·
        refine ⟨7551367531494252576800735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5034245020996168384533823 7551367531494252576800735)
        ·
          refine ⟨11327051297241378865201103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7551367531494252576800735 11327051297241378865201103)
          ·
            refine ⟨16990576945862068297801655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11327051297241378865201103 16990576945862068297801655)
            ·
              refine ⟨25485865418793102446702483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16990576945862068297801655 25485865418793102446702483)
              ·
                refine ⟨38228798128189653670053725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25485865418793102446702483 38228798128189653670053725)
                ·
                  refine ⟨14335799298071120126270147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38228798128189653670053725 14335799298071120126270147)
                  ·
                    refine ⟨21503698947106680189405221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14335799298071120126270147 21503698947106680189405221)
                    ·
                      refine ⟨4031943552582502535513479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21503698947106680189405221 4031943552582502535513479)
                      ·
                        rfl

theorem cell23_7852182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_7852182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7852182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7852182 prefixEnd_7852182 := by exact prefixLift 7852182
  have htrace : WordTrace (prefixWord ++ tailWord_7852182) baseStart_7852182 baseEnd_7852182 := by
    simpa [prefixWord, tailWord_7852182, baseEnd_7852182] using wordTrace_append hprefix tailTrace_7852182
  have hstable : (prefixWord ++ tailWord_7852182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7852182).length < 2 ^ (prefixWord ++ tailWord_7852182).sum := by decide
  have hdescent : baseEnd_7852182 < baseStart_7852182 := by decide
  rcases family_descends (prefixWord ++ tailWord_7852182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7852224 : List Nat := [2, 1, 1, 2, 5, 1, 1, 1, 2, 4, 3]
def baseStart_7852224 : Nat := 118140960795 + 7852224 * 2 ^ 59
def prefixEnd_7852224 : Nat := 4983230072969 + 3 ^ 40 * 7852224 * 2
def baseEnd_7852224 : Nat := 4031965118769991371188285

theorem tailTrace_7852224 : CollatzResearch.WordTrace tailWord_7852224 prefixEnd_7852224 4031965118769991371188285 := by
  unfold tailWord_7852224
  simp only [CollatzResearch.WordTrace]
  refine ⟨143197068752370487968809863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190929425003160650625079817 143197068752370487968809863)
  ·
    refine ⟨214795603128555731953214795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143197068752370487968809863 214795603128555731953214795)
    ·
      refine ⟨322193404692833597929822193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214795603128555731953214795 322193404692833597929822193)
      ·
        refine ⟨241645053519625198447366645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 322193404692833597929822193 241645053519625198447366645)
        ·
          refine ⟨22654223767464862354440623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 241645053519625198447366645 22654223767464862354440623)
          ·
            refine ⟨33981335651197293531660935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22654223767464862354440623 33981335651197293531660935)
            ·
              refine ⟨50972003476795940297491403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33981335651197293531660935 50972003476795940297491403)
              ·
                refine ⟨76458005215193910446237105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50972003476795940297491403 76458005215193910446237105)
                ·
                  refine ⟨57343503911395432834677829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76458005215193910446237105 57343503911395432834677829)
                  ·
                    refine ⟨10751906983386643656502093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57343503911395432834677829 10751906983386643656502093)
                    ·
                      refine ⟨4031965118769991371188285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10751906983386643656502093 4031965118769991371188285)
                      ·
                        rfl

theorem cell23_7852224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 1, 2, 4, 3].length) (baseStart_7852224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7852224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7852224 prefixEnd_7852224 := by exact prefixLift 7852224
  have htrace : WordTrace (prefixWord ++ tailWord_7852224) baseStart_7852224 baseEnd_7852224 := by
    simpa [prefixWord, tailWord_7852224, baseEnd_7852224] using wordTrace_append hprefix tailTrace_7852224
  have hstable : (prefixWord ++ tailWord_7852224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7852224).length < 2 ^ (prefixWord ++ tailWord_7852224).sum := by decide
  have hdescent : baseEnd_7852224 < baseStart_7852224 := by decide
  rcases family_descends (prefixWord ++ tailWord_7852224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7852234 : List Nat := [3, 1, 2, 1, 3, 1, 3, 1, 2, 2, 4]
def baseStart_7852234 : Nat := 118140960795 + 7852234 * 2 ^ 59
def prefixEnd_7852234 : Nat := 4983230072969 + 3 ^ 40 * 7852234 * 2
def baseEnd_7852234 : Nat := 4031970253576536332063239

theorem tailTrace_7852234 : CollatzResearch.WordTrace tailWord_7852234 prefixEnd_7852234 4031970253576536332063239 := by
  unfold tailWord_7852234
  simp only [CollatzResearch.WordTrace]
  refine ⟨71598625558676186911370939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190929668156469831763655837 71598625558676186911370939)
  ·
    refine ⟨107397938338014280367056409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71598625558676186911370939 107397938338014280367056409)
    ·
      refine ⟨80548453753510710275292307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107397938338014280367056409 80548453753510710275292307)
      ·
        refine ⟨120822680630266065412938461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80548453753510710275292307 120822680630266065412938461)
        ·
          refine ⟨45308505236349774529851923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120822680630266065412938461 45308505236349774529851923)
          ·
            refine ⟨67962757854524661794777885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45308505236349774529851923 67962757854524661794777885)
            ·
              refine ⟨25486034195446748173041707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67962757854524661794777885 25486034195446748173041707)
              ·
                refine ⟨38229051293170122259562561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25486034195446748173041707 38229051293170122259562561)
                ·
                  refine ⟨28671788469877591694671921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38229051293170122259562561 28671788469877591694671921)
                  ·
                    refine ⟨21503841352408193771003941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28671788469877591694671921 21503841352408193771003941)
                    ·
                      refine ⟨4031970253576536332063239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21503841352408193771003941 4031970253576536332063239)
                      ·
                        rfl

theorem cell23_7852234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 1, 2, 2, 4].length) (baseStart_7852234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7852234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7852234 prefixEnd_7852234 := by exact prefixLift 7852234
  have htrace : WordTrace (prefixWord ++ tailWord_7852234) baseStart_7852234 baseEnd_7852234 := by
    simpa [prefixWord, tailWord_7852234, baseEnd_7852234] using wordTrace_append hprefix tailTrace_7852234
  have hstable : (prefixWord ++ tailWord_7852234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7852234).length < 2 ^ (prefixWord ++ tailWord_7852234).sum := by decide
  have hdescent : baseEnd_7852234 < baseStart_7852234 := by decide
  rcases family_descends (prefixWord ++ tailWord_7852234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7852238 : List Nat := [4, 1, 1, 1, 4, 2, 2, 1, 1, 4, 2]
def baseStart_7852238 : Nat := 118140960795 + 7852238 * 2 ^ 59
def prefixEnd_7852238 : Nat := 4983230072969 + 3 ^ 40 * 7852238 * 2
def baseEnd_7852238 : Nat := 4031972307499154316413221

theorem tailTrace_7852238 : CollatzResearch.WordTrace tailWord_7852238 prefixEnd_7852238 4031972307499154316413221 := by
  unfold tailWord_7852238
  simp only [CollatzResearch.WordTrace]
  refine ⟨35799331015836282041078671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 190929765417793504219086245 35799331015836282041078671)
  ·
    refine ⟨53698996523754423061618007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35799331015836282041078671 53698996523754423061618007)
    ·
      refine ⟨80548494785631634592427011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53698996523754423061618007 80548494785631634592427011)
      ·
        refine ⟨120822742178447451888640517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80548494785631634592427011 120822742178447451888640517)
        ·
          refine ⟨22654264158458897229120097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 120822742178447451888640517 22654264158458897229120097)
          ·
            refine ⟨16990698118844172921840073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22654264158458897229120097 16990698118844172921840073)
            ·
              refine ⟨12743023589133129691380055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16990698118844172921840073 12743023589133129691380055)
              ·
                refine ⟨19114535383699694537070083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12743023589133129691380055 19114535383699694537070083)
                ·
                  refine ⟨28671803075549541805605125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19114535383699694537070083 28671803075549541805605125)
                  ·
                    refine ⟨5375963076665539088550961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28671803075549541805605125 5375963076665539088550961)
                    ·
                      refine ⟨4031972307499154316413221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5375963076665539088550961 4031972307499154316413221)
                      ·
                        rfl

theorem cell23_7852238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 2, 1, 1, 4, 2].length) (baseStart_7852238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7852238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7852238 prefixEnd_7852238 := by exact prefixLift 7852238
  have htrace : WordTrace (prefixWord ++ tailWord_7852238) baseStart_7852238 baseEnd_7852238 := by
    simpa [prefixWord, tailWord_7852238, baseEnd_7852238] using wordTrace_append hprefix tailTrace_7852238
  have hstable : (prefixWord ++ tailWord_7852238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7852238).length < 2 ^ (prefixWord ++ tailWord_7852238).sum := by decide
  have hdescent : baseEnd_7852238 < baseStart_7852238 := by decide
  rcases family_descends (prefixWord ++ tailWord_7852238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7852259 : List Nat := [1, 1, 1, 8, 2, 1, 2, 1, 1, 3, 2]
def baseStart_7852259 : Nat := 118140960795 + 7852259 * 2 ^ 59
def prefixEnd_7852259 : Nat := 4983230072969 + 3 ^ 40 * 7852259 * 2
def baseEnd_7852259 : Nat := 4031983090592898734250625

theorem tailTrace_7852259 : CollatzResearch.WordTrace tailWord_7852259 prefixEnd_7852259 4031983090592898734250625 := by
  unfold tailWord_7852259
  simp only [CollatzResearch.WordTrace]
  refine ⟨286395414059614176915143831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190930276039742784610095887 286395414059614176915143831)
  ·
    refine ⟨429593121089421265372715747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286395414059614176915143831 429593121089421265372715747)
    ·
      refine ⟨644389681634131898059073621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 429593121089421265372715747 644389681634131898059073621)
      ·
        refine ⟨7551441581649983180379769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 644389681634131898059073621 7551441581649983180379769)
        ·
          refine ⟨5663581186237487385284827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7551441581649983180379769 5663581186237487385284827)
          ·
            refine ⟨8495371779356231077927241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5663581186237487385284827 8495371779356231077927241)
            ·
              refine ⟨6371528834517173308445431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8495371779356231077927241 6371528834517173308445431)
              ·
                refine ⟨9557293251775759962668147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6371528834517173308445431 9557293251775759962668147)
                ·
                  refine ⟨14335939877663639944002221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9557293251775759962668147 14335939877663639944002221)
                  ·
                    refine ⟨5375977454123864979000833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14335939877663639944002221 5375977454123864979000833)
                    ·
                      refine ⟨4031983090592898734250625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5375977454123864979000833 4031983090592898734250625)
                      ·
                        rfl

theorem cell23_7852259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_7852259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7852259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7852259 prefixEnd_7852259 := by exact prefixLift 7852259
  have htrace : WordTrace (prefixWord ++ tailWord_7852259) baseStart_7852259 baseEnd_7852259 := by
    simpa [prefixWord, tailWord_7852259, baseEnd_7852259] using wordTrace_append hprefix tailTrace_7852259
  have hstable : (prefixWord ++ tailWord_7852259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7852259).length < 2 ^ (prefixWord ++ tailWord_7852259).sum := by decide
  have hdescent : baseEnd_7852259 < baseStart_7852259 := by decide
  rcases family_descends (prefixWord ++ tailWord_7852259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7852261 : List Nat := [1, 3, 1, 4, 2, 1, 1, 5, 5]
def baseStart_7852261 : Nat := 118140960795 + 7852261 * 2 ^ 59
def prefixEnd_7852261 : Nat := 4983230072969 + 3 ^ 40 * 7852261 * 2
def baseEnd_7852261 : Nat := 447998235283800858491735

theorem tailTrace_7852261 : CollatzResearch.WordTrace tailWord_7852261 prefixEnd_7852261 447998235283800858491735 := by
  unfold tailWord_7852261
  simp only [CollatzResearch.WordTrace]
  refine ⟨286395487005606931256716637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190930324670404620837811091 286395487005606931256716637)
  ·
    refine ⟨107398307627102599221268739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 286395487005606931256716637 107398307627102599221268739)
    ·
      refine ⟨161097461440653898831903109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107398307627102599221268739 161097461440653898831903109)
      ·
        refine ⟨30205774020122606030981833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 161097461440653898831903109 30205774020122606030981833)
        ·
          refine ⟨22654330515091954523236375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30205774020122606030981833 22654330515091954523236375)
          ·
            refine ⟨33981495772637931784854563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22654330515091954523236375 33981495772637931784854563)
            ·
              refine ⟨50972243658956897677281845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33981495772637931784854563 50972243658956897677281845)
              ·
                refine ⟨4778647843027209157245173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50972243658956897677281845 4778647843027209157245173)
                ·
                  refine ⟨447998235283800858491735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4778647843027209157245173 447998235283800858491735)
                  ·
                    rfl

theorem cell23_7852261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 5, 5].length) (baseStart_7852261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7852261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7852261 prefixEnd_7852261 := by exact prefixLift 7852261
  have htrace : WordTrace (prefixWord ++ tailWord_7852261) baseStart_7852261 baseEnd_7852261 := by
    simpa [prefixWord, tailWord_7852261, baseEnd_7852261] using wordTrace_append hprefix tailTrace_7852261
  have hstable : (prefixWord ++ tailWord_7852261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7852261).length < 2 ^ (prefixWord ++ tailWord_7852261).sum := by decide
  have hdescent : baseEnd_7852261 < baseStart_7852261 := by decide
  rcases family_descends (prefixWord ++ tailWord_7852261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7852328 : List Nat := [2, 1, 5, 1, 3, 1, 1, 2, 2, 1, 4]
def baseStart_7852328 : Nat := 118140960795 + 7852328 * 2 ^ 59
def prefixEnd_7852328 : Nat := 4983230072969 + 3 ^ 40 * 7852328 * 2
def baseEnd_7852328 : Nat := 4032018520758058964287807

theorem tailTrace_7852328 : CollatzResearch.WordTrace tailWord_7852328 prefixEnd_7852328 4032018520758058964287807 := by
  unfold tailWord_7852328
  simp only [CollatzResearch.WordTrace]
  refine ⟨143198965348182100849702819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190931953797576134466270425 143198965348182100849702819)
  ·
    refine ⟨214798448022273151274554229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143198965348182100849702819 214798448022273151274554229)
    ·
      refine ⟨20137354502088107931989459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 214798448022273151274554229 20137354502088107931989459)
      ·
        refine ⟨30206031753132161897984189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20137354502088107931989459 30206031753132161897984189)
        ·
          refine ⟨11327261907424560711744071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30206031753132161897984189 11327261907424560711744071)
          ·
            refine ⟨16990892861136841067616107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11327261907424560711744071 16990892861136841067616107)
            ·
              refine ⟨25486339291705261601424161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16990892861136841067616107 25486339291705261601424161)
              ·
                refine ⟨19114754468778946201068121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25486339291705261601424161 19114754468778946201068121)
                ·
                  refine ⟨14336065851584209650801091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19114754468778946201068121 14336065851584209650801091)
                  ·
                    refine ⟨21504098777376314476201637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14336065851584209650801091 21504098777376314476201637)
                    ·
                      refine ⟨4032018520758058964287807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21504098777376314476201637 4032018520758058964287807)
                      ·
                        rfl

theorem cell23_7852328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 2, 2, 1, 4].length) (baseStart_7852328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7852328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7852328 prefixEnd_7852328 := by exact prefixLift 7852328
  have htrace : WordTrace (prefixWord ++ tailWord_7852328) baseStart_7852328 baseEnd_7852328 := by
    simpa [prefixWord, tailWord_7852328, baseEnd_7852328] using wordTrace_append hprefix tailTrace_7852328
  have hstable : (prefixWord ++ tailWord_7852328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7852328).length < 2 ^ (prefixWord ++ tailWord_7852328).sum := by decide
  have hdescent : baseEnd_7852328 < baseStart_7852328 := by decide
  rcases family_descends (prefixWord ++ tailWord_7852328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7852361 : List Nat := [1, 2, 1, 1, 2, 3, 1, 3, 5, 1, 3]
def baseStart_7852361 : Nat := 118140960795 + 7852361 * 2 ^ 59
def prefixEnd_7852361 : Nat := 4983230072969 + 3 ^ 40 * 7852361 * 2
def baseEnd_7852361 : Nat := 4032035465619657335175155

theorem tailTrace_7852361 : CollatzResearch.WordTrace tailWord_7852361 prefixEnd_7852361 4032035465619657335175155 := by
  unfold tailWord_7852361
  simp only [CollatzResearch.WordTrace]
  refine ⟨286399134305244648335356937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190932756203496432223571291 286399134305244648335356937)
  ·
    refine ⟨214799350728933486251517703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286399134305244648335356937 214799350728933486251517703)
    ·
      refine ⟨322199026093400229377276555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214799350728933486251517703 322199026093400229377276555)
      ·
        refine ⟨483298539140100344065914833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322199026093400229377276555 483298539140100344065914833)
        ·
          refine ⟨362473904355075258049436125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 483298539140100344065914833 362473904355075258049436125)
          ·
            refine ⟨135927714133153221768538547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 362473904355075258049436125 135927714133153221768538547)
            ·
              refine ⟨203891571199729832652807821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135927714133153221768538547 203891571199729832652807821)
              ·
                refine ⟨76459339199898687244802933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 203891571199729832652807821 76459339199898687244802933)
                ·
                  refine ⟨7168063049990501929200275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 76459339199898687244802933 7168063049990501929200275)
                  ·
                    refine ⟨10752094574985752893800413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7168063049990501929200275 10752094574985752893800413)
                    ·
                      refine ⟨4032035465619657335175155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10752094574985752893800413 4032035465619657335175155)
                      ·
                        rfl

theorem cell23_7852361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 3, 5, 1, 3].length) (baseStart_7852361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7852361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7852361 prefixEnd_7852361 := by exact prefixLift 7852361
  have htrace : WordTrace (prefixWord ++ tailWord_7852361) baseStart_7852361 baseEnd_7852361 := by
    simpa [prefixWord, tailWord_7852361, baseEnd_7852361] using wordTrace_append hprefix tailTrace_7852361
  have hstable : (prefixWord ++ tailWord_7852361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7852361).length < 2 ^ (prefixWord ++ tailWord_7852361).sum := by decide
  have hdescent : baseEnd_7852361 < baseStart_7852361 := by decide
  rcases family_descends (prefixWord ++ tailWord_7852361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7852388 : List Nat := [2, 3, 1, 1, 3, 1, 1, 4, 2, 3, 2]
def baseStart_7852388 : Nat := 118140960795 + 7852388 * 2 ^ 59
def prefixEnd_7852388 : Nat := 4983230072969 + 3 ^ 40 * 7852388 * 2
def baseEnd_7852388 : Nat := 4032049329597328729537531

theorem tailTrace_7852388 : CollatzResearch.WordTrace tailWord_7852388 prefixEnd_7852388 4032049329597328729537531 := by
  unfold tailWord_7852388
  simp only [CollatzResearch.WordTrace]
  refine ⟨143200059538073415973294909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190933412717431221297726545 143200059538073415973294909)
  ·
    refine ⟨53700022326777530989985591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143200059538073415973294909 53700022326777530989985591)
    ·
      refine ⟨80550033490166296484978387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53700022326777530989985591 80550033490166296484978387)
      ·
        refine ⟨120825050235249444727467581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80550033490166296484978387 120825050235249444727467581)
        ·
          refine ⟨45309393838218541772800343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120825050235249444727467581 45309393838218541772800343)
          ·
            refine ⟨67964090757327812659200515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45309393838218541772800343 67964090757327812659200515)
            ·
              refine ⟨101946136135991718988800773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67964090757327812659200515 101946136135991718988800773)
              ·
                refine ⟨19114900525498447310400145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 101946136135991718988800773 19114900525498447310400145)
                ·
                  refine ⟨14336175394123835482800109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19114900525498447310400145 14336175394123835482800109)
                  ·
                    refine ⟨5376065772796438306050041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14336175394123835482800109 5376065772796438306050041)
                    ·
                      refine ⟨4032049329597328729537531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5376065772796438306050041 4032049329597328729537531)
                      ·
                        rfl

theorem cell23_7852388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 4, 2, 3, 2].length) (baseStart_7852388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7852388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7852388 prefixEnd_7852388 := by exact prefixLift 7852388
  have htrace : WordTrace (prefixWord ++ tailWord_7852388) baseStart_7852388 baseEnd_7852388 := by
    simpa [prefixWord, tailWord_7852388, baseEnd_7852388] using wordTrace_append hprefix tailTrace_7852388
  have hstable : (prefixWord ++ tailWord_7852388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7852388).length < 2 ^ (prefixWord ++ tailWord_7852388).sum := by decide
  have hdescent : baseEnd_7852388 < baseStart_7852388 := by decide
  rcases family_descends (prefixWord ++ tailWord_7852388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7852401 : List Nat := [1, 2, 2, 2, 1, 2, 1, 2, 2, 6, 2]
def baseStart_7852401 : Nat := 118140960795 + 7852401 * 2 ^ 59
def prefixEnd_7852401 : Nat := 4983230072969 + 3 ^ 40 * 7852401 * 2
def baseEnd_7852401 : Nat := 4032056004845837178674971

theorem tailTrace_7852401 : CollatzResearch.WordTrace tailWord_7852401 prefixEnd_7852401 4032056004845837178674971 := by
  unfold tailWord_7852401
  simp only [CollatzResearch.WordTrace]
  refine ⟨286400593225099735166813057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190933728816733156777875371 286400593225099735166813057)
  ·
    refine ⟨214800444918824801375109793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286400593225099735166813057 214800444918824801375109793)
    ·
      refine ⟨161100333689118601031332345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214800444918824801375109793 161100333689118601031332345)
      ·
        refine ⟨120825250266838950773499259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161100333689118601031332345 120825250266838950773499259)
        ·
          refine ⟨181237875400258426160248889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120825250266838950773499259 181237875400258426160248889)
          ·
            refine ⟨135928406550193819620186667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181237875400258426160248889 135928406550193819620186667)
            ·
              refine ⟨203892609825290729430280001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135928406550193819620186667 203892609825290729430280001)
              ·
                refine ⟨152919457368968047072710001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 203892609825290729430280001 152919457368968047072710001)
                ·
                  refine ⟨114689593026726035304532501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 152919457368968047072710001 114689593026726035304532501)
                  ·
                    refine ⟨5376074673127782904899961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 114689593026726035304532501 5376074673127782904899961)
                    ·
                      refine ⟨4032056004845837178674971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5376074673127782904899961 4032056004845837178674971)
                      ·
                        rfl

theorem cell23_7852401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 2, 2, 6, 2].length) (baseStart_7852401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7852401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7852401 prefixEnd_7852401 := by exact prefixLift 7852401
  have htrace : WordTrace (prefixWord ++ tailWord_7852401) baseStart_7852401 baseEnd_7852401 := by
    simpa [prefixWord, tailWord_7852401, baseEnd_7852401] using wordTrace_append hprefix tailTrace_7852401
  have hstable : (prefixWord ++ tailWord_7852401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7852401).length < 2 ^ (prefixWord ++ tailWord_7852401).sum := by decide
  have hdescent : baseEnd_7852401 < baseStart_7852401 := by decide
  rcases family_descends (prefixWord ++ tailWord_7852401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7852411 : List Nat := [1, 1, 1, 1, 1, 8, 2, 1, 1, 6]
def baseStart_7852411 : Nat := 118140960795 + 7852411 * 2 ^ 59
def prefixEnd_7852411 : Nat := 4983230072969 + 3 ^ 40 * 7852411 * 2
def baseEnd_7852411 : Nat := 1344020379884127379849975

theorem tailTrace_7852411 : CollatzResearch.WordTrace tailWord_7852411 prefixEnd_7852411 1344020379884127379849975 := by
  unfold tailWord_7852411
  simp only [CollatzResearch.WordTrace]
  refine ⟨286400957955063506874677087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190933971970042337916451391 286400957955063506874677087)
  ·
    refine ⟨429601436932595260312015631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286400957955063506874677087 429601436932595260312015631)
    ·
      refine ⟨644402155398892890468023447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 429601436932595260312015631 644402155398892890468023447)
      ·
        refine ⟨966603233098339335702035171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 644402155398892890468023447 966603233098339335702035171)
        ·
          refine ⟨1449904849647509003553052757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 966603233098339335702035171 1449904849647509003553052757)
          ·
            refine ⟨16991072456806746135387337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1449904849647509003553052757 16991072456806746135387337)
            ·
              refine ⟨12743304342605059601540503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16991072456806746135387337 12743304342605059601540503)
              ·
                refine ⟨19114956513907589402310755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12743304342605059601540503 19114956513907589402310755)
                ·
                  refine ⟨28672434770861384103466133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19114956513907589402310755 28672434770861384103466133)
                  ·
                    refine ⟨1344020379884127379849975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28672434770861384103466133 1344020379884127379849975)
                    ·
                      rfl

theorem cell23_7852411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 2, 1, 1, 6].length) (baseStart_7852411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7852411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7852411 prefixEnd_7852411 := by exact prefixLift 7852411
  have htrace : WordTrace (prefixWord ++ tailWord_7852411) baseStart_7852411 baseEnd_7852411 := by
    simpa [prefixWord, tailWord_7852411, baseEnd_7852411] using wordTrace_append hprefix tailTrace_7852411
  have hstable : (prefixWord ++ tailWord_7852411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7852411).length < 2 ^ (prefixWord ++ tailWord_7852411).sum := by decide
  have hdescent : baseEnd_7852411 < baseStart_7852411 := by decide
  rcases family_descends (prefixWord ++ tailWord_7852411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7852452 : List Nat := [2, 3, 1, 2, 1, 1, 4, 4, 1, 2, 2]
def baseStart_7852452 : Nat := 118140960795 + 7852452 * 2 ^ 59
def prefixEnd_7852452 : Nat := 4983230072969 + 3 ^ 40 * 7852452 * 2
def baseEnd_7852452 : Nat := 4032082192359216479137237

theorem tailTrace_7852452 : CollatzResearch.WordTrace tailWord_7852452 prefixEnd_7852452 4032082192359216479137237 := by
  unfold tailWord_7852452
  simp only [CollatzResearch.WordTrace]
  refine ⟨143201226673957485438459805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190934968898609980584613073 143201226673957485438459805)
  ·
    refine ⟨53700460002734057039422427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143201226673957485438459805 53700460002734057039422427)
    ·
      refine ⟨80550690004101085559133641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53700460002734057039422427 80550690004101085559133641)
      ·
        refine ⟨60413017503075814169350231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80550690004101085559133641 60413017503075814169350231)
        ·
          refine ⟨90619526254613721254025347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60413017503075814169350231 90619526254613721254025347)
          ·
            refine ⟨135929289381920581881038021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90619526254613721254025347 135929289381920581881038021)
            ·
              refine ⟨25486741759110109102694629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 135929289381920581881038021 25486741759110109102694629)
              ·
                refine ⟨4778764079833145456755243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25486741759110109102694629 4778764079833145456755243)
                ·
                  refine ⟨7168146119749718185132865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4778764079833145456755243 7168146119749718185132865)
                  ·
                    refine ⟨5376109589812288638849649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7168146119749718185132865 5376109589812288638849649)
                    ·
                      refine ⟨4032082192359216479137237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5376109589812288638849649 4032082192359216479137237)
                      ·
                        rfl

theorem cell23_7852452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 4, 1, 2, 2].length) (baseStart_7852452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7852452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7852452 prefixEnd_7852452 := by exact prefixLift 7852452
  have htrace : WordTrace (prefixWord ++ tailWord_7852452) baseStart_7852452 baseEnd_7852452 := by
    simpa [prefixWord, tailWord_7852452, baseEnd_7852452] using wordTrace_append hprefix tailTrace_7852452
  have hstable : (prefixWord ++ tailWord_7852452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7852452).length < 2 ^ (prefixWord ++ tailWord_7852452).sum := by decide
  have hdescent : baseEnd_7852452 < baseStart_7852452 := by decide
  rcases family_descends (prefixWord ++ tailWord_7852452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7852502 : List Nat := [5, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3]
def baseStart_7852502 : Nat := 118140960795 + 7852502 * 2 ^ 59
def prefixEnd_7852502 : Nat := 4983230072969 + 3 ^ 40 * 7852502 * 2
def baseEnd_7852502 : Nat := 4032107866391941283512007

theorem tailTrace_7852502 : CollatzResearch.WordTrace tailWord_7852502 prefixEnd_7852502 4032107866391941283512007 := by
  unfold tailWord_7852502
  simp only [CollatzResearch.WordTrace]
  refine ⟨17900267312358364338514985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 190936184665155886277493173 17900267312358364338514985)
  ·
    refine ⟨13425200484268773253886239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17900267312358364338514985 13425200484268773253886239)
    ·
      refine ⟨20137800726403159880829359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13425200484268773253886239 20137800726403159880829359)
      ·
        refine ⟨30206701089604739821244039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20137800726403159880829359 30206701089604739821244039)
        ·
          refine ⟨45310051634407109731866059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30206701089604739821244039 45310051634407109731866059)
          ·
            refine ⟨67965077451610664597799089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45310051634407109731866059 67965077451610664597799089)
            ·
              refine ⟨50973808088707998448349317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67965077451610664597799089 50973808088707998448349317)
              ·
                refine ⟨9557589016632749709065497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50973808088707998448349317 9557589016632749709065497)
                ·
                  refine ⟨7168191762474562281799123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9557589016632749709065497 7168191762474562281799123)
                  ·
                    refine ⟨10752287643711843422698685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7168191762474562281799123 10752287643711843422698685)
                    ·
                      refine ⟨4032107866391941283512007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10752287643711843422698685 4032107866391941283512007)
                      ·
                        rfl

theorem cell23_7852502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3].length) (baseStart_7852502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7852502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7852502 prefixEnd_7852502 := by exact prefixLift 7852502
  have htrace : WordTrace (prefixWord ++ tailWord_7852502) baseStart_7852502 baseEnd_7852502 := by
    simpa [prefixWord, tailWord_7852502, baseEnd_7852502] using wordTrace_append hprefix tailTrace_7852502
  have hstable : (prefixWord ++ tailWord_7852502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7852502).length < 2 ^ (prefixWord ++ tailWord_7852502).sum := by decide
  have hdescent : baseEnd_7852502 < baseStart_7852502 := by decide
  rcases family_descends (prefixWord ++ tailWord_7852502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7852546 : List Nat := [3, 4, 1, 2, 2, 1, 3, 1, 1, 3, 2]
def baseStart_7852546 : Nat := 118140960795 + 7852546 * 2 ^ 59
def prefixEnd_7852546 : Nat := 4983230072969 + 3 ^ 40 * 7852546 * 2
def baseEnd_7852546 : Nat := 4032130459540739111361805

theorem tailTrace_7852546 : CollatzResearch.WordTrace tailWord_7852546 prefixEnd_7852546 4032130459540739111361805 := by
  unfold tailWord_7852546
  simp only [CollatzResearch.WordTrace]
  refine ⟨71601470452393606232710373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190937254539716283287227661 71601470452393606232710373)
  ·
    refine ⟨13425275709823801168633195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71601470452393606232710373 13425275709823801168633195)
    ·
      refine ⟨20137913564735701752949793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13425275709823801168633195 20137913564735701752949793)
      ·
        refine ⟨15103435173551776314712345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20137913564735701752949793 15103435173551776314712345)
        ·
          refine ⟨11327576380163832236034259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15103435173551776314712345 11327576380163832236034259)
          ·
            refine ⟨16991364570245748354051389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11327576380163832236034259 16991364570245748354051389)
            ·
              refine ⟨6371761713842155632769271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16991364570245748354051389 6371761713842155632769271)
              ·
                refine ⟨9557642570763233449153907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6371761713842155632769271 9557642570763233449153907)
                ·
                  refine ⟨14336463856144850173730861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9557642570763233449153907 14336463856144850173730861)
                  ·
                    refine ⟨5376173946054318815149073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14336463856144850173730861 5376173946054318815149073)
                    ·
                      refine ⟨4032130459540739111361805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5376173946054318815149073 4032130459540739111361805)
                      ·
                        rfl

theorem cell23_7852546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 3, 1, 1, 3, 2].length) (baseStart_7852546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7852546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7852546 prefixEnd_7852546 := by exact prefixLift 7852546
  have htrace : WordTrace (prefixWord ++ tailWord_7852546) baseStart_7852546 baseEnd_7852546 := by
    simpa [prefixWord, tailWord_7852546, baseEnd_7852546] using wordTrace_append hprefix tailTrace_7852546
  have hstable : (prefixWord ++ tailWord_7852546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7852546).length < 2 ^ (prefixWord ++ tailWord_7852546).sum := by decide
  have hdescent : baseEnd_7852546 < baseStart_7852546 := by decide
  rcases family_descends (prefixWord ++ tailWord_7852546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7852561 : List Nat := [1, 2, 2, 1, 1, 2, 2, 3, 4, 5]
def baseStart_7852561 : Nat := 118140960795 + 7852561 * 2 ^ 59
def prefixEnd_7852561 : Nat := 4983230072969 + 3 ^ 40 * 7852561 * 2
def baseEnd_7852561 : Nat := 1344046053916852184224745

theorem tailTrace_7852561 : CollatzResearch.WordTrace tailWord_7852561 prefixEnd_7852561 1344046053916852184224745 := by
  unfold tailWord_7852561
  simp only [CollatzResearch.WordTrace]
  refine ⟨286406428904520082492637537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190937619269680054995091691 286406428904520082492637537)
  ·
    refine ⟨214804821678390061869478153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286406428904520082492637537 214804821678390061869478153)
    ·
      refine ⟨161103616258792546402108615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214804821678390061869478153 161103616258792546402108615)
      ·
        refine ⟨241655424388188819603162923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161103616258792546402108615 241655424388188819603162923)
        ·
          refine ⟨362483136582283229404744385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241655424388188819603162923 362483136582283229404744385)
          ·
            refine ⟨271862352436712422053558289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 362483136582283229404744385 271862352436712422053558289)
            ·
              refine ⟨203896764327534316540168717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 271862352436712422053558289 203896764327534316540168717)
              ·
                refine ⟨76461286622825368702563269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 203896764327534316540168717 76461286622825368702563269)
                ·
                  refine ⟨14336491241779756631730613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76461286622825368702563269 14336491241779756631730613)
                  ·
                    refine ⟨1344046053916852184224745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14336491241779756631730613 1344046053916852184224745)
                    ·
                      rfl

theorem cell23_7852561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 5].length) (baseStart_7852561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7852561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7852561 prefixEnd_7852561 := by exact prefixLift 7852561
  have htrace : WordTrace (prefixWord ++ tailWord_7852561) baseStart_7852561 baseEnd_7852561 := by
    simpa [prefixWord, tailWord_7852561, baseEnd_7852561] using wordTrace_append hprefix tailTrace_7852561
  have hstable : (prefixWord ++ tailWord_7852561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7852561).length < 2 ^ (prefixWord ++ tailWord_7852561).sum := by decide
  have hdescent : baseEnd_7852561 < baseStart_7852561 := by decide
  rcases family_descends (prefixWord ++ tailWord_7852561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7852611 : List Nat := [1, 1, 1, 3, 1, 2, 1, 2, 1, 6, 4]
def baseStart_7852611 : Nat := 118140960795 + 7852611 * 2 ^ 59
def prefixEnd_7852611 : Nat := 4983230072969 + 3 ^ 40 * 7852611 * 2
def baseEnd_7852611 : Nat := 4032163835783281357049005

theorem tailTrace_7852611 : CollatzResearch.WordTrace tailWord_7852611 prefixEnd_7852611 4032163835783281357049005 := by
  unfold tailWord_7852611
  simp only [CollatzResearch.WordTrace]
  refine ⟨286408252554338941031957687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190938835036225960687971791 286408252554338941031957687)
  ·
    refine ⟨429612378831508411547936531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286408252554338941031957687 429612378831508411547936531)
    ·
      refine ⟨644418568247262617321904797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 429612378831508411547936531 644418568247262617321904797)
      ·
        refine ⟨241656963092723481495714299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 644418568247262617321904797 241656963092723481495714299)
        ·
          refine ⟨362485444639085222243571449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241656963092723481495714299 362485444639085222243571449)
          ·
            refine ⟨271864083479313916682678587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 362485444639085222243571449 271864083479313916682678587)
            ·
              refine ⟨407796125218970875024017881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 271864083479313916682678587 407796125218970875024017881)
              ·
                refine ⟨305847093914228156268013411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 407796125218970875024017881 305847093914228156268013411)
                ·
                  refine ⟨458770640871342234402020117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 305847093914228156268013411 458770640871342234402020117)
                  ·
                    refine ⟨21504873790844167237594693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 458770640871342234402020117 21504873790844167237594693)
                    ·
                      refine ⟨4032163835783281357049005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21504873790844167237594693 4032163835783281357049005)
                      ·
                        rfl

theorem cell23_7852611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 6, 4].length) (baseStart_7852611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7852611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7852611 prefixEnd_7852611 := by exact prefixLift 7852611
  have htrace : WordTrace (prefixWord ++ tailWord_7852611) baseStart_7852611 baseEnd_7852611 := by
    simpa [prefixWord, tailWord_7852611, baseEnd_7852611] using wordTrace_append hprefix tailTrace_7852611
  have hstable : (prefixWord ++ tailWord_7852611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7852611).length < 2 ^ (prefixWord ++ tailWord_7852611).sum := by decide
  have hdescent : baseEnd_7852611 < baseStart_7852611 := by decide
  rcases family_descends (prefixWord ++ tailWord_7852611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7852615 : List Nat := [1, 1, 4, 1, 4, 1, 1, 2, 2, 4, 2]
def baseStart_7852615 : Nat := 118140960795 + 7852615 * 2 ^ 59
def prefixEnd_7852615 : Nat := 4983230072969 + 3 ^ 40 * 7852615 * 2
def baseEnd_7852615 : Nat := 4032165889705899341398987

theorem tailTrace_7852615 : CollatzResearch.WordTrace tailWord_7852615 prefixEnd_7852615 4032165889705899341398987 := by
  unfold tailWord_7852615
  simp only [CollatzResearch.WordTrace]
  refine ⟨286408398446324449715103299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190938932297549633143402199 286408398446324449715103299)
  ·
    refine ⟨429612597669486674572654949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286408398446324449715103299 429612597669486674572654949)
    ·
      refine ⟨80552362063028751482372803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 429612597669486674572654949 80552362063028751482372803)
      ·
        refine ⟨120828543094543127223559205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80552362063028751482372803 120828543094543127223559205)
        ·
          refine ⟨22655351830226836354417351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 120828543094543127223559205 22655351830226836354417351)
          ·
            refine ⟨33983027745340254531626027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22655351830226836354417351 33983027745340254531626027)
            ·
              refine ⟨50974541618010381797439041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33983027745340254531626027 50974541618010381797439041)
              ·
                refine ⟨38230906213507786348079281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50974541618010381797439041 38230906213507786348079281)
                ·
                  refine ⟨28673179660130839761059461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38230906213507786348079281 28673179660130839761059461)
                  ·
                    refine ⟨5376221186274532455198649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28673179660130839761059461 5376221186274532455198649)
                    ·
                      refine ⟨4032165889705899341398987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5376221186274532455198649 4032165889705899341398987)
                      ·
                        rfl

theorem cell23_7852615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 2, 2, 4, 2].length) (baseStart_7852615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7852615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7852615 prefixEnd_7852615 := by exact prefixLift 7852615
  have htrace : WordTrace (prefixWord ++ tailWord_7852615) baseStart_7852615 baseEnd_7852615 := by
    simpa [prefixWord, tailWord_7852615, baseEnd_7852615] using wordTrace_append hprefix tailTrace_7852615
  have hstable : (prefixWord ++ tailWord_7852615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7852615).length < 2 ^ (prefixWord ++ tailWord_7852615).sum := by decide
  have hdescent : baseEnd_7852615 < baseStart_7852615 := by decide
  rcases family_descends (prefixWord ++ tailWord_7852615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7852625 : List Nat := [1, 2, 2, 1, 3, 4, 2, 1, 3, 4]
def baseStart_7852625 : Nat := 118140960795 + 7852625 * 2 ^ 59
def prefixEnd_7852625 : Nat := 4983230072969 + 3 ^ 40 * 7852625 * 2
def baseEnd_7852625 : Nat := 1344057008170814767424647

theorem tailTrace_7852625 : CollatzResearch.WordTrace tailWord_7852625 prefixEnd_7852625 1344057008170814767424647 := by
  unfold tailWord_7852625
  simp only [CollatzResearch.WordTrace]
  refine ⟨286408763176288221422967329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190939175450858814281978219 286408763176288221422967329)
  ·
    refine ⟨214806572382216166067225497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286408763176288221422967329 214806572382216166067225497)
    ·
      refine ⟨161104929286662124550419123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214806572382216166067225497 161104929286662124550419123)
      ·
        refine ⟨241657393929993186825628685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161104929286662124550419123 241657393929993186825628685)
        ·
          refine ⟨90621522723747445059610757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 241657393929993186825628685 90621522723747445059610757)
          ·
            refine ⟨16991535510702645948677017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90621522723747445059610757 16991535510702645948677017)
            ·
              refine ⟨12743651633026984461507763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16991535510702645948677017 12743651633026984461507763)
              ·
                refine ⟨19115477449540476692261645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12743651633026984461507763 19115477449540476692261645)
                ·
                  refine ⟨7168304043577678759598117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19115477449540476692261645 7168304043577678759598117)
                  ·
                    refine ⟨1344057008170814767424647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7168304043577678759598117 1344057008170814767424647)
                    ·
                      rfl

theorem cell23_7852625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 2, 1, 3, 4].length) (baseStart_7852625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7852625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7852625 prefixEnd_7852625 := by exact prefixLift 7852625
  have htrace : WordTrace (prefixWord ++ tailWord_7852625) baseStart_7852625 baseEnd_7852625 := by
    simpa [prefixWord, tailWord_7852625, baseEnd_7852625] using wordTrace_append hprefix tailTrace_7852625
  have hstable : (prefixWord ++ tailWord_7852625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7852625).length < 2 ^ (prefixWord ++ tailWord_7852625).sum := by decide
  have hdescent : baseEnd_7852625 < baseStart_7852625 := by decide
  rcases family_descends (prefixWord ++ tailWord_7852625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7852675 : List Nat := [1, 1, 1, 3, 3, 1, 3, 1, 4, 3, 2]
def baseStart_7852675 : Nat := 118140960795 + 7852675 * 2 ^ 59
def prefixEnd_7852675 : Nat := 4983230072969 + 3 ^ 40 * 7852675 * 2
def baseEnd_7852675 : Nat := 4032196698545169106648711

theorem tailTrace_7852675 : CollatzResearch.WordTrace tailWord_7852675 prefixEnd_7852675 4032196698545169106648711 := by
  unfold tailWord_7852675
  simp only [CollatzResearch.WordTrace]
  refine ⟨286410586826107079962287479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190940391217404719974858319 286410586826107079962287479)
  ·
    refine ⟨429615880239160619943431219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286410586826107079962287479 429615880239160619943431219)
    ·
      refine ⟨644423820358740929915146829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 429615880239160619943431219 644423820358740929915146829)
      ·
        refine ⟨241658932634527848718180061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 644423820358740929915146829 241658932634527848718180061)
        ·
          refine ⟨90622099737947943269317523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 241658932634527848718180061 90622099737947943269317523)
          ·
            refine ⟨135933149606921914903976285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90622099737947943269317523 135933149606921914903976285)
            ·
              refine ⟨50974931102595718088991107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135933149606921914903976285 50974931102595718088991107)
              ·
                refine ⟨76462396653893577133486661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50974931102595718088991107 76462396653893577133486661)
                ·
                  refine ⟨14336699372605045712528749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76462396653893577133486661 14336699372605045712528749)
                  ·
                    refine ⟨5376262264726892142198281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14336699372605045712528749 5376262264726892142198281)
                    ·
                      refine ⟨4032196698545169106648711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5376262264726892142198281 4032196698545169106648711)
                      ·
                        rfl

theorem cell23_7852675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 1, 4, 3, 2].length) (baseStart_7852675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7852675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7852675 prefixEnd_7852675 := by exact prefixLift 7852675
  have htrace : WordTrace (prefixWord ++ tailWord_7852675) baseStart_7852675 baseEnd_7852675 := by
    simpa [prefixWord, tailWord_7852675, baseEnd_7852675] using wordTrace_append hprefix tailTrace_7852675
  have hstable : (prefixWord ++ tailWord_7852675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7852675).length < 2 ^ (prefixWord ++ tailWord_7852675).sum := by decide
  have hdescent : baseEnd_7852675 < baseStart_7852675 := by decide
  rcases family_descends (prefixWord ++ tailWord_7852675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7852732 : List Nat := [2, 2, 2, 3, 1, 1, 4, 2, 2, 4]
def baseStart_7852732 : Nat := 118140960795 + 7852732 * 2 ^ 59
def prefixEnd_7852732 : Nat := 4983230072969 + 3 ^ 40 * 7852732 * 2
def baseEnd_7852732 : Nat := 1344075322314158461211983

theorem tailTrace_7852732 : CollatzResearch.WordTrace tailWord_7852732 prefixEnd_7852732 1344075322314158461211983 := by
  unfold tailWord_7852732
  simp only [CollatzResearch.WordTrace]
  refine ⟨143206332893450289348556225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190941777191267052464741633 143206332893450289348556225)
  ·
    refine ⟨107404749670087717011417169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143206332893450289348556225 107404749670087717011417169)
    ·
      refine ⟨80553562252565787758562877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107404749670087717011417169 80553562252565787758562877)
      ·
        refine ⟨30207585844712170409461079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80553562252565787758562877 30207585844712170409461079)
        ·
          refine ⟨45311378767068255614191619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30207585844712170409461079 45311378767068255614191619)
          ·
            refine ⟨67967068150602383421287429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45311378767068255614191619 67967068150602383421287429)
            ·
              refine ⟨12743825278237946891491393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67967068150602383421287429 12743825278237946891491393)
              ·
                refine ⟨9557868958678460168618545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12743825278237946891491393 9557868958678460168618545)
                ·
                  refine ⟨7168401719008845126463909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9557868958678460168618545 7168401719008845126463909)
                  ·
                    refine ⟨1344075322314158461211983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7168401719008845126463909 1344075322314158461211983)
                    ·
                      rfl

theorem cell23_7852732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 4, 2, 2, 4].length) (baseStart_7852732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7852732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7852732 prefixEnd_7852732 := by exact prefixLift 7852732
  have htrace : WordTrace (prefixWord ++ tailWord_7852732) baseStart_7852732 baseEnd_7852732 := by
    simpa [prefixWord, tailWord_7852732, baseEnd_7852732] using wordTrace_append hprefix tailTrace_7852732
  have hstable : (prefixWord ++ tailWord_7852732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7852732).length < 2 ^ (prefixWord ++ tailWord_7852732).sum := by decide
  have hdescent : baseEnd_7852732 < baseStart_7852732 := by decide
  rcases family_descends (prefixWord ++ tailWord_7852732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7852749 : List Nat := [1, 6, 2, 1, 2, 1, 2, 1, 1, 6]
def baseStart_7852749 : Nat := 118140960795 + 7852749 * 2 ^ 59
def prefixEnd_7852749 : Nat := 4983230072969 + 3 ^ 40 * 7852749 * 2
def baseEnd_7852749 : Nat := 1344078232037867272374457

theorem tailTrace_7852749 : CollatzResearch.WordTrace tailWord_7852749 prefixEnd_7852749 1344078232037867272374457 := by
  unfold tailWord_7852749
  simp only [CollatzResearch.WordTrace]
  refine ⟨286413285827838990600481301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190942190551892660400320867 286413285827838990600481301)
  ·
    refine ⟨13425622773179952684397561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 286413285827838990600481301 13425622773179952684397561)
    ·
      refine ⟨10069217079884964513298171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13425622773179952684397561 10069217079884964513298171)
      ·
        refine ⟨15103825619827446769947257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10069217079884964513298171 15103825619827446769947257)
        ·
          refine ⟨11327869214870585077460443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15103825619827446769947257 11327869214870585077460443)
          ·
            refine ⟨16991803822305877616190665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11327869214870585077460443 16991803822305877616190665)
            ·
              refine ⟨12743852866729408212142999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16991803822305877616190665 12743852866729408212142999)
              ·
                refine ⟨19115779300094112318214499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12743852866729408212142999 19115779300094112318214499)
                ·
                  refine ⟨28673668950141168477321749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19115779300094112318214499 28673668950141168477321749)
                  ·
                    refine ⟨1344078232037867272374457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28673668950141168477321749 1344078232037867272374457)
                    ·
                      rfl

theorem cell23_7852749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_7852749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7852749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7852749 prefixEnd_7852749 := by exact prefixLift 7852749
  have htrace : WordTrace (prefixWord ++ tailWord_7852749) baseStart_7852749 baseEnd_7852749 := by
    simpa [prefixWord, tailWord_7852749, baseEnd_7852749] using wordTrace_append hprefix tailTrace_7852749
  have hstable : (prefixWord ++ tailWord_7852749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7852749).length < 2 ^ (prefixWord ++ tailWord_7852749).sum := by decide
  have hdescent : baseEnd_7852749 < baseStart_7852749 := by decide
  rcases family_descends (prefixWord ++ tailWord_7852749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7852756 : List Nat := [2, 4, 1, 3, 2, 1, 1, 2, 3, 2, 2]
def baseStart_7852756 : Nat := 118140960795 + 7852756 * 2 ^ 59
def prefixEnd_7852756 : Nat := 4983230072969 + 3 ^ 40 * 7852756 * 2
def baseEnd_7852756 : Nat := 4032238290478183289735839

theorem tailTrace_7852756 : CollatzResearch.WordTrace tailWord_7852756 prefixEnd_7852756 4032238290478183289735839 := by
  unfold tailWord_7852756
  simp only [CollatzResearch.WordTrace]
  refine ⟨143206770569406815397993061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190942360759209087197324081 143206770569406815397993061)
  ·
    refine ⟨26851269481763777887123699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 143206770569406815397993061 26851269481763777887123699)
    ·
      refine ⟨40276904222645666830685549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26851269481763777887123699 40276904222645666830685549)
      ·
        refine ⟨15103839083492125061507081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40276904222645666830685549 15103839083492125061507081)
        ·
          refine ⟨11327879312619093796130311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15103839083492125061507081 11327879312619093796130311)
          ·
            refine ⟨16991818968928640694195467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11327879312619093796130311 16991818968928640694195467)
            ·
              refine ⟨25487728453392961041293201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16991818968928640694195467 25487728453392961041293201)
              ·
                refine ⟨19115796340044720780969901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25487728453392961041293201 19115796340044720780969901)
                ·
                  refine ⟨7168423627516770292863713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19115796340044720780969901 7168423627516770292863713)
                  ·
                    refine ⟨5376317720637577719647785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7168423627516770292863713 5376317720637577719647785)
                    ·
                      refine ⟨4032238290478183289735839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5376317720637577719647785 4032238290478183289735839)
                      ·
                        rfl

theorem cell23_7852756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 2, 3, 2, 2].length) (baseStart_7852756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7852756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7852756 prefixEnd_7852756 := by exact prefixLift 7852756
  have htrace : WordTrace (prefixWord ++ tailWord_7852756) baseStart_7852756 baseEnd_7852756 := by
    simpa [prefixWord, tailWord_7852756, baseEnd_7852756] using wordTrace_append hprefix tailTrace_7852756
  have hstable : (prefixWord ++ tailWord_7852756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7852756).length < 2 ^ (prefixWord ++ tailWord_7852756).sum := by decide
  have hdescent : baseEnd_7852756 < baseStart_7852756 := by decide
  rcases family_descends (prefixWord ++ tailWord_7852756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7852768 : List Nat := [2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 5]
def baseStart_7852768 : Nat := 118140960795 + 7852768 * 2 ^ 59
def prefixEnd_7852768 : Nat := 4983230072969 + 3 ^ 40 * 7852768 * 2
def baseEnd_7852768 : Nat := 4032244452246037242785783

theorem tailTrace_7852768 : CollatzResearch.WordTrace tailWord_7852768 prefixEnd_7852768 4032244452246037242785783 := by
  unfold tailWord_7852768
  simp only [CollatzResearch.WordTrace]
  refine ⟨143206989407385078422711479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190942652543180104563615305 143206989407385078422711479)
  ·
    refine ⟨214810484111077617634067219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143206989407385078422711479 214810484111077617634067219)
    ·
      refine ⟨322215726166616426451100829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214810484111077617634067219 322215726166616426451100829)
      ·
        refine ⟨120830897312481159919162811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 322215726166616426451100829 120830897312481159919162811)
        ·
          refine ⟨181246345968721739878744217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120830897312481159919162811 181246345968721739878744217)
          ·
            refine ⟨135934759476541304909058163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181246345968721739878744217 135934759476541304909058163)
            ·
              refine ⟨203902139214811957363587245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135934759476541304909058163 203902139214811957363587245)
              ·
                refine ⟨76463302205554484011345217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 203902139214811957363587245 76463302205554484011345217)
                ·
                  refine ⟨57347476654165863008508913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76463302205554484011345217 57347476654165863008508913)
                  ·
                    refine ⟨43010607490624397256381685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57347476654165863008508913 43010607490624397256381685)
                    ·
                      refine ⟨4032244452246037242785783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43010607490624397256381685 4032244452246037242785783)
                      ·
                        rfl

theorem cell23_7852768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 5].length) (baseStart_7852768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7852768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7852768 prefixEnd_7852768 := by exact prefixLift 7852768
  have htrace : WordTrace (prefixWord ++ tailWord_7852768) baseStart_7852768 baseEnd_7852768 := by
    simpa [prefixWord, tailWord_7852768, baseEnd_7852768] using wordTrace_append hprefix tailTrace_7852768
  have hstable : (prefixWord ++ tailWord_7852768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7852768).length < 2 ^ (prefixWord ++ tailWord_7852768).sum := by decide
  have hdescent : baseEnd_7852768 < baseStart_7852768 := by decide
  rcases family_descends (prefixWord ++ tailWord_7852768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7852776 : List Nat := [2, 1, 4, 1, 4, 2, 2, 1, 1, 2, 3]
def baseStart_7852776 : Nat := 118140960795 + 7852776 * 2 ^ 59
def prefixEnd_7852776 : Nat := 4983230072969 + 3 ^ 40 * 7852776 * 2
def baseEnd_7852776 : Nat := 4032248560091273211485747

theorem tailTrace_7852776 : CollatzResearch.WordTrace tailWord_7852776 prefixEnd_7852776 4032248560091273211485747 := by
  unfold tailWord_7852776
  simp only [CollatzResearch.WordTrace]
  refine ⟨143207135299370587105857091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190942847065827449474476121 143207135299370587105857091)
  ·
    refine ⟨214810702949055880658785637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143207135299370587105857091 214810702949055880658785637)
    ·
      refine ⟨40277006802947977623522307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 214810702949055880658785637 40277006802947977623522307)
      ·
        refine ⟨60415510204421966435283461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40277006802947977623522307 60415510204421966435283461)
        ·
          refine ⟨11327908163329118706615649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60415510204421966435283461 11327908163329118706615649)
          ·
            refine ⟨8495931122496839029961737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11327908163329118706615649 8495931122496839029961737)
            ·
              refine ⟨6371948341872629272471303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8495931122496839029961737 6371948341872629272471303)
              ·
                refine ⟨9557922512808943908706955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6371948341872629272471303 9557922512808943908706955)
                ·
                  refine ⟨14336883769213415863060433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9557922512808943908706955 14336883769213415863060433)
                  ·
                    refine ⟨10752662826910061897295325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14336883769213415863060433 10752662826910061897295325)
                    ·
                      refine ⟨4032248560091273211485747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10752662826910061897295325 4032248560091273211485747)
                      ·
                        rfl

theorem cell23_7852776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 2, 1, 1, 2, 3].length) (baseStart_7852776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7852776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7852776 prefixEnd_7852776 := by exact prefixLift 7852776
  have htrace : WordTrace (prefixWord ++ tailWord_7852776) baseStart_7852776 baseEnd_7852776 := by
    simpa [prefixWord, tailWord_7852776, baseEnd_7852776] using wordTrace_append hprefix tailTrace_7852776
  have hstable : (prefixWord ++ tailWord_7852776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7852776).length < 2 ^ (prefixWord ++ tailWord_7852776).sum := by decide
  have hdescent : baseEnd_7852776 < baseStart_7852776 := by decide
  rcases family_descends (prefixWord ++ tailWord_7852776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7852846 : List Nat := [4, 1, 3, 2, 1, 1, 2, 1, 4, 2, 2]
def baseStart_7852846 : Nat := 118140960795 + 7852846 * 2 ^ 59
def prefixEnd_7852846 : Nat := 4983230072969 + 3 ^ 40 * 7852846 * 2
def baseEnd_7852846 : Nat := 4032284503737087937610425

theorem tailTrace_7852846 : CollatzResearch.WordTrace tailWord_7852846 prefixEnd_7852846 4032284503737087937610425 := by
  unfold tailWord_7852846
  simp only [CollatzResearch.WordTrace]
  refine ⟨35802102963560947020845299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 190944549138991717444508261 35802102963560947020845299)
  ·
    refine ⟨53703154445341420531267949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35802102963560947020845299 53703154445341420531267949)
    ·
      refine ⟨20138682917003032699225481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53703154445341420531267949 20138682917003032699225481)
      ·
        refine ⟨15104012187752274524419111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20138682917003032699225481 15104012187752274524419111)
        ·
          refine ⟨22656018281628411786628667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15104012187752274524419111 22656018281628411786628667)
          ·
            refine ⟨33984027422442617679943001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22656018281628411786628667 33984027422442617679943001)
            ·
              refine ⟨25488020566831963259957251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33984027422442617679943001 25488020566831963259957251)
              ·
                refine ⟨38232030850247944889935877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25488020566831963259957251 38232030850247944889935877)
                ·
                  refine ⟨7168505784421489666862977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38232030850247944889935877 7168505784421489666862977)
                  ·
                    refine ⟨5376379338316117250147233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7168505784421489666862977 5376379338316117250147233)
                    ·
                      refine ⟨4032284503737087937610425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5376379338316117250147233 4032284503737087937610425)
                      ·
                        rfl

theorem cell23_7852846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 1, 4, 2, 2].length) (baseStart_7852846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7852846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7852846 prefixEnd_7852846 := by exact prefixLift 7852846
  have htrace : WordTrace (prefixWord ++ tailWord_7852846) baseStart_7852846 baseEnd_7852846 := by
    simpa [prefixWord, tailWord_7852846, baseEnd_7852846] using wordTrace_append hprefix tailTrace_7852846
  have hstable : (prefixWord ++ tailWord_7852846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7852846).length < 2 ^ (prefixWord ++ tailWord_7852846).sum := by decide
  have hdescent : baseEnd_7852846 < baseStart_7852846 := by decide
  rcases family_descends (prefixWord ++ tailWord_7852846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7852863 : List Nat := [1, 1, 2, 2, 5, 3, 2, 1, 2, 2, 2]
def baseStart_7852863 : Nat := 118140960795 + 7852863 * 2 ^ 59
def prefixEnd_7852863 : Nat := 4983230072969 + 3 ^ 40 * 7852863 * 2
def baseEnd_7852863 : Nat := 4032293232908214371097847

theorem tailTrace_7852863 : CollatzResearch.WordTrace tailWord_7852863 prefixEnd_7852863 4032293232908214371097847 := by
  unfold tailWord_7852863
  simp only [CollatzResearch.WordTrace]
  refine ⟨286417443749425988070131243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190944962499617325380087495 286417443749425988070131243)
  ·
    refine ⟨429626165624138982105196865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286417443749425988070131243 429626165624138982105196865)
    ·
      refine ⟨322219624218104236578897649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 429626165624138982105196865 322219624218104236578897649)
      ·
        refine ⟨241664718163578177434173237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 322219624218104236578897649 241664718163578177434173237)
        ·
          refine ⟨22656067327835454134453741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 241664718163578177434173237 22656067327835454134453741)
          ·
            refine ⟨8496025247938295300420153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22656067327835454134453741 8496025247938295300420153)
            ·
              refine ⟨6372018935953721475315115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8496025247938295300420153 6372018935953721475315115)
              ·
                refine ⟨9558028403930582212972673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6372018935953721475315115 9558028403930582212972673)
                ·
                  refine ⟨7168521302947936659729505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9558028403930582212972673 7168521302947936659729505)
                  ·
                    refine ⟨5376390977210952494797129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7168521302947936659729505 5376390977210952494797129)
                    ·
                      refine ⟨4032293232908214371097847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5376390977210952494797129 4032293232908214371097847)
                      ·
                        rfl

theorem cell23_7852863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 2, 1, 2, 2, 2].length) (baseStart_7852863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7852863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7852863 prefixEnd_7852863 := by exact prefixLift 7852863
  have htrace : WordTrace (prefixWord ++ tailWord_7852863) baseStart_7852863 baseEnd_7852863 := by
    simpa [prefixWord, tailWord_7852863, baseEnd_7852863] using wordTrace_append hprefix tailTrace_7852863
  have hstable : (prefixWord ++ tailWord_7852863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7852863).length < 2 ^ (prefixWord ++ tailWord_7852863).sum := by decide
  have hdescent : baseEnd_7852863 < baseStart_7852863 := by decide
  rcases family_descends (prefixWord ++ tailWord_7852863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7852882 : List Nat := [3, 2, 2, 1, 1, 2, 4, 1, 2, 5]
def baseStart_7852882 : Nat := 118140960795 + 7852882 * 2 ^ 59
def prefixEnd_7852882 : Nat := 4983230072969 + 3 ^ 40 * 7852882 * 2
def baseEnd_7852882 : Nat := 1344100996346883265586753

theorem tailTrace_7852882 : CollatzResearch.WordTrace tailWord_7852882 prefixEnd_7852882 1344100996346883265586753 := by
  unfold tailWord_7852882
  simp only [CollatzResearch.WordTrace]
  refine ⟨71604534184089288578768225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190945424490904769543381933 71604534184089288578768225)
  ·
    refine ⟨53703400638066966434076169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71604534184089288578768225 53703400638066966434076169)
    ·
      refine ⟨40277550478550224825557127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53703400638066966434076169 40277550478550224825557127)
      ·
        refine ⟨60416325717825337238335691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40277550478550224825557127 60416325717825337238335691)
        ·
          refine ⟨90624488576738005857503537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60416325717825337238335691 90624488576738005857503537)
          ·
            refine ⟨67968366432553504393127653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90624488576738005857503537 67968366432553504393127653)
            ·
              refine ⟨12744068706103782073711435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67968366432553504393127653 12744068706103782073711435)
              ·
                refine ⟨19116103059155673110567153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12744068706103782073711435 19116103059155673110567153)
                ·
                  refine ⟨14337077294366754832925365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19116103059155673110567153 14337077294366754832925365)
                  ·
                    refine ⟨1344100996346883265586753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14337077294366754832925365 1344100996346883265586753)
                    ·
                      rfl

theorem cell23_7852882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 4, 1, 2, 5].length) (baseStart_7852882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7852882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7852882 prefixEnd_7852882 := by exact prefixLift 7852882
  have htrace : WordTrace (prefixWord ++ tailWord_7852882) baseStart_7852882 baseEnd_7852882 := by
    simpa [prefixWord, tailWord_7852882, baseEnd_7852882] using wordTrace_append hprefix tailTrace_7852882
  have hstable : (prefixWord ++ tailWord_7852882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7852882).length < 2 ^ (prefixWord ++ tailWord_7852882).sum := by decide
  have hdescent : baseEnd_7852882 < baseStart_7852882 := by decide
  rcases family_descends (prefixWord ++ tailWord_7852882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7852892 : List Nat := [2, 2, 4, 2, 1, 1, 1, 2, 1, 2, 5]
def baseStart_7852892 : Nat := 118140960795 + 7852892 * 2 ^ 59
def prefixEnd_7852892 : Nat := 4983230072969 + 3 ^ 40 * 7852892 * 2
def baseEnd_7852892 : Nat := 4032308123847194757635213

theorem tailTrace_7852892 : CollatzResearch.WordTrace tailWord_7852892 prefixEnd_7852892 4032308123847194757635213 := by
  unfold tailWord_7852892
  simp only [CollatzResearch.WordTrace]
  refine ⟨143209250733160463011468465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190945667644213950681957953 143209250733160463011468465)
  ·
    refine ⟨107406938049870347258601349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143209250733160463011468465 107406938049870347258601349)
    ·
      refine ⟨20138800884350690110987753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107406938049870347258601349 20138800884350690110987753)
      ·
        refine ⟨15104100663263017583240815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20138800884350690110987753 15104100663263017583240815)
        ·
          refine ⟨22656150994894526374861223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15104100663263017583240815 22656150994894526374861223)
          ·
            refine ⟨33984226492341789562291835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22656150994894526374861223 33984226492341789562291835)
            ·
              refine ⟨50976339738512684343437753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33984226492341789562291835 50976339738512684343437753)
              ·
                refine ⟨38232254803884513257578315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50976339738512684343437753 38232254803884513257578315)
                ·
                  refine ⟨57348382205826769886367473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38232254803884513257578315 57348382205826769886367473)
                  ·
                    refine ⟨43011286654370077414775605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57348382205826769886367473 43011286654370077414775605)
                    ·
                      refine ⟨4032308123847194757635213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43011286654370077414775605 4032308123847194757635213)
                      ·
                        rfl

theorem cell23_7852892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_7852892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7852892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7852892 prefixEnd_7852892 := by exact prefixLift 7852892
  have htrace : WordTrace (prefixWord ++ tailWord_7852892) baseStart_7852892 baseEnd_7852892 := by
    simpa [prefixWord, tailWord_7852892, baseEnd_7852892] using wordTrace_append hprefix tailTrace_7852892
  have hstable : (prefixWord ++ tailWord_7852892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7852892).length < 2 ^ (prefixWord ++ tailWord_7852892).sum := by decide
  have hdescent : baseEnd_7852892 < baseStart_7852892 := by decide
  rcases family_descends (prefixWord ++ tailWord_7852892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7852905 : List Nat := [1, 2, 1, 1, 1, 3, 1, 1, 5, 4, 3]
def baseStart_7852905 : Nat := 118140960795 + 7852905 * 2 ^ 59
def prefixEnd_7852905 : Nat := 4983230072969 + 3 ^ 40 * 7852905 * 2
def baseEnd_7852905 : Nat := 4032314799095703206772653

theorem tailTrace_7852905 : CollatzResearch.WordTrace tailWord_7852905 prefixEnd_7852905 4032314799095703206772653 := by
  unfold tailWord_7852905
  simp only [CollatzResearch.WordTrace]
  refine ⟨286418975615273829243160169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190945983743515886162106779 286418975615273829243160169)
  ·
    refine ⟨214814231711455371932370127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286418975615273829243160169 214814231711455371932370127)
    ·
      refine ⟨322221347567183057898555191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214814231711455371932370127 322221347567183057898555191)
      ·
        refine ⟨483332021350774586847832787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322221347567183057898555191 483332021350774586847832787)
        ·
          refine ⟨724998032026161880271749181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 483332021350774586847832787 724998032026161880271749181)
          ·
            refine ⟨271874262009810705101905943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 724998032026161880271749181 271874262009810705101905943)
            ·
              refine ⟨407811393014716057652858915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 271874262009810705101905943 407811393014716057652858915)
              ·
                refine ⟨611717089522074086479288373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 407811393014716057652858915 611717089522074086479288373)
                ·
                  refine ⟨57348477142694445607433285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 611717089522074086479288373 57348477142694445607433285)
                  ·
                    refine ⟨10752839464255208551393741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57348477142694445607433285 10752839464255208551393741)
                    ·
                      refine ⟨4032314799095703206772653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10752839464255208551393741 4032314799095703206772653)
                      ·
                        rfl

theorem cell23_7852905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 5, 4, 3].length) (baseStart_7852905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7852905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7852905 prefixEnd_7852905 := by exact prefixLift 7852905
  have htrace : WordTrace (prefixWord ++ tailWord_7852905) baseStart_7852905 baseEnd_7852905 := by
    simpa [prefixWord, tailWord_7852905, baseEnd_7852905] using wordTrace_append hprefix tailTrace_7852905
  have hstable : (prefixWord ++ tailWord_7852905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7852905).length < 2 ^ (prefixWord ++ tailWord_7852905).sum := by decide
  have hdescent : baseEnd_7852905 < baseStart_7852905 := by decide
  rcases family_descends (prefixWord ++ tailWord_7852905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7852959 : List Nat := [1, 1, 2, 5, 2, 3, 1, 2, 6]
def baseStart_7852959 : Nat := 118140960795 + 7852959 * 2 ^ 59
def prefixEnd_7852959 : Nat := 4983230072969 + 3 ^ 40 * 7852959 * 2
def baseEnd_7852959 : Nat := 448038058561227332833045

theorem tailTrace_7852959 : CollatzResearch.WordTrace tailWord_7852959 prefixEnd_7852959 448038058561227332833045 := by
  unfold tailWord_7852959
  simp only [CollatzResearch.WordTrace]
  refine ⟨286420945157078196465625931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190947296771385464310417287 286420945157078196465625931)
  ·
    refine ⟨429631417735617294698438897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286420945157078196465625931 429631417735617294698438897)
    ·
      refine ⟨322223563301712971023829173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 429631417735617294698438897 322223563301712971023829173)
      ·
        refine ⟨30208459059535591033483985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 322223563301712971023829173 30208459059535591033483985)
        ·
          refine ⟨22656344294651693275112989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30208459059535591033483985 22656344294651693275112989)
          ·
            refine ⟨8496129110494384978167371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22656344294651693275112989 8496129110494384978167371)
            ·
              refine ⟨12744193665741577467251057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8496129110494384978167371 12744193665741577467251057)
              ·
                refine ⟨9558145249306183100438293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12744193665741577467251057 9558145249306183100438293)
                ·
                  refine ⟨448038058561227332833045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9558145249306183100438293 448038058561227332833045)
                  ·
                    rfl

theorem cell23_7852959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 1, 2, 6].length) (baseStart_7852959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7852959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7852959 prefixEnd_7852959 := by exact prefixLift 7852959
  have htrace : WordTrace (prefixWord ++ tailWord_7852959) baseStart_7852959 baseEnd_7852959 := by
    simpa [prefixWord, tailWord_7852959, baseEnd_7852959] using wordTrace_append hprefix tailTrace_7852959
  have hstable : (prefixWord ++ tailWord_7852959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7852959).length < 2 ^ (prefixWord ++ tailWord_7852959).sum := by decide
  have hdescent : baseEnd_7852959 < baseStart_7852959 := by decide
  rcases family_descends (prefixWord ++ tailWord_7852959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7852962 : List Nat := [3, 3, 1, 2, 2, 1, 1, 1, 1, 2, 6]
def baseStart_7852962 : Nat := 118140960795 + 7852962 * 2 ^ 59
def prefixEnd_7852962 : Nat := 4983230072969 + 3 ^ 40 * 7852962 * 2
def baseEnd_7852962 : Nat := 4032344067493009483759891

theorem tailTrace_7852962 : CollatzResearch.WordTrace tailWord_7852962 prefixEnd_7852962 4032344067493009483759891 := by
  unfold tailWord_7852962
  simp only [CollatzResearch.WordTrace]
  refine ⟨71605263644016831994496285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190947369717378218651990093 71605263644016831994496285)
  ·
    refine ⟨26851973866506311997936107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71605263644016831994496285 26851973866506311997936107)
    ·
      refine ⟨40277960799759467996904161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26851973866506311997936107 40277960799759467996904161)
      ·
        refine ⟨30208470599819600997678121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40277960799759467996904161 30208470599819600997678121)
        ·
          refine ⟨22656352949864700748258591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30208470599819600997678121 22656352949864700748258591)
          ·
            refine ⟨33984529424797051122387887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22656352949864700748258591 33984529424797051122387887)
            ·
              refine ⟨50976794137195576683581831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33984529424797051122387887 50976794137195576683581831)
              ·
                refine ⟨76465191205793365025372747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50976794137195576683581831 76465191205793365025372747)
                ·
                  refine ⟨114697786808690047538059121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76465191205793365025372747 114697786808690047538059121)
                  ·
                    refine ⟨86023340106517535653544341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 114697786808690047538059121 86023340106517535653544341)
                    ·
                      refine ⟨4032344067493009483759891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86023340106517535653544341 4032344067493009483759891)
                      ·
                        rfl

theorem cell23_7852962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_7852962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7852962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7852962 prefixEnd_7852962 := by exact prefixLift 7852962
  have htrace : WordTrace (prefixWord ++ tailWord_7852962) baseStart_7852962 baseEnd_7852962 := by
    simpa [prefixWord, tailWord_7852962, baseEnd_7852962] using wordTrace_append hprefix tailTrace_7852962
  have hstable : (prefixWord ++ tailWord_7852962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7852962).length < 2 ^ (prefixWord ++ tailWord_7852962).sum := by decide
  have hdescent : baseEnd_7852962 < baseStart_7852962 := by decide
  rcases family_descends (prefixWord ++ tailWord_7852962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7852969 : List Nat := [1, 2, 1, 1, 1, 1, 8, 1, 3, 1, 3]
def baseStart_7852969 : Nat := 118140960795 + 7852969 * 2 ^ 59
def prefixEnd_7852969 : Nat := 4983230072969 + 3 ^ 40 * 7852969 * 2
def baseEnd_7852969 : Nat := 4032347661857590956372359

theorem tailTrace_7852969 : CollatzResearch.WordTrace tailWord_7852969 prefixEnd_7852969 4032347661857590956372359 := by
  unfold tailWord_7852969
  simp only [CollatzResearch.WordTrace]
  refine ⟨286421309887041968173489961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190947539924694645448993307 286421309887041968173489961)
  ·
    refine ⟨214815982415281476130117471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286421309887041968173489961 214815982415281476130117471)
    ·
      refine ⟨322223973622922214195176207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214815982415281476130117471 322223973622922214195176207)
      ·
        refine ⟨483335960434383321292764311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322223973622922214195176207 483335960434383321292764311)
        ·
          refine ⟨725003940651574981939146467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 483335960434383321292764311 725003940651574981939146467)
          ·
            refine ⟨1087505910977362472908719701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 725003940651574981939146467 1087505910977362472908719701)
            ·
              refine ⟨12744209894265966479399059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1087505910977362472908719701 12744209894265966479399059)
              ·
                refine ⟨19116314841398949719098589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12744209894265966479399059 19116314841398949719098589)
                ·
                  refine ⟨7168618065524606144661971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19116314841398949719098589 7168618065524606144661971)
                  ·
                    refine ⟨10752927098286909216992957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7168618065524606144661971 10752927098286909216992957)
                    ·
                      refine ⟨4032347661857590956372359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10752927098286909216992957 4032347661857590956372359)
                      ·
                        rfl

theorem cell23_7852969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 8, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 8, 1, 3, 1, 3].length) (baseStart_7852969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7852969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7852969 prefixEnd_7852969 := by exact prefixLift 7852969
  have htrace : WordTrace (prefixWord ++ tailWord_7852969) baseStart_7852969 baseEnd_7852969 := by
    simpa [prefixWord, tailWord_7852969, baseEnd_7852969] using wordTrace_append hprefix tailTrace_7852969
  have hstable : (prefixWord ++ tailWord_7852969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7852969).length < 2 ^ (prefixWord ++ tailWord_7852969).sum := by decide
  have hdescent : baseEnd_7852969 < baseStart_7852969 := by decide
  rcases family_descends (prefixWord ++ tailWord_7852969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7852975 : List Nat := [1, 1, 2, 1, 2, 2, 2, 1, 2, 5, 4]
def baseStart_7852975 : Nat := 118140960795 + 7852975 * 2 ^ 59
def prefixEnd_7852975 : Nat := 4983230072969 + 3 ^ 40 * 7852975 * 2
def baseEnd_7852975 : Nat := 4032350742741517932897331

theorem tailTrace_7852975 : CollatzResearch.WordTrace tailWord_7852975 prefixEnd_7852975 4032350742741517932897331 := by
  unfold tailWord_7852975
  simp only [CollatzResearch.WordTrace]
  refine ⟨286421528725020231198208379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190947685816680154132138919 286421528725020231198208379)
  ·
    refine ⟨429632293087530346797312569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286421528725020231198208379 429632293087530346797312569)
    ·
      refine ⟨322224219815647760097984427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 429632293087530346797312569 322224219815647760097984427)
      ·
        refine ⟨483336329723471640146976641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322224219815647760097984427 483336329723471640146976641)
        ·
          refine ⟨362502247292603730110232481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 483336329723471640146976641 362502247292603730110232481)
          ·
            refine ⟨271876685469452797582674361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 362502247292603730110232481 271876685469452797582674361)
            ·
              refine ⟨203907514102089598187005771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 271876685469452797582674361 203907514102089598187005771)
              ·
                refine ⟨305861271153134397280508657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 203907514102089598187005771 305861271153134397280508657)
                ·
                  refine ⟨229395953364850797960381493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 305861271153134397280508657 229395953364850797960381493)
                  ·
                    refine ⟨21505870627954762308785765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 229395953364850797960381493 21505870627954762308785765)
                    ·
                      refine ⟨4032350742741517932897331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21505870627954762308785765 4032350742741517932897331)
                      ·
                        rfl

theorem cell23_7852975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 5, 4].length) (baseStart_7852975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7852975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7852975 prefixEnd_7852975 := by exact prefixLift 7852975
  have htrace : WordTrace (prefixWord ++ tailWord_7852975) baseStart_7852975 baseEnd_7852975 := by
    simpa [prefixWord, tailWord_7852975, baseEnd_7852975] using wordTrace_append hprefix tailTrace_7852975
  have hstable : (prefixWord ++ tailWord_7852975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7852975).length < 2 ^ (prefixWord ++ tailWord_7852975).sum := by decide
  have hdescent : baseEnd_7852975 < baseStart_7852975 := by decide
  rcases family_descends (prefixWord ++ tailWord_7852975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7853003 : List Nat := [1, 1, 1, 1, 3, 7, 1, 3, 1, 1, 3]
def baseStart_7853003 : Nat := 118140960795 + 7853003 * 2 ^ 59
def prefixEnd_7853003 : Nat := 4983230072969 + 3 ^ 40 * 7853003 * 2
def baseEnd_7853003 : Nat := 4032365120199843823347203

theorem tailTrace_7853003 : CollatzResearch.WordTrace tailWord_7853003 prefixEnd_7853003 4032365120199843823347203 := by
  unfold tailWord_7853003
  simp only [CollatzResearch.WordTrace]
  refine ⟨286422549968918791980227663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190948366645945861320151775 286422549968918791980227663)
  ·
    refine ⟨429633824953378187970341495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286422549968918791980227663 429633824953378187970341495)
    ·
      refine ⟨644450737430067281955512243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 429633824953378187970341495 644450737430067281955512243)
      ·
        refine ⟨966676106145100922933268365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 644450737430067281955512243 966676106145100922933268365)
        ·
          refine ⟨362503539804412846099975637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 966676106145100922933268365 362503539804412846099975637)
          ·
            refine ⟨8496176714165926080468179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 362503539804412846099975637 8496176714165926080468179)
            ·
              refine ⟨12744265071248889120702269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8496176714165926080468179 12744265071248889120702269)
              ·
                refine ⟨4779099401718333420263351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12744265071248889120702269 4779099401718333420263351)
                ·
                  refine ⟨7168649102577500130395027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4779099401718333420263351 7168649102577500130395027)
                  ·
                    refine ⟨10752973653866250195592541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7168649102577500130395027 10752973653866250195592541)
                    ·
                      refine ⟨4032365120199843823347203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10752973653866250195592541 4032365120199843823347203)
                      ·
                        rfl

theorem cell23_7853003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 1, 3, 1, 1, 3].length) (baseStart_7853003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7853003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7853003 prefixEnd_7853003 := by exact prefixLift 7853003
  have htrace : WordTrace (prefixWord ++ tailWord_7853003) baseStart_7853003 baseEnd_7853003 := by
    simpa [prefixWord, tailWord_7853003, baseEnd_7853003] using wordTrace_append hprefix tailTrace_7853003
  have hstable : (prefixWord ++ tailWord_7853003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7853003).length < 2 ^ (prefixWord ++ tailWord_7853003).sum := by decide
  have hdescent : baseEnd_7853003 < baseStart_7853003 := by decide
  rcases family_descends (prefixWord ++ tailWord_7853003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7853046 : List Nat := [5, 1, 1, 1, 3, 2, 1, 1, 3, 2, 3]
def baseStart_7853046 : Nat := 118140960795 + 7853046 * 2 ^ 59
def prefixEnd_7853046 : Nat := 4983230072969 + 3 ^ 40 * 7853046 * 2
def baseEnd_7853046 : Nat := 4032387199867987155109505

theorem tailTrace_7853046 : CollatzResearch.WordTrace tailWord_7853046 prefixEnd_7853046 4032387199867987155109505 := by
  unfold tailWord_7853046
  simp only [CollatzResearch.WordTrace]
  refine ⟨17901507394235188145252687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 190949412205175340216028661 17901507394235188145252687)
  ·
    refine ⟨26852261091352782217879031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17901507394235188145252687 26852261091352782217879031)
    ·
      refine ⟨40278391637029173326818547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26852261091352782217879031 40278391637029173326818547)
      ·
        refine ⟨60417587455543759990227821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40278391637029173326818547 60417587455543759990227821)
        ·
          refine ⟨22656595295828909996335433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60417587455543759990227821 22656595295828909996335433)
          ·
            refine ⟨16992446471871682497251575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22656595295828909996335433 16992446471871682497251575)
            ·
              refine ⟨25488669707807523745877363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16992446471871682497251575 25488669707807523745877363)
              ·
                refine ⟨38233004561711285618816045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25488669707807523745877363 38233004561711285618816045)
                ·
                  refine ⟨14337376710641732107056017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38233004561711285618816045 14337376710641732107056017)
                  ·
                    refine ⟨10753032532981299080292013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14337376710641732107056017 10753032532981299080292013)
                    ·
                      refine ⟨4032387199867987155109505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10753032532981299080292013 4032387199867987155109505)
                      ·
                        rfl

theorem cell23_7853046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 1, 3, 2, 3].length) (baseStart_7853046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7853046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7853046 prefixEnd_7853046 := by exact prefixLift 7853046
  have htrace : WordTrace (prefixWord ++ tailWord_7853046) baseStart_7853046 baseEnd_7853046 := by
    simpa [prefixWord, tailWord_7853046, baseEnd_7853046] using wordTrace_append hprefix tailTrace_7853046
  have hstable : (prefixWord ++ tailWord_7853046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7853046).length < 2 ^ (prefixWord ++ tailWord_7853046).sum := by decide
  have hdescent : baseEnd_7853046 < baseStart_7853046 := by decide
  rcases family_descends (prefixWord ++ tailWord_7853046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7853077 : List Nat := [1, 3, 2, 1, 4, 3, 2, 2, 1, 2, 2]
def baseStart_7853077 : Nat := 118140960795 + 7853077 * 2 ^ 59
def prefixEnd_7853077 : Nat := 4983230072969 + 3 ^ 40 * 7853077 * 2
def baseEnd_7853077 : Nat := 4032403117768276533821863

theorem tailTrace_7853077 : CollatzResearch.WordTrace tailWord_7853077 prefixEnd_7853077 4032403117768276533821863 := by
  unfold tailWord_7853077
  simp only [CollatzResearch.WordTrace]
  refine ⟨286425248970650702618421485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190950165980433801745614323 286425248970650702618421485)
  ·
    refine ⟨107409468363994013481908057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 286425248970650702618421485 107409468363994013481908057)
    ·
      refine ⟨80557101272995510111431043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107409468363994013481908057 80557101272995510111431043)
      ·
        refine ⟨120835651909493265167146565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80557101272995510111431043 120835651909493265167146565)
        ·
          refine ⟨22656684733029987218839981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 120835651909493265167146565 22656684733029987218839981)
          ·
            refine ⟨8496256774886245207064993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22656684733029987218839981 8496256774886245207064993)
            ·
              refine ⟨6372192581164683905298745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8496256774886245207064993 6372192581164683905298745)
              ·
                refine ⟨4779144435873512928974059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6372192581164683905298745 4779144435873512928974059)
                ·
                  refine ⟨7168716653810269393461089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4779144435873512928974059 7168716653810269393461089)
                  ·
                    refine ⟨5376537490357702045095817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7168716653810269393461089 5376537490357702045095817)
                    ·
                      refine ⟨4032403117768276533821863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5376537490357702045095817 4032403117768276533821863)
                      ·
                        rfl

theorem cell23_7853077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 2, 2, 1, 2, 2].length) (baseStart_7853077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7853077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7853077 prefixEnd_7853077 := by exact prefixLift 7853077
  have htrace : WordTrace (prefixWord ++ tailWord_7853077) baseStart_7853077 baseEnd_7853077 := by
    simpa [prefixWord, tailWord_7853077, baseEnd_7853077] using wordTrace_append hprefix tailTrace_7853077
  have hstable : (prefixWord ++ tailWord_7853077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7853077).length < 2 ^ (prefixWord ++ tailWord_7853077).sum := by decide
  have hdescent : baseEnd_7853077 < baseStart_7853077 := by decide
  rcases family_descends (prefixWord ++ tailWord_7853077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7853082 : List Nat := [3, 1, 1, 3, 1, 2, 1, 1, 1, 5, 4]
def baseStart_7853082 : Nat := 118140960795 + 7853082 * 2 ^ 59
def prefixEnd_7853082 : Nat := 4983230072969 + 3 ^ 40 * 7853082 * 2
def baseEnd_7853082 : Nat := 4032405685171549014259339

theorem tailTrace_7853082 : CollatzResearch.WordTrace tailWord_7853082 prefixEnd_7853082 4032405685171549014259339 := by
  unfold tailWord_7853082
  simp only [CollatzResearch.WordTrace]
  refine ⟨71606357833908147118088375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190950287557088392314902333 71606357833908147118088375)
  ·
    refine ⟨107409536750862220677132563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71606357833908147118088375 107409536750862220677132563)
    ·
      refine ⟨161114305126293331015698845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107409536750862220677132563 161114305126293331015698845)
      ·
        refine ⟨60417864422359999130887067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161114305126293331015698845 60417864422359999130887067)
        ·
          refine ⟨90626796633539998696330601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60417864422359999130887067 90626796633539998696330601)
          ·
            refine ⟨67970097475154999022247951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90626796633539998696330601 67970097475154999022247951)
            ·
              refine ⟨101955146212732498533371927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67970097475154999022247951 101955146212732498533371927)
              ·
                refine ⟨152932719319098747800057891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101955146212732498533371927 152932719319098747800057891)
                ·
                  refine ⟨229399078978648121700086837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 152932719319098747800057891 229399078978648121700086837)
                  ·
                    refine ⟨21506163654248261409383141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 229399078978648121700086837 21506163654248261409383141)
                    ·
                      refine ⟨4032405685171549014259339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21506163654248261409383141 4032405685171549014259339)
                      ·
                        rfl

theorem cell23_7853082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 1, 5, 4].length) (baseStart_7853082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7853082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7853082 prefixEnd_7853082 := by exact prefixLift 7853082
  have htrace : WordTrace (prefixWord ++ tailWord_7853082) baseStart_7853082 baseEnd_7853082 := by
    simpa [prefixWord, tailWord_7853082, baseEnd_7853082] using wordTrace_append hprefix tailTrace_7853082
  have hstable : (prefixWord ++ tailWord_7853082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7853082).length < 2 ^ (prefixWord ++ tailWord_7853082).sum := by decide
  have hdescent : baseEnd_7853082 < baseStart_7853082 := by decide
  rcases family_descends (prefixWord ++ tailWord_7853082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7853116 : List Nat := [2, 2, 2, 2, 2, 2, 2, 2, 1, 4, 2]
def baseStart_7853116 : Nat := 118140960795 + 7853116 * 2 ^ 59
def prefixEnd_7853116 : Nat := 4983230072969 + 3 ^ 40 * 7853116 * 2
def baseEnd_7853116 : Nat := 4032423143513801881234183

theorem tailTrace_7853116 : CollatzResearch.WordTrace tailWord_7853116 prefixEnd_7853116 4032423143513801881234183 := by
  unfold tailWord_7853116
  simp only [CollatzResearch.WordTrace]
  refine ⟨143213335708754706139545601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190951114278339608186060801 143213335708754706139545601)
  ·
    refine ⟨107410001781566029604659201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143213335708754706139545601 107410001781566029604659201)
    ·
      refine ⟨80557501336174522203494401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107410001781566029604659201 80557501336174522203494401)
      ·
        refine ⟨60418126002130891652620801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80557501336174522203494401 60418126002130891652620801)
        ·
          refine ⟨45313594501598168739465601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60418126002130891652620801 45313594501598168739465601)
          ·
            refine ⟨33985195876198626554599201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45313594501598168739465601 33985195876198626554599201)
            ·
              refine ⟨25488896907148969915949401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33985195876198626554599201 25488896907148969915949401)
              ·
                refine ⟨19116672680361727436962051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25488896907148969915949401 19116672680361727436962051)
                ·
                  refine ⟨28675009020542591155443077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19116672680361727436962051 28675009020542591155443077)
                  ·
                    refine ⟨5376564191351735841645577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28675009020542591155443077 5376564191351735841645577)
                    ·
                      refine ⟨4032423143513801881234183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5376564191351735841645577 4032423143513801881234183)
                      ·
                        rfl

theorem cell23_7853116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 1, 4, 2].length) (baseStart_7853116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7853116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7853116 prefixEnd_7853116 := by exact prefixLift 7853116
  have htrace : WordTrace (prefixWord ++ tailWord_7853116) baseStart_7853116 baseEnd_7853116 := by
    simpa [prefixWord, tailWord_7853116, baseEnd_7853116] using wordTrace_append hprefix tailTrace_7853116
  have hstable : (prefixWord ++ tailWord_7853116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7853116).length < 2 ^ (prefixWord ++ tailWord_7853116).sum := by decide
  have hdescent : baseEnd_7853116 < baseStart_7853116 := by decide
  rcases family_descends (prefixWord ++ tailWord_7853116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7853126 : List Nat := [6, 1, 1, 1, 1, 2, 1, 2, 2, 6]
def baseStart_7853126 : Nat := 118140960795 + 7853126 * 2 ^ 59
def prefixEnd_7853126 : Nat := 4983230072969 + 3 ^ 40 * 7853126 * 2
def baseEnd_7853126 : Nat := 1344142759440115614036379

theorem tailTrace_7853126 : CollatzResearch.WordTrace tailWord_7853126 prefixEnd_7853126 1344142759440115614036379 := by
  unfold tailWord_7853126
  simp only [CollatzResearch.WordTrace]
  refine ⟨8950844879608536999592351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 190951357431648789324636821 8950844879608536999592351)
  ·
    refine ⟨13426267319412805499388527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8950844879608536999592351 13426267319412805499388527)
    ·
      refine ⟨20139400979119208249082791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13426267319412805499388527 20139400979119208249082791)
      ·
        refine ⟨30209101468678812373624187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20139400979119208249082791 30209101468678812373624187)
        ·
          refine ⟨45313652203018218560436281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30209101468678812373624187 45313652203018218560436281)
          ·
            refine ⟨33985239152263663920327211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45313652203018218560436281 33985239152263663920327211)
            ·
              refine ⟨50977858728395495880490817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33985239152263663920327211 50977858728395495880490817)
              ·
                refine ⟨38233394046296621910368113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50977858728395495880490817 38233394046296621910368113)
                ·
                  refine ⟨28675045534722466432776085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38233394046296621910368113 28675045534722466432776085)
                  ·
                    refine ⟨1344142759440115614036379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28675045534722466432776085 1344142759440115614036379)
                    ·
                      rfl

theorem cell23_7853126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 2, 2, 6].length) (baseStart_7853126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7853126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7853126 prefixEnd_7853126 := by exact prefixLift 7853126
  have htrace : WordTrace (prefixWord ++ tailWord_7853126) baseStart_7853126 baseEnd_7853126 := by
    simpa [prefixWord, tailWord_7853126, baseEnd_7853126] using wordTrace_append hprefix tailTrace_7853126
  have hstable : (prefixWord ++ tailWord_7853126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7853126).length < 2 ^ (prefixWord ++ tailWord_7853126).sum := by decide
  have hdescent : baseEnd_7853126 < baseStart_7853126 := by decide
  rcases family_descends (prefixWord ++ tailWord_7853126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7853152 : List Nat := [2, 1, 1, 3, 2, 2, 1, 1, 3, 7]
def baseStart_7853152 : Nat := 118140960795 + 7853152 * 2 ^ 59
def prefixEnd_7853152 : Nat := 4983230072969 + 3 ^ 40 * 7853152 * 2
def baseEnd_7853152 : Nat := 1344147209605787913461339

theorem tailTrace_7853152 : CollatzResearch.WordTrace tailWord_7853152 prefixEnd_7853152 1344147209605787913461339 := by
  unfold tailWord_7853152
  simp only [CollatzResearch.WordTrace]
  refine ⟨143213992222689495213700855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190951989630252660284934473 143213992222689495213700855)
  ·
    refine ⟨214820988334034242820551283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143213992222689495213700855 214820988334034242820551283)
    ·
      refine ⟨322231482501051364230826925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214820988334034242820551283 322231482501051364230826925)
      ·
        refine ⟨120836805937894261586560097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 322231482501051364230826925 120836805937894261586560097)
        ·
          refine ⟨90627604453420696189920073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120836805937894261586560097 90627604453420696189920073)
          ·
            refine ⟨67970703340065522142440055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90627604453420696189920073 67970703340065522142440055)
            ·
              refine ⟨101956055010098283213660083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67970703340065522142440055 101956055010098283213660083)
              ·
                refine ⟨152934082515147424820490125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101956055010098283213660083 152934082515147424820490125)
                ·
                  refine ⟨57350280943180284307683797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 152934082515147424820490125 57350280943180284307683797)
                  ·
                    refine ⟨1344147209605787913461339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57350280943180284307683797 1344147209605787913461339)
                    ·
                      rfl

theorem cell23_7853152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 1, 3, 7].length) (baseStart_7853152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7853152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7853152 prefixEnd_7853152 := by exact prefixLift 7853152
  have htrace : WordTrace (prefixWord ++ tailWord_7853152) baseStart_7853152 baseEnd_7853152 := by
    simpa [prefixWord, tailWord_7853152, baseEnd_7853152] using wordTrace_append hprefix tailTrace_7853152
  have hstable : (prefixWord ++ tailWord_7853152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7853152).length < 2 ^ (prefixWord ++ tailWord_7853152).sum := by decide
  have hdescent : baseEnd_7853152 < baseStart_7853152 := by decide
  rcases family_descends (prefixWord ++ tailWord_7853152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7853223 : List Nat := [1, 1, 6, 2, 1, 2, 2, 1, 2, 1, 4]
def baseStart_7853223 : Nat := 118140960795 + 7853223 * 2 ^ 59
def prefixEnd_7853223 : Nat := 4983230072969 + 3 ^ 40 * 7853223 * 2
def baseEnd_7853223 : Nat := 4032478085943832962596191

theorem tailTrace_7853223 : CollatzResearch.WordTrace tailWord_7853223 prefixEnd_7853223 4032478085943832962596191 := by
  unfold tailWord_7853223
  simp only [CollatzResearch.WordTrace]
  refine ⟨286430574028121769553236323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190953716018747846368824215 286430574028121769553236323)
  ·
    refine ⟨429645861042182654329854485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286430574028121769553236323 429645861042182654329854485)
    ·
      refine ⟨20139649736352311921711929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 429645861042182654329854485 20139649736352311921711929)
      ·
        refine ⟨15104737302264233941283947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20139649736352311921711929 15104737302264233941283947)
        ·
          refine ⟨22657105953396350911925921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15104737302264233941283947 22657105953396350911925921)
          ·
            refine ⟨16992829465047263183944441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22657105953396350911925921 16992829465047263183944441)
            ·
              refine ⟨12744622098785447387958331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16992829465047263183944441 12744622098785447387958331)
              ·
                refine ⟨19116933148178171081937497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12744622098785447387958331 19116933148178171081937497)
                ·
                  refine ⟨14337699861133628311453123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19116933148178171081937497 14337699861133628311453123)
                  ·
                    refine ⟨21506549791700442467179685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14337699861133628311453123 21506549791700442467179685)
                    ·
                      refine ⟨4032478085943832962596191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21506549791700442467179685 4032478085943832962596191)
                      ·
                        rfl

theorem cell23_7853223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_7853223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7853223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7853223 prefixEnd_7853223 := by exact prefixLift 7853223
  have htrace : WordTrace (prefixWord ++ tailWord_7853223) baseStart_7853223 baseEnd_7853223 := by
    simpa [prefixWord, tailWord_7853223, baseEnd_7853223] using wordTrace_append hprefix tailTrace_7853223
  have hstable : (prefixWord ++ tailWord_7853223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7853223).length < 2 ^ (prefixWord ++ tailWord_7853223).sum := by decide
  have hdescent : baseEnd_7853223 < baseStart_7853223 := by decide
  rcases family_descends (prefixWord ++ tailWord_7853223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7853246 : List Nat := [4, 2, 1, 1, 3, 1, 1, 4, 6]
def baseStart_7853246 : Nat := 118140960795 + 7853246 * 2 ^ 59
def prefixEnd_7853246 : Nat := 4983230072969 + 3 ^ 40 * 7853246 * 2
def baseEnd_7853246 : Nat := 448054432888765152512065

theorem tailTrace_7853246 : CollatzResearch.WordTrace tailWord_7853246 prefixEnd_7853246 448054432888765152512065 := by
  unfold tailWord_7853246
  simp only [CollatzResearch.WordTrace]
  refine ⟨35803926613379805560165449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 190954275271358962987549061 35803926613379805560165449)
  ·
    refine ⟨26852944960034854170124087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35803926613379805560165449 26852944960034854170124087)
    ·
      refine ⟨40279417440052281255186131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26852944960034854170124087 40279417440052281255186131)
      ·
        refine ⟨60419126160078421882779197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40279417440052281255186131 60419126160078421882779197)
        ·
          refine ⟨22657172310029408206042199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60419126160078421882779197 22657172310029408206042199)
          ·
            refine ⟨33985758465044112309063299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22657172310029408206042199 33985758465044112309063299)
            ·
              refine ⟨50978637697566168463594949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33985758465044112309063299 50978637697566168463594949)
              ·
                refine ⟨9558494568293656586924053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50978637697566168463594949 9558494568293656586924053)
                ·
                  refine ⟨448054432888765152512065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9558494568293656586924053 448054432888765152512065)
                  ·
                    rfl

theorem cell23_7853246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 4, 6].length) (baseStart_7853246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7853246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7853246 prefixEnd_7853246 := by exact prefixLift 7853246
  have htrace : WordTrace (prefixWord ++ tailWord_7853246) baseStart_7853246 baseEnd_7853246 := by
    simpa [prefixWord, tailWord_7853246, baseEnd_7853246] using wordTrace_append hprefix tailTrace_7853246
  have hstable : (prefixWord ++ tailWord_7853246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7853246).length < 2 ^ (prefixWord ++ tailWord_7853246).sum := by decide
  have hdescent : baseEnd_7853246 < baseStart_7853246 := by decide
  rcases family_descends (prefixWord ++ tailWord_7853246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7853277 : List Nat := [1, 4, 3, 2, 3, 1, 1, 1, 2, 2, 3]
def baseStart_7853277 : Nat := 118140960795 + 7853277 * 2 ^ 59
def prefixEnd_7853277 : Nat := 4983230072969 + 3 ^ 40 * 7853277 * 2
def baseEnd_7853277 : Nat := 4032505813899175751320943

theorem tailTrace_7853277 : CollatzResearch.WordTrace tailWord_7853277 prefixEnd_7853277 4032505813899175751320943 := by
  unfold tailWord_7853277
  simp only [CollatzResearch.WordTrace]
  refine ⟨286432543569926136775702085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190955029046617424517134723 286432543569926136775702085)
  ·
    refine ⟨53706101919361150645444141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 286432543569926136775702085 53706101919361150645444141)
    ·
      refine ⟨20139788219760431492041553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53706101919361150645444141 20139788219760431492041553)
      ·
        refine ⟨15104841164820323619031165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20139788219760431492041553 15104841164820323619031165)
        ·
          refine ⟨5664315436807621357136687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15104841164820323619031165 5664315436807621357136687)
          ·
            refine ⟨8496473155211432035705031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5664315436807621357136687 8496473155211432035705031)
            ·
              refine ⟨12744709732817148053557547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8496473155211432035705031 12744709732817148053557547)
              ·
                refine ⟨19117064599225722080336321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12744709732817148053557547 19117064599225722080336321)
                ·
                  refine ⟨14337798449419291560252241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19117064599225722080336321 14337798449419291560252241)
                  ·
                    refine ⟨10753348837064468670189181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14337798449419291560252241 10753348837064468670189181)
                    ·
                      refine ⟨4032505813899175751320943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10753348837064468670189181 4032505813899175751320943)
                      ·
                        rfl

theorem cell23_7853277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 1, 1, 2, 2, 3].length) (baseStart_7853277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7853277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7853277 prefixEnd_7853277 := by exact prefixLift 7853277
  have htrace : WordTrace (prefixWord ++ tailWord_7853277) baseStart_7853277 baseEnd_7853277 := by
    simpa [prefixWord, tailWord_7853277, baseEnd_7853277] using wordTrace_append hprefix tailTrace_7853277
  have hstable : (prefixWord ++ tailWord_7853277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7853277).length < 2 ^ (prefixWord ++ tailWord_7853277).sum := by decide
  have hdescent : baseEnd_7853277 < baseStart_7853277 := by decide
  rcases family_descends (prefixWord ++ tailWord_7853277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7853290 : List Nat := [3, 1, 3, 1, 1, 3, 1, 5, 1, 1, 3]
def baseStart_7853290 : Nat := 118140960795 + 7853290 * 2 ^ 59
def prefixEnd_7853290 : Nat := 4983230072969 + 3 ^ 40 * 7853290 * 2
def baseEnd_7853290 : Nat := 4032512489147684200458383

theorem tailTrace_7853290 : CollatzResearch.WordTrace tailWord_7853290 prefixEnd_7853290 4032512489147684200458383 := by
  unfold tailWord_7853290
  simp only [CollatzResearch.WordTrace]
  refine ⟨71608254429719759998981331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190955345145919359997283549 71608254429719759998981331)
  ·
    refine ⟨107412381644579639998471997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71608254429719759998981331 107412381644579639998471997)
    ·
      refine ⟨40279643116717364999426999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107412381644579639998471997 40279643116717364999426999)
      ·
        refine ⟨60419464675076047499140499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40279643116717364999426999 60419464675076047499140499)
        ·
          refine ⟨90629197012614071248710749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60419464675076047499140499 90629197012614071248710749)
          ·
            refine ⟨33985948879730276718266531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90629197012614071248710749 33985948879730276718266531)
            ·
              refine ⟨50978923319595415077399797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33985948879730276718266531 50978923319595415077399797)
              ·
                refine ⟨4779274061212070163506231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50978923319595415077399797 4779274061212070163506231)
                ·
                  refine ⟨7168911091818105245259347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4779274061212070163506231 7168911091818105245259347)
                  ·
                    refine ⟨10753366637727157867889021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7168911091818105245259347 10753366637727157867889021)
                    ·
                      refine ⟨4032512489147684200458383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10753366637727157867889021 4032512489147684200458383)
                      ·
                        rfl

theorem cell23_7853290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 5, 1, 1, 3].length) (baseStart_7853290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7853290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7853290 prefixEnd_7853290 := by exact prefixLift 7853290
  have htrace : WordTrace (prefixWord ++ tailWord_7853290) baseStart_7853290 baseEnd_7853290 := by
    simpa [prefixWord, tailWord_7853290, baseEnd_7853290] using wordTrace_append hprefix tailTrace_7853290
  have hstable : (prefixWord ++ tailWord_7853290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7853290).length < 2 ^ (prefixWord ++ tailWord_7853290).sum := by decide
  have hdescent : baseEnd_7853290 < baseStart_7853290 := by decide
  rcases family_descends (prefixWord ++ tailWord_7853290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7853293 : List Nat := [1, 5, 1, 2, 2, 2, 1, 3, 1, 5]
def baseStart_7853293 : Nat := 118140960795 + 7853293 * 2 ^ 59
def prefixEnd_7853293 : Nat := 4983230072969 + 3 ^ 40 * 7853293 * 2
def baseEnd_7853293 : Nat := 1344171343196549229573623

theorem tailTrace_7853293 : CollatzResearch.WordTrace tailWord_7853293 prefixEnd_7853293 1344171343196549229573623 := by
  unfold tailWord_7853293
  simp only [CollatzResearch.WordTrace]
  refine ⟨286433127137868171508284533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190955418091912114338856355 286433127137868171508284533)
  ·
    refine ⟨26853105669175141078901675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 286433127137868171508284533 26853105669175141078901675)
    ·
      refine ⟨40279658503762711618352513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26853105669175141078901675 40279658503762711618352513)
      ·
        refine ⟨30209743877822033713764385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40279658503762711618352513 30209743877822033713764385)
        ·
          refine ⟨22657307908366525285323289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30209743877822033713764385 22657307908366525285323289)
          ·
            refine ⟨16992980931274893963992467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22657307908366525285323289 16992980931274893963992467)
            ·
              refine ⟨25489471396912340945988701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16992980931274893963992467 25489471396912340945988701)
              ·
                refine ⟨9558551773842127854745763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25489471396912340945988701 9558551773842127854745763)
                ·
                  refine ⟨14337827660763191782118645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9558551773842127854745763 14337827660763191782118645)
                  ·
                    refine ⟨1344171343196549229573623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14337827660763191782118645 1344171343196549229573623)
                    ·
                      rfl

theorem cell23_7853293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 3, 1, 5].length) (baseStart_7853293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7853293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7853293 prefixEnd_7853293 := by exact prefixLift 7853293
  have htrace : WordTrace (prefixWord ++ tailWord_7853293) baseStart_7853293 baseEnd_7853293 := by
    simpa [prefixWord, tailWord_7853293, baseEnd_7853293] using wordTrace_append hprefix tailTrace_7853293
  have hstable : (prefixWord ++ tailWord_7853293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7853293).length < 2 ^ (prefixWord ++ tailWord_7853293).sum := by decide
  have hdescent : baseEnd_7853293 < baseStart_7853293 := by decide
  rcases family_descends (prefixWord ++ tailWord_7853293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7853306 : List Nat := [3, 1, 1, 1, 1, 4, 3, 1, 4, 4]
def baseStart_7853306 : Nat := 118140960795 + 7853306 * 2 ^ 59
def prefixEnd_7853306 : Nat := 4983230072969 + 3 ^ 40 * 7853306 * 2
def baseEnd_7853306 : Nat := 1344173568279385379286103

theorem tailTrace_7853306 : CollatzResearch.WordTrace tailWord_7853306 prefixEnd_7853306 1344173568279385379286103 := by
  unfold tailWord_7853306
  simp only [CollatzResearch.WordTrace]
  refine ⟨71608400321705268682126943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190955734191214049819005181 71608400321705268682126943)
  ·
    refine ⟨107412600482557903023190415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71608400321705268682126943 107412600482557903023190415)
    ·
      refine ⟨161118900723836854534785623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107412600482557903023190415 161118900723836854534785623)
      ·
        refine ⟨241678351085755281802178435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161118900723836854534785623 241678351085755281802178435)
        ·
          refine ⟨362517526628632922703267653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241678351085755281802178435 362517526628632922703267653)
          ·
            refine ⟨67972036242868673006862685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 362517526628632922703267653 67972036242868673006862685)
            ·
              refine ⟨25489513591075752377573507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67972036242868673006862685 25489513591075752377573507)
              ·
                refine ⟨38234270386613628566360261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25489513591075752377573507 38234270386613628566360261)
                ·
                  refine ⟨7168925697490055356192549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38234270386613628566360261 7168925697490055356192549)
                  ·
                    refine ⟨1344173568279385379286103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7168925697490055356192549 1344173568279385379286103)
                    ·
                      rfl

theorem cell23_7853306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 1, 4, 4].length) (baseStart_7853306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7853306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7853306 prefixEnd_7853306 := by exact prefixLift 7853306
  have htrace : WordTrace (prefixWord ++ tailWord_7853306) baseStart_7853306 baseEnd_7853306 := by
    simpa [prefixWord, tailWord_7853306, baseEnd_7853306] using wordTrace_append hprefix tailTrace_7853306
  have hstable : (prefixWord ++ tailWord_7853306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7853306).length < 2 ^ (prefixWord ++ tailWord_7853306).sum := by decide
  have hdescent : baseEnd_7853306 < baseStart_7853306 := by decide
  rcases family_descends (prefixWord ++ tailWord_7853306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7853309 : List Nat := [1, 4, 1, 1, 1, 1, 1, 1, 2, 6, 4]
def baseStart_7853309 : Nat := 118140960795 + 7853309 * 2 ^ 59
def prefixEnd_7853309 : Nat := 4983230072969 + 3 ^ 40 * 7853309 * 2
def baseEnd_7853309 : Nat := 4032522245280119626120795

theorem tailTrace_7853309 : CollatzResearch.WordTrace tailWord_7853309 prefixEnd_7853309 4032522245280119626120795 := by
  unfold tailWord_7853309
  simp only [CollatzResearch.WordTrace]
  refine ⟨286433710705810206240866981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190955807137206804160577987 286433710705810206240866981)
  ·
    refine ⟨53706320757339413670162559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 286433710705810206240866981 53706320757339413670162559)
    ·
      refine ⟨80559481136009120505243839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53706320757339413670162559 80559481136009120505243839)
      ·
        refine ⟨120839221704013680757865759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80559481136009120505243839 120839221704013680757865759)
        ·
          refine ⟨181258832556020521136798639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120839221704013680757865759 181258832556020521136798639)
          ·
            refine ⟨271888248834030781705197959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181258832556020521136798639 271888248834030781705197959)
            ·
              refine ⟨407832373251046172557796939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 271888248834030781705197959 407832373251046172557796939)
              ·
                refine ⟨611748559876569258836695409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 407832373251046172557796939 611748559876569258836695409)
                ·
                  refine ⟨458811419907426944127521557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 611748559876569258836695409 458811419907426944127521557)
                  ·
                    refine ⟨21506785308160638005977573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 458811419907426944127521557 21506785308160638005977573)
                    ·
                      refine ⟨4032522245280119626120795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21506785308160638005977573 4032522245280119626120795)
                      ·
                        rfl

theorem cell23_7853309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 6, 4].length) (baseStart_7853309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7853309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7853309 prefixEnd_7853309 := by exact prefixLift 7853309
  have htrace : WordTrace (prefixWord ++ tailWord_7853309) baseStart_7853309 baseEnd_7853309 := by
    simpa [prefixWord, tailWord_7853309, baseEnd_7853309] using wordTrace_append hprefix tailTrace_7853309
  have hstable : (prefixWord ++ tailWord_7853309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7853309).length < 2 ^ (prefixWord ++ tailWord_7853309).sum := by decide
  have hdescent : baseEnd_7853309 < baseStart_7853309 := by decide
  rcases family_descends (prefixWord ++ tailWord_7853309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7853316 : List Nat := [2, 3, 2, 2, 2, 1, 1, 1, 3, 1, 5]
def baseStart_7853316 : Nat := 118140960795 + 7853316 * 2 ^ 59
def prefixEnd_7853316 : Nat := 4983230072969 + 3 ^ 40 * 7853316 * 2
def baseEnd_7853316 : Nat := 4032525839644701098733263

theorem tailTrace_7853316 : CollatzResearch.WordTrace tailWord_7853316 prefixEnd_7853316 4032525839644701098733263 := by
  unfold tailWord_7853316
  simp only [CollatzResearch.WordTrace]
  refine ⟨143216983008392423218185901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190955977344523230957581201 143216983008392423218185901)
  ·
    refine ⟨53706368628147158706819713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143216983008392423218185901 53706368628147158706819713)
    ·
      refine ⟨40279776471110369030114785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53706368628147158706819713 40279776471110369030114785)
      ·
        refine ⟨30209832353332776772586089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40279776471110369030114785 30209832353332776772586089)
        ·
          refine ⟨22657374264999582579439567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30209832353332776772586089 22657374264999582579439567)
          ·
            refine ⟨33986061397499373869159351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22657374264999582579439567 33986061397499373869159351)
            ·
              refine ⟨50979092096249060803739027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33986061397499373869159351 50979092096249060803739027)
              ·
                refine ⟨76468638144373591205608541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50979092096249060803739027 76468638144373591205608541)
                ·
                  refine ⟨28675739304140096702103203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76468638144373591205608541 28675739304140096702103203)
                  ·
                    refine ⟨43013608956210145053154805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28675739304140096702103203 43013608956210145053154805)
                    ·
                      refine ⟨4032525839644701098733263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43013608956210145053154805 4032525839644701098733263)
                      ·
                        rfl

theorem cell23_7853316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_7853316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7853316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7853316 prefixEnd_7853316 := by exact prefixLift 7853316
  have htrace : WordTrace (prefixWord ++ tailWord_7853316) baseStart_7853316 baseEnd_7853316 := by
    simpa [prefixWord, tailWord_7853316, baseEnd_7853316] using wordTrace_append hprefix tailTrace_7853316
  have hstable : (prefixWord ++ tailWord_7853316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7853316).length < 2 ^ (prefixWord ++ tailWord_7853316).sum := by decide
  have hdescent : baseEnd_7853316 < baseStart_7853316 := by decide
  rcases family_descends (prefixWord ++ tailWord_7853316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7853326 : List Nat := [4, 1, 1, 2, 1, 4, 1, 1, 1, 1, 6]
def baseStart_7853326 : Nat := 118140960795 + 7853326 * 2 ^ 59
def prefixEnd_7853326 : Nat := 4983230072969 + 3 ^ 40 * 7853326 * 2
def baseEnd_7853326 : Nat := 4032530974451246059608217

theorem tailTrace_7853326 : CollatzResearch.WordTrace tailWord_7853326 prefixEnd_7853326 4032530974451246059608217 := by
  unfold tailWord_7853326
  simp only [CollatzResearch.WordTrace]
  refine ⟨35804291343343577268029479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 190956220497832412096157221 35804291343343577268029479)
  ·
    refine ⟨53706437015015365902044219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35804291343343577268029479 53706437015015365902044219)
    ·
      refine ⟨80559655522523048853066329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53706437015015365902044219 80559655522523048853066329)
      ·
        refine ⟨60419741641892286639799747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80559655522523048853066329 60419741641892286639799747)
        ·
          refine ⟨90629612462838429959699621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60419741641892286639799747 90629612462838429959699621)
          ·
            refine ⟨16993052336782205617443679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90629612462838429959699621 16993052336782205617443679)
            ·
              refine ⟨25489578505173308426165519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16993052336782205617443679 25489578505173308426165519)
              ·
                refine ⟨38234367757759962639248279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25489578505173308426165519 38234367757759962639248279)
                ·
                  refine ⟨57351551636639943958872419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38234367757759962639248279 57351551636639943958872419)
                  ·
                    refine ⟨86027327454959915938308629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57351551636639943958872419 86027327454959915938308629)
                    ·
                      refine ⟨4032530974451246059608217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86027327454959915938308629 4032530974451246059608217)
                      ·
                        rfl

theorem cell23_7853326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 1, 1, 1, 6].length) (baseStart_7853326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7853326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7853326 prefixEnd_7853326 := by exact prefixLift 7853326
  have htrace : WordTrace (prefixWord ++ tailWord_7853326) baseStart_7853326 baseEnd_7853326 := by
    simpa [prefixWord, tailWord_7853326, baseEnd_7853326] using wordTrace_append hprefix tailTrace_7853326
  have hstable : (prefixWord ++ tailWord_7853326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7853326).length < 2 ^ (prefixWord ++ tailWord_7853326).sum := by decide
  have hdescent : baseEnd_7853326 < baseStart_7853326 := by decide
  rcases family_descends (prefixWord ++ tailWord_7853326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7853336 : List Nat := [2, 1, 2, 3, 1, 3, 4, 7]
def baseStart_7853336 : Nat := 118140960795 + 7853336 * 2 ^ 59
def prefixEnd_7853336 : Nat := 4983230072969 + 3 ^ 40 * 7853336 * 2
def baseEnd_7853336 : Nat := 149353189231770037795673

theorem tailTrace_7853336 : CollatzResearch.WordTrace tailWord_7853336 prefixEnd_7853336 149353189231770037795673 := by
  unfold tailWord_7853336
  simp only [CollatzResearch.WordTrace]
  refine ⟨143217347738356194926049931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190956463651141593234733241 143217347738356194926049931)
  ·
    refine ⟨214826021607534292389074897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143217347738356194926049931 214826021607534292389074897)
    ·
      refine ⟨161119516205650719291806173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214826021607534292389074897 161119516205650719291806173)
      ·
        refine ⟨60419818577119019734427315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161119516205650719291806173 60419818577119019734427315)
        ·
          refine ⟨90629727865678529601640973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60419818577119019734427315 90629727865678529601640973)
          ·
            refine ⟨33986147949629448600615365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90629727865678529601640973 33986147949629448600615365)
            ·
              refine ⟨6372402740555521612615381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33986147949629448600615365 6372402740555521612615381)
              ·
                refine ⟨149353189231770037795673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6372402740555521612615381 149353189231770037795673)
                ·
                  rfl

theorem cell23_7853336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 4, 7].length) (baseStart_7853336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7853336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7853336 prefixEnd_7853336 := by exact prefixLift 7853336
  have htrace : WordTrace (prefixWord ++ tailWord_7853336) baseStart_7853336 baseEnd_7853336 := by
    simpa [prefixWord, tailWord_7853336, baseEnd_7853336] using wordTrace_append hprefix tailTrace_7853336
  have hstable : (prefixWord ++ tailWord_7853336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7853336).length < 2 ^ (prefixWord ++ tailWord_7853336).sum := by decide
  have hdescent : baseEnd_7853336 < baseStart_7853336 := by decide
  rcases family_descends (prefixWord ++ tailWord_7853336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7853347 : List Nat := [1, 1, 1, 4, 2, 3, 3, 3, 1, 2, 2]
def baseStart_7853347 : Nat := 118140960795 + 7853347 * 2 ^ 59
def prefixEnd_7853347 : Nat := 4983230072969 + 3 ^ 40 * 7853347 * 2
def baseEnd_7853347 : Nat := 4032541757544990477445621

theorem tailTrace_7853347 : CollatzResearch.WordTrace tailWord_7853347 prefixEnd_7853347 4032541757544990477445621 := by
  unfold tailWord_7853347
  simp only [CollatzResearch.WordTrace]
  refine ⟨286435096679672538730750295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190956731119781692487166863 286435096679672538730750295)
  ·
    refine ⟨429652645019508808096125443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286435096679672538730750295 429652645019508808096125443)
    ·
      refine ⟨644478967529263212144188165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 429652645019508808096125443 644478967529263212144188165)
      ·
        refine ⟨120839806411736852277035281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 644478967529263212144188165 120839806411736852277035281)
        ·
          refine ⟨90629854808802639207776461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120839806411736852277035281 90629854808802639207776461)
          ·
            refine ⟨33986195553300989702916173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90629854808802639207776461 33986195553300989702916173)
            ·
              refine ⟨12744823332487871138593565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33986195553300989702916173 12744823332487871138593565)
              ·
                refine ⟨4779308749682951676972587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12744823332487871138593565 4779308749682951676972587)
                ·
                  refine ⟨7168963124524427515458881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4779308749682951676972587 7168963124524427515458881)
                  ·
                    refine ⟨5376722343393320636594161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7168963124524427515458881 5376722343393320636594161)
                    ·
                      refine ⟨4032541757544990477445621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5376722343393320636594161 4032541757544990477445621)
                      ·
                        rfl

theorem cell23_7853347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 3, 3, 1, 2, 2].length) (baseStart_7853347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7853347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7853347 prefixEnd_7853347 := by exact prefixLift 7853347
  have htrace : WordTrace (prefixWord ++ tailWord_7853347) baseStart_7853347 baseEnd_7853347 := by
    simpa [prefixWord, tailWord_7853347, baseEnd_7853347] using wordTrace_append hprefix tailTrace_7853347
  have hstable : (prefixWord ++ tailWord_7853347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7853347).length < 2 ^ (prefixWord ++ tailWord_7853347).sum := by decide
  have hdescent : baseEnd_7853347 < baseStart_7853347 := by decide
  rcases family_descends (prefixWord ++ tailWord_7853347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7853359 : List Nat := [1, 1, 2, 1, 2, 1, 3, 1, 4, 2, 5]
def baseStart_7853359 : Nat := 118140960795 + 7853359 * 2 ^ 59
def prefixEnd_7853359 : Nat := 4983230072969 + 3 ^ 40 * 7853359 * 2
def baseEnd_7853359 : Nat := 4032547919312844430495565

theorem tailTrace_7853359 : CollatzResearch.WordTrace tailWord_7853359 prefixEnd_7853359 4032547919312844430495565 := by
  unfold tailWord_7853359
  simp only [CollatzResearch.WordTrace]
  refine ⟨286435534355629064780187131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190957022903752709853458087 286435534355629064780187131)
  ·
    refine ⟨429653301533443597170280697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286435534355629064780187131 429653301533443597170280697)
    ·
      refine ⟨322239976150082697877710523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 429653301533443597170280697 322239976150082697877710523)
      ·
        refine ⟨483359964225124046816565785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322239976150082697877710523 483359964225124046816565785)
        ·
          refine ⟨362519973168843035112424339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 483359964225124046816565785 362519973168843035112424339)
          ·
            refine ⟨543779959753264552668636509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 362519973168843035112424339 543779959753264552668636509)
            ·
              refine ⟨203917484907474207250738691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 543779959753264552668636509 203917484907474207250738691)
              ·
                refine ⟨305876227361211310876108037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 203917484907474207250738691 305876227361211310876108037)
                ·
                  refine ⟨57351792630227120789270257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 305876227361211310876108037 57351792630227120789270257)
                  ·
                    refine ⟨43013844472670340591952693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57351792630227120789270257 43013844472670340591952693)
                    ·
                      refine ⟨4032547919312844430495565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 43013844472670340591952693 4032547919312844430495565)
                      ·
                        rfl

theorem cell23_7853359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 4, 2, 5].length) (baseStart_7853359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7853359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7853359 prefixEnd_7853359 := by exact prefixLift 7853359
  have htrace : WordTrace (prefixWord ++ tailWord_7853359) baseStart_7853359 baseEnd_7853359 := by
    simpa [prefixWord, tailWord_7853359, baseEnd_7853359] using wordTrace_append hprefix tailTrace_7853359
  have hstable : (prefixWord ++ tailWord_7853359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7853359).length < 2 ^ (prefixWord ++ tailWord_7853359).sum := by decide
  have hdescent : baseEnd_7853359 < baseStart_7853359 := by decide
  rcases family_descends (prefixWord ++ tailWord_7853359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7853363 : List Nat := [1, 1, 1, 2, 5, 2, 2, 1, 4, 1, 3]
def baseStart_7853363 : Nat := 118140960795 + 7853363 * 2 ^ 59
def prefixEnd_7853363 : Nat := 4983230072969 + 3 ^ 40 * 7853363 * 2
def baseEnd_7853363 : Nat := 4032549973235462414845547

theorem tailTrace_7853363 : CollatzResearch.WordTrace tailWord_7853363 prefixEnd_7853363 4032549973235462414845547 := by
  unfold tailWord_7853363
  simp only [CollatzResearch.WordTrace]
  refine ⟨286435680247614573463332743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190957120165076382308888495 286435680247614573463332743)
  ·
    refine ⟨429653520371421860194999115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286435680247614573463332743 429653520371421860194999115)
    ·
      refine ⟨644480280557132790292498673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 429653520371421860194999115 644480280557132790292498673)
      ·
        refine ⟨483360210417849592719374005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 644480280557132790292498673 483360210417849592719374005)
        ·
          refine ⟨45315019726673399317441313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 483360210417849592719374005 45315019726673399317441313)
          ·
            refine ⟨33986264795005049488080985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45315019726673399317441313 33986264795005049488080985)
            ·
              refine ⟨25489698596253787116060739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33986264795005049488080985 25489698596253787116060739)
              ·
                refine ⟨38234547894380680674091109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25489698596253787116060739 38234547894380680674091109)
                ·
                  refine ⟨7168977730196377626392083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38234547894380680674091109 7168977730196377626392083)
                  ·
                    refine ⟨10753466595294566439588125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7168977730196377626392083 10753466595294566439588125)
                    ·
                      refine ⟨4032549973235462414845547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10753466595294566439588125 4032549973235462414845547)
                      ·
                        rfl

theorem cell23_7853363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 1, 4, 1, 3].length) (baseStart_7853363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7853363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7853363 prefixEnd_7853363 := by exact prefixLift 7853363
  have htrace : WordTrace (prefixWord ++ tailWord_7853363) baseStart_7853363 baseEnd_7853363 := by
    simpa [prefixWord, tailWord_7853363, baseEnd_7853363] using wordTrace_append hprefix tailTrace_7853363
  have hstable : (prefixWord ++ tailWord_7853363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7853363).length < 2 ^ (prefixWord ++ tailWord_7853363).sum := by decide
  have hdescent : baseEnd_7853363 < baseStart_7853363 := by decide
  rcases family_descends (prefixWord ++ tailWord_7853363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7853379 : List Nat := [1, 1, 1, 3, 1, 3, 1, 3, 1, 8]
def baseStart_7853379 : Nat := 118140960795 + 7853379 * 2 ^ 59
def prefixEnd_7853379 : Nat := 4983230072969 + 3 ^ 40 * 7853379 * 2
def baseEnd_7853379 : Nat := 1344186062975311450748491

theorem tailTrace_7853379 : CollatzResearch.WordTrace tailWord_7853379 prefixEnd_7853379 1344186062975311450748491 := by
  unfold tailWord_7853379
  simp only [CollatzResearch.WordTrace]
  refine ⟨286436263815556608195915191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190957509210371072130610127 286436263815556608195915191)
  ·
    refine ⟨429654395723334912293872787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286436263815556608195915191 429654395723334912293872787)
    ·
      refine ⟨644481593585002368440809181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 429654395723334912293872787 644481593585002368440809181)
      ·
        refine ⟨241680597594375888165303443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 644481593585002368440809181 241680597594375888165303443)
        ·
          refine ⟨362520896391563832247955165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241680597594375888165303443 362520896391563832247955165)
          ·
            refine ⟨135945336146836437092983187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 362520896391563832247955165 135945336146836437092983187)
            ·
              refine ⟨203918004220254655639474781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135945336146836437092983187 203918004220254655639474781)
              ·
                refine ⟨76469251582595495864803043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 203918004220254655639474781 76469251582595495864803043)
                ·
                  refine ⟨114703877373893243797204565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76469251582595495864803043 114703877373893243797204565)
                  ·
                    refine ⟨1344186062975311450748491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 114703877373893243797204565 1344186062975311450748491)
                    ·
                      rfl

theorem cell23_7853379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 3, 1, 8].length) (baseStart_7853379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7853379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7853379 prefixEnd_7853379 := by exact prefixLift 7853379
  have htrace : WordTrace (prefixWord ++ tailWord_7853379) baseStart_7853379 baseEnd_7853379 := by
    simpa [prefixWord, tailWord_7853379, baseEnd_7853379] using wordTrace_append hprefix tailTrace_7853379
  have hstable : (prefixWord ++ tailWord_7853379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7853379).length < 2 ^ (prefixWord ++ tailWord_7853379).sum := by decide
  have hdescent : baseEnd_7853379 < baseStart_7853379 := by decide
  rcases family_descends (prefixWord ++ tailWord_7853379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7853426 : List Nat := [3, 2, 1, 2, 1, 2, 2, 3, 7]
def baseStart_7853426 : Nat := 118140960795 + 7853426 * 2 ^ 59
def prefixEnd_7853426 : Nat := 4983230072969 + 3 ^ 40 * 7853426 * 2
def baseEnd_7853426 : Nat := 448064702501855074261973

theorem tailTrace_7853426 : CollatzResearch.WordTrace tailWord_7853426 prefixEnd_7853426 448064702501855074261973 := by
  unfold tailWord_7853426
  simp only [CollatzResearch.WordTrace]
  refine ⟨71609494511596583805719033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190958652030924223481917421 71609494511596583805719033)
  ·
    refine ⟨53707120883697437854289275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71609494511596583805719033 53707120883697437854289275)
    ·
      refine ⟨80560681325546156781433913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53707120883697437854289275 80560681325546156781433913)
      ·
        refine ⟨60420510994159617586075435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80560681325546156781433913 60420510994159617586075435)
        ·
          refine ⟨90630766491239426379113153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60420510994159617586075435 90630766491239426379113153)
          ·
            refine ⟨67973074868429569784334865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90630766491239426379113153 67973074868429569784334865)
            ·
              refine ⟨50979806151322177338251149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67973074868429569784334865 50979806151322177338251149)
              ·
                refine ⟨19117427306745816501844181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50979806151322177338251149 19117427306745816501844181)
                ·
                  refine ⟨448064702501855074261973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19117427306745816501844181 448064702501855074261973)
                  ·
                    rfl

theorem cell23_7853426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 3, 7].length) (baseStart_7853426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7853426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7853426 prefixEnd_7853426 := by exact prefixLift 7853426
  have htrace : WordTrace (prefixWord ++ tailWord_7853426) baseStart_7853426 baseEnd_7853426 := by
    simpa [prefixWord, tailWord_7853426, baseEnd_7853426] using wordTrace_append hprefix tailTrace_7853426
  have hstable : (prefixWord ++ tailWord_7853426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7853426).length < 2 ^ (prefixWord ++ tailWord_7853426).sum := by decide
  have hdescent : baseEnd_7853426 < baseStart_7853426 := by decide
  rcases family_descends (prefixWord ++ tailWord_7853426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7853458 : List Nat := [3, 2, 3, 3, 2, 1, 2, 1, 1, 3, 2]
def baseStart_7853458 : Nat := 118140960795 + 7853458 * 2 ^ 59
def prefixEnd_7853458 : Nat := 4983230072969 + 3 ^ 40 * 7853458 * 2
def baseEnd_7853458 : Nat := 4032598753897639543157611

theorem tailTrace_7853458 : CollatzResearch.WordTrace tailWord_7853458 prefixEnd_7853458 4032598753897639543157611 := by
  unfold tailWord_7853458
  simp only [CollatzResearch.WordTrace]
  refine ⟨71609786295567601172010257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190959430121513603125360685 71609786295567601172010257)
  ·
    refine ⟨53707339721675700879007693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71609786295567601172010257 53707339721675700879007693)
    ·
      refine ⟨20140252395628387829627885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53707339721675700879007693 20140252395628387829627885)
      ·
        refine ⟨7552594648360645436110457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20140252395628387829627885 7552594648360645436110457)
        ·
          refine ⟨5664445986270484077082843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7552594648360645436110457 5664445986270484077082843)
          ·
            refine ⟨8496668979405726115624265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5664445986270484077082843 8496668979405726115624265)
            ·
              refine ⟨6372501734554294586718199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8496668979405726115624265 6372501734554294586718199)
              ·
                refine ⟨9558752601831441880077299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6372501734554294586718199 9558752601831441880077299)
                ·
                  refine ⟨14338128902747162820115949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9558752601831441880077299 14338128902747162820115949)
                  ·
                    refine ⟨5376798338530186057543481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14338128902747162820115949 5376798338530186057543481)
                    ·
                      refine ⟨4032598753897639543157611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5376798338530186057543481 4032598753897639543157611)
                      ·
                        rfl

theorem cell23_7853458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_7853458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7853458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7853458 prefixEnd_7853458 := by exact prefixLift 7853458
  have htrace : WordTrace (prefixWord ++ tailWord_7853458) baseStart_7853458 baseEnd_7853458 := by
    simpa [prefixWord, tailWord_7853458, baseEnd_7853458] using wordTrace_append hprefix tailTrace_7853458
  have hstable : (prefixWord ++ tailWord_7853458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7853458).length < 2 ^ (prefixWord ++ tailWord_7853458).sum := by decide
  have hdescent : baseEnd_7853458 < baseStart_7853458 := by decide
  rcases family_descends (prefixWord ++ tailWord_7853458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7853460 : List Nat := [2, 4, 2, 1, 2, 1, 1, 5, 5]
def baseStart_7853460 : Nat := 118140960795 + 7853460 * 2 ^ 59
def prefixEnd_7853460 : Nat := 4983230072969 + 3 ^ 40 * 7853460 * 2
def baseEnd_7853460 : Nat := 448066642317660948370289

theorem tailTrace_7853460 : CollatzResearch.WordTrace tailWord_7853460 prefixEnd_7853460 448066642317660948370289 := by
  unfold tailWord_7853460
  simp only [CollatzResearch.WordTrace]
  refine ⟨143219609064131579514806917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190959478752175439353075889 143219609064131579514806917)
  ·
    refine ⟨26853676699524671159026297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 143219609064131579514806917 26853676699524671159026297)
    ·
      refine ⟨20140257524643503369269723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26853676699524671159026297 20140257524643503369269723)
      ·
        refine ⟨30210386286965255053904585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20140257524643503369269723 30210386286965255053904585)
        ·
          refine ⟨22657789715223941290428439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30210386286965255053904585 22657789715223941290428439)
          ·
            refine ⟨33986684572835911935642659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22657789715223941290428439 33986684572835911935642659)
            ·
              refine ⟨50980026859253867903463989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33986684572835911935642659 50980026859253867903463989)
              ·
                refine ⟨4779377518055050115949749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50980026859253867903463989 4779377518055050115949749)
                ·
                  refine ⟨448066642317660948370289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4779377518055050115949749 448066642317660948370289)
                  ·
                    rfl

theorem cell23_7853460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 5, 5].length) (baseStart_7853460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7853460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7853460 prefixEnd_7853460 := by exact prefixLift 7853460
  have htrace : WordTrace (prefixWord ++ tailWord_7853460) baseStart_7853460 baseEnd_7853460 := by
    simpa [prefixWord, tailWord_7853460, baseEnd_7853460] using wordTrace_append hprefix tailTrace_7853460
  have hstable : (prefixWord ++ tailWord_7853460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7853460).length < 2 ^ (prefixWord ++ tailWord_7853460).sum := by decide
  have hdescent : baseEnd_7853460 < baseStart_7853460 := by decide
  rcases family_descends (prefixWord ++ tailWord_7853460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7853493 : List Nat := [1, 3, 3, 2, 2, 1, 1, 2, 1, 3, 4]
def baseStart_7853493 : Nat := 118140960795 + 7853493 * 2 ^ 59
def prefixEnd_7853493 : Nat := 4983230072969 + 3 ^ 40 * 7853493 * 2
def baseEnd_7853493 : Nat := 4032616725720546906219949

theorem tailTrace_7853493 : CollatzResearch.WordTrace tailWord_7853493 prefixEnd_7853493 4032616725720546906219949 := by
  unfold tailWord_7853493
  simp only [CollatzResearch.WordTrace]
  refine ⟨286440421737143605665565133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190960281158095737110376755 286440421737143605665565133)
  ·
    refine ⟨107415158151428852124586925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 286440421737143605665565133 107415158151428852124586925)
    ·
      refine ⟨40280684306785819546720097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107415158151428852124586925 40280684306785819546720097)
      ·
        refine ⟨30210513230089364660040073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40280684306785819546720097 30210513230089364660040073)
        ·
          refine ⟨22657884922567023495030055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30210513230089364660040073 22657884922567023495030055)
          ·
            refine ⟨33986827383850535242545083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22657884922567023495030055 33986827383850535242545083)
            ·
              refine ⟨50980241075775802863817625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33986827383850535242545083 50980241075775802863817625)
              ·
                refine ⟨38235180806831852147863219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50980241075775802863817625 38235180806831852147863219)
                ·
                  refine ⟨57352771210247778221794829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38235180806831852147863219 57352771210247778221794829)
                  ·
                    refine ⟨21507289203842916833173061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57352771210247778221794829 21507289203842916833173061)
                    ·
                      refine ⟨4032616725720546906219949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21507289203842916833173061 4032616725720546906219949)
                      ·
                        rfl

theorem cell23_7853493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_7853493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7853493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7853493 prefixEnd_7853493 := by exact prefixLift 7853493
  have htrace : WordTrace (prefixWord ++ tailWord_7853493) baseStart_7853493 baseEnd_7853493 := by
    simpa [prefixWord, tailWord_7853493, baseEnd_7853493] using wordTrace_append hprefix tailTrace_7853493
  have hstable : (prefixWord ++ tailWord_7853493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7853493).length < 2 ^ (prefixWord ++ tailWord_7853493).sum := by decide
  have hdescent : baseEnd_7853493 < baseStart_7853493 := by decide
  rcases family_descends (prefixWord ++ tailWord_7853493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7853513 : List Nat := [1, 2, 1, 1, 2, 1, 3, 5, 2, 2, 3]
def baseStart_7853513 : Nat := 118140960795 + 7853513 * 2 ^ 59
def prefixEnd_7853513 : Nat := 4983230072969 + 3 ^ 40 * 7853513 * 2
def baseEnd_7853513 : Nat := 4032626995333636827969857

theorem tailTrace_7853513 : CollatzResearch.WordTrace tailWord_7853513 prefixEnd_7853513 4032626995333636827969857 := by
  unfold tailWord_7853513
  simp only [CollatzResearch.WordTrace]
  refine ⟨286441151197071149081293193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190960767464714099387528795 286441151197071149081293193)
  ·
    refine ⟨214830863397803361810969895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286441151197071149081293193 214830863397803361810969895)
    ·
      refine ⟨322246295096705042716454843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214830863397803361810969895 322246295096705042716454843)
      ·
        refine ⟨483369442645057564074682265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322246295096705042716454843 483369442645057564074682265)
        ·
          refine ⟨362527081983793173056011699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 483369442645057564074682265 362527081983793173056011699)
          ·
            refine ⟨543790622975689759584017549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 362527081983793173056011699 543790622975689759584017549)
            ·
              refine ⟨203921483615883659844006581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 543790622975689759584017549 203921483615883659844006581)
              ·
                refine ⟨19117639088989093110375617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 203921483615883659844006581 19117639088989093110375617)
                ·
                  refine ⟨14338229316741819832781713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19117639088989093110375617 14338229316741819832781713)
                  ·
                    refine ⟨10753671987556364874586285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14338229316741819832781713 10753671987556364874586285)
                    ·
                      refine ⟨4032626995333636827969857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10753671987556364874586285 4032626995333636827969857)
                      ·
                        rfl

theorem cell23_7853513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 5, 2, 2, 3].length) (baseStart_7853513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7853513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7853513 prefixEnd_7853513 := by exact prefixLift 7853513
  have htrace : WordTrace (prefixWord ++ tailWord_7853513) baseStart_7853513 baseEnd_7853513 := by
    simpa [prefixWord, tailWord_7853513, baseEnd_7853513] using wordTrace_append hprefix tailTrace_7853513
  have hstable : (prefixWord ++ tailWord_7853513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7853513).length < 2 ^ (prefixWord ++ tailWord_7853513).sum := by decide
  have hdescent : baseEnd_7853513 < baseStart_7853513 := by decide
  rcases family_descends (prefixWord ++ tailWord_7853513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7853530 : List Nat := [3, 1, 1, 2, 3, 3, 1, 2, 2, 2, 3]
def baseStart_7853530 : Nat := 118140960795 + 7853530 * 2 ^ 59
def prefixEnd_7853530 : Nat := 4983230072969 + 3 ^ 40 * 7853530 * 2
def baseEnd_7853530 : Nat := 4032635724504763261457279

theorem tailTrace_7853530 : CollatzResearch.WordTrace tailWord_7853530 prefixEnd_7853530 4032635724504763261457279 := by
  unfold tailWord_7853530
  simp only [CollatzResearch.WordTrace]
  refine ⟨71610442809502390246165511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190961180825339707323108029 71610442809502390246165511)
  ·
    refine ⟨107415664214253585369248267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71610442809502390246165511 107415664214253585369248267)
    ·
      refine ⟨161123496321380378053872401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107415664214253585369248267 161123496321380378053872401)
      ·
        refine ⟨120842622241035283540404301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161123496321380378053872401 120842622241035283540404301)
        ·
          refine ⟨45315983340388231327651613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120842622241035283540404301 45315983340388231327651613)
          ·
            refine ⟨16993493752645586747869355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45315983340388231327651613 16993493752645586747869355)
            ·
              refine ⟨25490240628968380121804033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16993493752645586747869355 25490240628968380121804033)
              ·
                refine ⟨19117680471726285091353025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25490240628968380121804033 19117680471726285091353025)
                ·
                  refine ⟨14338260353794713818514769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19117680471726285091353025 14338260353794713818514769)
                  ·
                    refine ⟨10753695265346035363886077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14338260353794713818514769 10753695265346035363886077)
                    ·
                      refine ⟨4032635724504763261457279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10753695265346035363886077 4032635724504763261457279)
                      ·
                        rfl

theorem cell23_7853530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 2, 2, 2, 3].length) (baseStart_7853530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7853530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7853530 prefixEnd_7853530 := by exact prefixLift 7853530
  have htrace : WordTrace (prefixWord ++ tailWord_7853530) baseStart_7853530 baseEnd_7853530 := by
    simpa [prefixWord, tailWord_7853530, baseEnd_7853530] using wordTrace_append hprefix tailTrace_7853530
  have hstable : (prefixWord ++ tailWord_7853530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7853530).length < 2 ^ (prefixWord ++ tailWord_7853530).sum := by decide
  have hdescent : baseEnd_7853530 < baseStart_7853530 := by decide
  rcases family_descends (prefixWord ++ tailWord_7853530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7853533 : List Nat := [1, 4, 3, 1, 1, 2, 2, 1, 8]
def baseStart_7853533 : Nat := 118140960795 + 7853533 * 2 ^ 59
def prefixEnd_7853533 : Nat := 4983230072969 + 3 ^ 40 * 7853533 * 2
def baseEnd_7853533 : Nat := 448070807216302972191085

theorem tailTrace_7853533 : CollatzResearch.WordTrace tailWord_7853533 prefixEnd_7853533 448070807216302972191085 := by
  unfold tailWord_7853533
  simp only [CollatzResearch.WordTrace]
  refine ⟨286441880656998692497021253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190961253771332461664680835 286441880656998692497021253)
  ·
    refine ⟨53707852623187254843191485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 286441880656998692497021253 53707852623187254843191485)
    ·
      refine ⟨20140444733695220566196807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53707852623187254843191485 20140444733695220566196807)
      ·
        refine ⟨30210667100542830849295211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20140444733695220566196807 30210667100542830849295211)
        ·
          refine ⟨45316000650814246273942817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30210667100542830849295211 45316000650814246273942817)
          ·
            refine ⟨33987000488110684705457113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45316000650814246273942817 33987000488110684705457113)
            ·
              refine ⟨25490250366083013529092835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33987000488110684705457113 25490250366083013529092835)
              ·
                refine ⟨38235375549124520293639253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25490250366083013529092835 38235375549124520293639253)
                ·
                  refine ⟨448070807216302972191085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38235375549124520293639253 448070807216302972191085)
                  ·
                    rfl

theorem cell23_7853533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 1, 8].length) (baseStart_7853533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7853533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7853533 prefixEnd_7853533 := by exact prefixLift 7853533
  have htrace : WordTrace (prefixWord ++ tailWord_7853533) baseStart_7853533 baseEnd_7853533 := by
    simpa [prefixWord, tailWord_7853533, baseEnd_7853533] using wordTrace_append hprefix tailTrace_7853533
  have hstable : (prefixWord ++ tailWord_7853533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7853533).length < 2 ^ (prefixWord ++ tailWord_7853533).sum := by decide
  have hdescent : baseEnd_7853533 < baseStart_7853533 := by decide
  rcases family_descends (prefixWord ++ tailWord_7853533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7853536 : List Nat := [2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 6]
def baseStart_7853536 : Nat := 118140960795 + 7853536 * 2 ^ 59
def prefixEnd_7853536 : Nat := 4983230072969 + 3 ^ 40 * 7853536 * 2
def baseEnd_7853536 : Nat := 4032638805388690237982251

theorem tailTrace_7853536 : CollatzResearch.WordTrace tailWord_7853536 prefixEnd_7853536 4032638805388690237982251 := by
  unfold tailWord_7853536
  simp only [CollatzResearch.WordTrace]
  refine ⟨143220995037993912004690231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190961326717325216006253641 143220995037993912004690231)
  ·
    refine ⟨214831492556990868007035347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143220995037993912004690231 214831492556990868007035347)
    ·
      refine ⟨322247238835486302010553021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214831492556990868007035347 322247238835486302010553021)
      ·
        refine ⟨120842714563307363253957383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 322247238835486302010553021 120842714563307363253957383)
        ·
          refine ⟨181264071844961044880936075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120842714563307363253957383 181264071844961044880936075)
          ·
            refine ⟨271896107767441567321404113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181264071844961044880936075 271896107767441567321404113)
            ·
              refine ⟨203922080825581175491053085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 271896107767441567321404113 203922080825581175491053085)
              ·
                refine ⟨76470780309592940809144907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 203922080825581175491053085 76470780309592940809144907)
                ·
                  refine ⟨114706170464389411213717361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76470780309592940809144907 114706170464389411213717361)
                  ·
                    refine ⟨86029627848292058410288021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 114706170464389411213717361 86029627848292058410288021)
                    ·
                      refine ⟨4032638805388690237982251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86029627848292058410288021 4032638805388690237982251)
                      ·
                        rfl

theorem cell23_7853536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 6].length) (baseStart_7853536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7853536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7853536 prefixEnd_7853536 := by exact prefixLift 7853536
  have htrace : WordTrace (prefixWord ++ tailWord_7853536) baseStart_7853536 baseEnd_7853536 := by
    simpa [prefixWord, tailWord_7853536, baseEnd_7853536] using wordTrace_append hprefix tailTrace_7853536
  have hstable : (prefixWord ++ tailWord_7853536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7853536).length < 2 ^ (prefixWord ++ tailWord_7853536).sum := by decide
  have hdescent : baseEnd_7853536 < baseStart_7853536 := by decide
  rcases family_descends (prefixWord ++ tailWord_7853536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7853577 : List Nat := [1, 2, 1, 1, 3, 1, 4, 5, 1, 1, 3]
def baseStart_7853577 : Nat := 118140960795 + 7853577 * 2 ^ 59
def prefixEnd_7853577 : Nat := 4983230072969 + 3 ^ 40 * 7853577 * 2
def baseEnd_7853577 : Nat := 4032659858095524577569563

theorem tailTrace_7853577 : CollatzResearch.WordTrace tailWord_7853577 prefixEnd_7853577 4032659858095524577569563 := by
  unfold tailWord_7853577
  simp only [CollatzResearch.WordTrace]
  refine ⟨286443485468839288011622985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190962323645892858674415323 286443485468839288011622985)
  ·
    refine ⟨214832614101629466008717239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286443485468839288011622985 214832614101629466008717239)
    ·
      refine ⟨322248921152444199013075859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214832614101629466008717239 322248921152444199013075859)
      ·
        refine ⟨483373381728666298519613789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322248921152444199013075859 483373381728666298519613789)
        ·
          refine ⟨181265018148249861944855171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 483373381728666298519613789 181265018148249861944855171)
          ·
            refine ⟨271897527222374792917282757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181265018148249861944855171 271897527222374792917282757)
            ·
              refine ⟨50980786354195273671990517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 271897527222374792917282757 50980786354195273671990517)
              ·
                refine ⟨4779448720705806906749111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50980786354195273671990517 4779448720705806906749111)
                ·
                  refine ⟨7169173081058710360123667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4779448720705806906749111 7169173081058710360123667)
                  ·
                    refine ⟨10753759621588065540185501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7169173081058710360123667 10753759621588065540185501)
                    ·
                      refine ⟨4032659858095524577569563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10753759621588065540185501 4032659858095524577569563)
                      ·
                        rfl

theorem cell23_7853577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 5, 1, 1, 3].length) (baseStart_7853577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7853577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7853577 prefixEnd_7853577 := by exact prefixLift 7853577
  have htrace : WordTrace (prefixWord ++ tailWord_7853577) baseStart_7853577 baseEnd_7853577 := by
    simpa [prefixWord, tailWord_7853577, baseEnd_7853577] using wordTrace_append hprefix tailTrace_7853577
  have hstable : (prefixWord ++ tailWord_7853577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7853577).length < 2 ^ (prefixWord ++ tailWord_7853577).sum := by decide
  have hdescent : baseEnd_7853577 < baseStart_7853577 := by decide
  rcases family_descends (prefixWord ++ tailWord_7853577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7853588 : List Nat := [2, 4, 3, 1, 2, 2, 2, 2, 1, 4]
def baseStart_7853588 : Nat := 118140960795 + 7853588 * 2 ^ 59
def prefixEnd_7853588 : Nat := 4983230072969 + 3 ^ 40 * 7853588 * 2
def baseEnd_7853588 : Nat := 1344221835460908011510671

theorem tailTrace_7853588 : CollatzResearch.WordTrace tailWord_7853588 prefixEnd_7853588 1344221835460908011510671 := by
  unfold tailWord_7853588
  simp only [CollatzResearch.WordTrace]
  refine ⟨143221943335899718445136709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190962591114532957926848945 143221943335899718445136709)
  ·
    refine ⟨26854114375481197208463133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 143221943335899718445136709 26854114375481197208463133)
    ·
      refine ⟨10070292890805448953173675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26854114375481197208463133 10070292890805448953173675)
      ·
        refine ⟨15105439336208173429760513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10070292890805448953173675 15105439336208173429760513)
        ·
          refine ⟨11329079502156130072320385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15105439336208173429760513 11329079502156130072320385)
          ·
            refine ⟨8496809626617097554240289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11329079502156130072320385 8496809626617097554240289)
            ·
              refine ⟨6372607219962823165680217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8496809626617097554240289 6372607219962823165680217)
              ·
                refine ⟨4779455414972117374260163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6372607219962823165680217 4779455414972117374260163)
                ·
                  refine ⟨7169183122458176061390245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4779455414972117374260163 7169183122458176061390245)
                  ·
                    refine ⟨1344221835460908011510671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7169183122458176061390245 1344221835460908011510671)
                    ·
                      rfl

theorem cell23_7853588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_7853588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7853588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7853588 prefixEnd_7853588 := by exact prefixLift 7853588
  have htrace : WordTrace (prefixWord ++ tailWord_7853588) baseStart_7853588 baseEnd_7853588 := by
    simpa [prefixWord, tailWord_7853588, baseEnd_7853588] using wordTrace_append hprefix tailTrace_7853588
  have hstable : (prefixWord ++ tailWord_7853588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7853588).length < 2 ^ (prefixWord ++ tailWord_7853588).sum := by decide
  have hdescent : baseEnd_7853588 < baseStart_7853588 := by decide
  rcases family_descends (prefixWord ++ tailWord_7853588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7853600 : List Nat := [2, 1, 1, 6, 1, 1, 1, 2, 3, 1, 4]
def baseStart_7853600 : Nat := 118140960795 + 7853600 * 2 ^ 59
def prefixEnd_7853600 : Nat := 4983230072969 + 3 ^ 40 * 7853600 * 2
def baseEnd_7853600 : Nat := 4032671668150577987581957

theorem tailTrace_7853600 : CollatzResearch.WordTrace tailWord_7853600 prefixEnd_7853600 4032671668150577987581957 := by
  unfold tailWord_7853600
  simp only [CollatzResearch.WordTrace]
  refine ⟨143222162173877981469855127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190962882898503975293140169 143222162173877981469855127)
  ·
    refine ⟨214833243260816972204782691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143222162173877981469855127 214833243260816972204782691)
    ·
      refine ⟨322249864891225458307174037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214833243260816972204782691 322249864891225458307174037)
      ·
        refine ⟨15105462416776193358148783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 322249864891225458307174037 15105462416776193358148783)
        ·
          refine ⟨22658193625164290037223175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15105462416776193358148783 22658193625164290037223175)
          ·
            refine ⟨33987290437746435055834763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22658193625164290037223175 33987290437746435055834763)
            ·
              refine ⟨50980935656619652583752145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33987290437746435055834763 50980935656619652583752145)
              ·
                refine ⟨38235701742464739437814109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50980935656619652583752145 38235701742464739437814109)
                ·
                  refine ⟨14338388153424277289180291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38235701742464739437814109 14338388153424277289180291)
                  ·
                    refine ⟨21507582230136415933770437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14338388153424277289180291 21507582230136415933770437)
                    ·
                      refine ⟨4032671668150577987581957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21507582230136415933770437 4032671668150577987581957)
                      ·
                        rfl

theorem cell23_7853600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_7853600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7853600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7853600 prefixEnd_7853600 := by exact prefixLift 7853600
  have htrace : WordTrace (prefixWord ++ tailWord_7853600) baseStart_7853600 baseEnd_7853600 := by
    simpa [prefixWord, tailWord_7853600, baseEnd_7853600] using wordTrace_append hprefix tailTrace_7853600
  have hstable : (prefixWord ++ tailWord_7853600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7853600).length < 2 ^ (prefixWord ++ tailWord_7853600).sum := by decide
  have hdescent : baseEnd_7853600 < baseStart_7853600 := by decide
  rcases family_descends (prefixWord ++ tailWord_7853600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7853610 : List Nat := [3, 1, 4, 1, 1, 1, 4, 1, 1, 6]
def baseStart_7853610 : Nat := 118140960795 + 7853610 * 2 ^ 59
def prefixEnd_7853610 : Nat := 4983230072969 + 3 ^ 40 * 7853610 * 2
def baseEnd_7853610 : Nat := 1344225600985707649485637

theorem tailTrace_7853610 : CollatzResearch.WordTrace tailWord_7853610 prefixEnd_7853610 1344225600985707649485637 := by
  unfold tailWord_7853610
  simp only [CollatzResearch.WordTrace]
  refine ⟨71611172269429933661893571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190963126051813156431716189 71611172269429933661893571)
  ·
    refine ⟨107416758404144900492840357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71611172269429933661893571 107416758404144900492840357)
    ·
      refine ⟨20140642200777168842407567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107416758404144900492840357 20140642200777168842407567)
      ·
        refine ⟨30210963301165753263611351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20140642200777168842407567 30210963301165753263611351)
        ·
          refine ⟨45316444951748629895417027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30210963301165753263611351 45316444951748629895417027)
          ·
            refine ⟨67974667427622944843125541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45316444951748629895417027 67974667427622944843125541)
            ·
              refine ⟨12745250142679302158086039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67974667427622944843125541 12745250142679302158086039)
              ·
                refine ⟨19117875214018953237129059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12745250142679302158086039 19117875214018953237129059)
                ·
                  refine ⟨28676812821028429855693589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19117875214018953237129059 28676812821028429855693589)
                  ·
                    refine ⟨1344225600985707649485637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28676812821028429855693589 1344225600985707649485637)
                    ·
                      rfl

theorem cell23_7853610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 4, 1, 1, 6].length) (baseStart_7853610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7853610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7853610 prefixEnd_7853610 := by exact prefixLift 7853610
  have htrace : WordTrace (prefixWord ++ tailWord_7853610) baseStart_7853610 baseEnd_7853610 := by
    simpa [prefixWord, tailWord_7853610, baseEnd_7853610] using wordTrace_append hprefix tailTrace_7853610
  have hstable : (prefixWord ++ tailWord_7853610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7853610).length < 2 ^ (prefixWord ++ tailWord_7853610).sum := by decide
  have hdescent : baseEnd_7853610 < baseStart_7853610 := by decide
  rcases family_descends (prefixWord ++ tailWord_7853610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7853661 : List Nat := [1, 4, 4, 2, 2, 1, 1, 1, 1, 6]
def baseStart_7853661 : Nat := 118140960795 + 7853661 * 2 ^ 59
def prefixEnd_7853661 : Nat := 4983230072969 + 3 ^ 40 * 7853661 * 2
def baseEnd_7853661 : Nat := 1344234330156834082973059

theorem tailTrace_7853661 : CollatzResearch.WordTrace tailWord_7853661 prefixEnd_7853661 1344234330156834082973059 := by
  unfold tailWord_7853661
  simp only [CollatzResearch.WordTrace]
  refine ⟨286446549200534970357680837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190964366133689980238453891 286446549200534970357680837)
  ·
    refine ⟨53708727975100306942065157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 286446549200534970357680837 53708727975100306942065157)
    ·
      refine ⟨10070386495331307551637217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53708727975100306942065157 10070386495331307551637217)
      ·
        refine ⟨7552789871498480663727913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10070386495331307551637217 7552789871498480663727913)
        ·
          refine ⟨5664592403623860497795935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7552789871498480663727913 5664592403623860497795935)
          ·
            refine ⟨8496888605435790746693903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5664592403623860497795935 8496888605435790746693903)
            ·
              refine ⟨12745332908153686120040855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8496888605435790746693903 12745332908153686120040855)
              ·
                refine ⟨19117999362230529180061283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12745332908153686120040855 19117999362230529180061283)
                ·
                  refine ⟨28676999043345793770091925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19117999362230529180061283 28676999043345793770091925)
                  ·
                    refine ⟨1344234330156834082973059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28676999043345793770091925 1344234330156834082973059)
                    ·
                      rfl

theorem cell23_7853661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_7853661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7853661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7853661 prefixEnd_7853661 := by exact prefixLift 7853661
  have htrace : WordTrace (prefixWord ++ tailWord_7853661) baseStart_7853661 baseEnd_7853661 := by
    simpa [prefixWord, tailWord_7853661, baseEnd_7853661] using wordTrace_append hprefix tailTrace_7853661
  have hstable : (prefixWord ++ tailWord_7853661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7853661).length < 2 ^ (prefixWord ++ tailWord_7853661).sum := by decide
  have hdescent : baseEnd_7853661 < baseStart_7853661 := by decide
  rcases family_descends (prefixWord ++ tailWord_7853661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7853667 : List Nat := [1, 1, 1, 5, 1, 5, 1, 1, 1, 3, 3]
def baseStart_7853667 : Nat := 118140960795 + 7853667 * 2 ^ 59
def prefixEnd_7853667 : Nat := 4983230072969 + 3 ^ 40 * 7853667 * 2
def baseEnd_7853667 : Nat := 4032706071354429225444149

theorem tailTrace_7853667 : CollatzResearch.WordTrace tailWord_7853667 prefixEnd_7853667 4032706071354429225444149 := by
  unfold tailWord_7853667
  simp only [CollatzResearch.WordTrace]
  refine ⟨286446768038513233382399255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190964512025675488921599503 286446768038513233382399255)
  ·
    refine ⟨429670152057769850073598883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286446768038513233382399255 429670152057769850073598883)
    ·
      refine ⟨644505228086654775110398325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 429670152057769850073598883 644505228086654775110398325)
      ·
        refine ⟨60422365133123885166599843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 644505228086654775110398325 60422365133123885166599843)
        ·
          refine ⟨90633547699685827749899765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60422365133123885166599843 90633547699685827749899765)
          ·
            refine ⟨8496895096845546351553103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 90633547699685827749899765 8496895096845546351553103)
            ·
              refine ⟨12745342645268319527329655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8496895096845546351553103 12745342645268319527329655)
              ·
                refine ⟨19118013967902479290994483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12745342645268319527329655 19118013967902479290994483)
                ·
                  refine ⟨28677020951853718936491725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19118013967902479290994483 28677020951853718936491725)
                  ·
                    refine ⟨10753882856945144601184397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28677020951853718936491725 10753882856945144601184397)
                    ·
                      refine ⟨4032706071354429225444149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10753882856945144601184397 4032706071354429225444149)
                      ·
                        rfl

theorem cell23_7853667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 1, 1, 1, 3, 3].length) (baseStart_7853667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7853667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7853667 prefixEnd_7853667 := by exact prefixLift 7853667
  have htrace : WordTrace (prefixWord ++ tailWord_7853667) baseStart_7853667 baseEnd_7853667 := by
    simpa [prefixWord, tailWord_7853667, baseEnd_7853667] using wordTrace_append hprefix tailTrace_7853667
  have hstable : (prefixWord ++ tailWord_7853667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7853667).length < 2 ^ (prefixWord ++ tailWord_7853667).sum := by decide
  have hdescent : baseEnd_7853667 < baseStart_7853667 := by decide
  rcases family_descends (prefixWord ++ tailWord_7853667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7853673 : List Nat := [1, 2, 1, 1, 1, 4, 2, 2, 2, 3, 4]
def baseStart_7853673 : Nat := 118140960795 + 7853673 * 2 ^ 59
def prefixEnd_7853673 : Nat := 4983230072969 + 3 ^ 40 * 7853673 * 2
def baseEnd_7853673 : Nat := 4032709152238356201969121

theorem tailTrace_7853673 : CollatzResearch.WordTrace tailWord_7853673 prefixEnd_7853673 4032709152238356201969121 := by
  unfold tailWord_7853673
  simp only [CollatzResearch.WordTrace]
  refine ⟨286446986876491496407117673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190964657917660997604745115 286446986876491496407117673)
  ·
    refine ⟨214835240157368622305338255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286446986876491496407117673 214835240157368622305338255)
    ·
      refine ⟨322252860236052933458007383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214835240157368622305338255 322252860236052933458007383)
      ·
        refine ⟨483379290354079400187011075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 322252860236052933458007383 483379290354079400187011075)
        ·
          refine ⟨725068935531119100280516613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 483379290354079400187011075 725068935531119100280516613)
          ·
            refine ⟨135950425412084831302596865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 725068935531119100280516613 135950425412084831302596865)
            ·
              refine ⟨101962819059063623476947649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135950425412084831302596865 101962819059063623476947649)
              ·
                refine ⟨76472114294297717607710737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101962819059063623476947649 76472114294297717607710737)
                ·
                  refine ⟨57354085720723288205783053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76472114294297717607710737 57354085720723288205783053)
                  ·
                    refine ⟨21507782145271233077168645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57354085720723288205783053 21507782145271233077168645)
                    ·
                      refine ⟨4032709152238356201969121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21507782145271233077168645 4032709152238356201969121)
                      ·
                        rfl

theorem cell23_7853673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 2, 2, 3, 4].length) (baseStart_7853673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7853673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7853673 prefixEnd_7853673 := by exact prefixLift 7853673
  have htrace : WordTrace (prefixWord ++ tailWord_7853673) baseStart_7853673 baseEnd_7853673 := by
    simpa [prefixWord, tailWord_7853673, baseEnd_7853673] using wordTrace_append hprefix tailTrace_7853673
  have hstable : (prefixWord ++ tailWord_7853673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7853673).length < 2 ^ (prefixWord ++ tailWord_7853673).sum := by decide
  have hdescent : baseEnd_7853673 < baseStart_7853673 := by decide
  rcases family_descends (prefixWord ++ tailWord_7853673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7853707 : List Nat := [1, 1, 1, 1, 4, 1, 3, 3, 4, 2, 2]
def baseStart_7853707 : Nat := 118140960795 + 7853707 * 2 ^ 59
def prefixEnd_7853707 : Nat := 4983230072969 + 3 ^ 40 * 7853707 * 2
def baseEnd_7853707 : Nat := 4032726610580609068943965

theorem tailTrace_7853707 : CollatzResearch.WordTrace tailWord_7853707 prefixEnd_7853707 4032726610580609068943965 := by
  unfold tailWord_7853707
  simp only [CollatzResearch.WordTrace]
  refine ⟨286448226958368320213855375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190965484638912213475903583 286448226958368320213855375)
  ·
    refine ⟨429672340437552480320783063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286448226958368320213855375 429672340437552480320783063)
    ·
      refine ⟨644508510656328720481174595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 429672340437552480320783063 644508510656328720481174595)
      ·
        refine ⟨966762765984493080721761893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 644508510656328720481174595 966762765984493080721761893)
        ·
          refine ⟨181268018622092452635330355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 966762765984493080721761893 181268018622092452635330355)
          ·
            refine ⟨271902027933138678952995533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181268018622092452635330355 271902027933138678952995533)
            ·
              refine ⟨101963260474927004607373325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 271902027933138678952995533 101963260474927004607373325)
              ·
                refine ⟨38236222678097626727764997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101963260474927004607373325 38236222678097626727764997)
                ·
                  refine ⟨7169291752143305011455937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38236222678097626727764997 7169291752143305011455937)
                  ·
                    refine ⟨5376968814107478758591953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7169291752143305011455937 5376968814107478758591953)
                    ·
                      refine ⟨4032726610580609068943965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5376968814107478758591953 4032726610580609068943965)
                      ·
                        rfl

theorem cell23_7853707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 3, 4, 2, 2].length) (baseStart_7853707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7853707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7853707 prefixEnd_7853707 := by exact prefixLift 7853707
  have htrace : WordTrace (prefixWord ++ tailWord_7853707) baseStart_7853707 baseEnd_7853707 := by
    simpa [prefixWord, tailWord_7853707, baseEnd_7853707] using wordTrace_append hprefix tailTrace_7853707
  have hstable : (prefixWord ++ tailWord_7853707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7853707).length < 2 ^ (prefixWord ++ tailWord_7853707).sum := by decide
  have hdescent : baseEnd_7853707 < baseStart_7853707 := by decide
  rcases family_descends (prefixWord ++ tailWord_7853707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7853713 : List Nat := [1, 2, 2, 1, 1, 1, 1, 7, 7]
def baseStart_7853713 : Nat := 118140960795 + 7853713 * 2 ^ 59
def prefixEnd_7853713 : Nat := 4983230072969 + 3 ^ 40 * 7853713 * 2
def baseEnd_7853713 : Nat := 448081076829392893940993

theorem tailTrace_7853713 : CollatzResearch.WordTrace tailWord_7853713 prefixEnd_7853713 448081076829392893940993 := by
  unfold tailWord_7853713
  simp only [CollatzResearch.WordTrace]
  refine ⟨286448445796346583238573793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190965630530897722159049195 286448445796346583238573793)
  ·
    refine ⟨214836334347259937428930345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286448445796346583238573793 214836334347259937428930345)
    ·
      refine ⟨161127250760444953071697759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214836334347259937428930345 161127250760444953071697759)
      ·
        refine ⟨241690876140667429607546639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161127250760444953071697759 241690876140667429607546639)
        ·
          refine ⟨362536314211001144411319959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241690876140667429607546639 362536314211001144411319959)
          ·
            refine ⟨543804471316501716616979939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 362536314211001144411319959 543804471316501716616979939)
            ·
              refine ⟨815706706974752574925469909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 543804471316501716616979939 815706706974752574925469909)
              ·
                refine ⟨19118125944720763474815701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 815706706974752574925469909 19118125944720763474815701)
                ·
                  refine ⟨448081076829392893940993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19118125944720763474815701 448081076829392893940993)
                  ·
                    rfl

theorem cell23_7853713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 7, 7].length) (baseStart_7853713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7853713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7853713 prefixEnd_7853713 := by exact prefixLift 7853713
  have htrace : WordTrace (prefixWord ++ tailWord_7853713) baseStart_7853713 baseEnd_7853713 := by
    simpa [prefixWord, tailWord_7853713, baseEnd_7853713] using wordTrace_append hprefix tailTrace_7853713
  have hstable : (prefixWord ++ tailWord_7853713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7853713).length < 2 ^ (prefixWord ++ tailWord_7853713).sum := by decide
  have hdescent : baseEnd_7853713 < baseStart_7853713 := by decide
  rcases family_descends (prefixWord ++ tailWord_7853713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7853760 : List Nat := [2, 1, 1, 2, 4, 1, 1, 4, 2, 5]
def baseStart_7853760 : Nat := 118140960795 + 7853760 * 2 ^ 59
def prefixEnd_7853760 : Nat := 4983230072969 + 3 ^ 40 * 7853760 * 2
def baseEnd_7853760 : Nat := 1344251275018432453860407

theorem tailTrace_7853760 : CollatzResearch.WordTrace tailWord_7853760 prefixEnd_7853760 1344251275018432453860407 := by
  unfold tailWord_7853760
  simp only [CollatzResearch.WordTrace]
  refine ⟨143225080013588155132767367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190966773351450873510356489 143225080013588155132767367)
  ·
    refine ⟨214837620020382232699151051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143225080013588155132767367 214837620020382232699151051)
    ·
      refine ⟨322256430030573349048726577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214837620020382232699151051 322256430030573349048726577)
      ·
        refine ⟨241692322522930011786544933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 322256430030573349048726577 241692322522930011786544933)
        ·
          refine ⟨45317310473049377209977175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 241692322522930011786544933 45317310473049377209977175)
          ·
            refine ⟨67975965709574065814965763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45317310473049377209977175 67975965709574065814965763)
            ·
              refine ⟨101963948564361098722448645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67975965709574065814965763 101963948564361098722448645)
              ·
                refine ⟨19118240355817706010459121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 101963948564361098722448645 19118240355817706010459121)
                ·
                  refine ⟨14338680266863279507844341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19118240355817706010459121 14338680266863279507844341)
                  ·
                    refine ⟨1344251275018432453860407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14338680266863279507844341 1344251275018432453860407)
                    ·
                      rfl

theorem cell23_7853760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 4, 2, 5].length) (baseStart_7853760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7853760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7853760 prefixEnd_7853760 := by exact prefixLift 7853760
  have htrace : WordTrace (prefixWord ++ tailWord_7853760) baseStart_7853760 baseEnd_7853760 := by
    simpa [prefixWord, tailWord_7853760, baseEnd_7853760] using wordTrace_append hprefix tailTrace_7853760
  have hstable : (prefixWord ++ tailWord_7853760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7853760).length < 2 ^ (prefixWord ++ tailWord_7853760).sum := by decide
  have hdescent : baseEnd_7853760 < baseStart_7853760 := by decide
  rcases family_descends (prefixWord ++ tailWord_7853760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7853797 : List Nat := [1, 3, 1, 4, 1, 1, 1, 2, 1, 6, 2]
def baseStart_7853797 : Nat := 118140960795 + 7853797 * 2 ^ 59
def prefixEnd_7853797 : Nat := 4983230072969 + 3 ^ 40 * 7853797 * 2
def baseEnd_7853797 : Nat := 4032772823839513716818551

theorem tailTrace_7853797 : CollatzResearch.WordTrace tailWord_7853797 prefixEnd_7853797 4032772823839513716818551 := by
  unfold tailWord_7853797
  simp only [CollatzResearch.WordTrace]
  refine ⟨286451509528042265584631645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190967673018694843723087763 286451509528042265584631645)
  ·
    refine ⟨107419316073015849594236867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 286451509528042265584631645 107419316073015849594236867)
    ·
      refine ⟨161128974109523774391355301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107419316073015849594236867 161128974109523774391355301)
      ·
        refine ⟨30211682645535707698379119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 161128974109523774391355301 30211682645535707698379119)
        ·
          refine ⟨45317523968303561547568679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30211682645535707698379119 45317523968303561547568679)
          ·
            refine ⟨67976285952455342321353019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45317523968303561547568679 67976285952455342321353019)
            ·
              refine ⟨101964428928683013482029529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67976285952455342321353019 101964428928683013482029529)
              ·
                refine ⟨76473321696512260111522147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101964428928683013482029529 76473321696512260111522147)
                ·
                  refine ⟨114709982544768390167283221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76473321696512260111522147 114709982544768390167283221)
                  ·
                    refine ⟨5377030431786018289091401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 114709982544768390167283221 5377030431786018289091401)
                    ·
                      refine ⟨4032772823839513716818551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5377030431786018289091401 4032772823839513716818551)
                      ·
                        rfl

theorem cell23_7853797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 2, 1, 6, 2].length) (baseStart_7853797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7853797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7853797 prefixEnd_7853797 := by exact prefixLift 7853797
  have htrace : WordTrace (prefixWord ++ tailWord_7853797) baseStart_7853797 baseEnd_7853797 := by
    simpa [prefixWord, tailWord_7853797, baseEnd_7853797] using wordTrace_append hprefix tailTrace_7853797
  have hstable : (prefixWord ++ tailWord_7853797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7853797).length < 2 ^ (prefixWord ++ tailWord_7853797).sum := by decide
  have hdescent : baseEnd_7853797 < baseStart_7853797 := by decide
  rcases family_descends (prefixWord ++ tailWord_7853797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7853810 : List Nat := [3, 2, 1, 3, 1, 1, 1, 1, 1, 3, 6]
def baseStart_7853810 : Nat := 118140960795 + 7853810 * 2 ^ 59
def prefixEnd_7853810 : Nat := 4983230072969 + 3 ^ 40 * 7853810 * 2
def baseEnd_7853810 : Nat := 4032779499088022165955991

theorem tailTrace_7853810 : CollatzResearch.WordTrace tailWord_7853810 prefixEnd_7853810 4032779499088022165955991 := by
  unfold tailWord_7853810
  simp only [CollatzResearch.WordTrace]
  refine ⟨71612995919248792201213721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190967989117996779203236589 71612995919248792201213721)
  ·
    refine ⟨53709746939436594150910291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71612995919248792201213721 53709746939436594150910291)
    ·
      refine ⟨80564620409154891226365437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53709746939436594150910291 80564620409154891226365437)
      ·
        refine ⟨30211732653433084209887039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80564620409154891226365437 30211732653433084209887039)
        ·
          refine ⟨45317598980149626314830559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30211732653433084209887039 45317598980149626314830559)
          ·
            refine ⟨67976398470224439472245839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45317598980149626314830559 67976398470224439472245839)
            ·
              refine ⟨101964597705336659208368759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67976398470224439472245839 101964597705336659208368759)
              ·
                refine ⟨152946896558004988812553139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101964597705336659208368759 152946896558004988812553139)
                ·
                  refine ⟨229420344837007483218829709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 152946896558004988812553139 229420344837007483218829709)
                  ·
                    refine ⟨86032629313877806207061141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 229420344837007483218829709 86032629313877806207061141)
                    ·
                      refine ⟨4032779499088022165955991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 86032629313877806207061141 4032779499088022165955991)
                      ·
                        rfl

theorem cell23_7853810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_7853810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7853810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7853810 prefixEnd_7853810 := by exact prefixLift 7853810
  have htrace : WordTrace (prefixWord ++ tailWord_7853810) baseStart_7853810 baseEnd_7853810 := by
    simpa [prefixWord, tailWord_7853810, baseEnd_7853810] using wordTrace_append hprefix tailTrace_7853810
  have hstable : (prefixWord ++ tailWord_7853810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7853810).length < 2 ^ (prefixWord ++ tailWord_7853810).sum := by decide
  have hdescent : baseEnd_7853810 < baseStart_7853810 := by decide
  rcases family_descends (prefixWord ++ tailWord_7853810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
