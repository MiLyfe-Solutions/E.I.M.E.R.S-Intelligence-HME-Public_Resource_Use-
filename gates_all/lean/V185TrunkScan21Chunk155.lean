import V185TrunkScan21Chunk154

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_1889597 : List Nat := [1, 4, 1, 5, 2, 1, 2, 2, 3]
def baseStart_1889597 : Nat := 118140960795 + 1889597 * 2 ^ 59
def prefixEnd_1889597 : Nat := 4983230072969 + 3 ^ 40 * 1889597 * 2
def baseEnd_1889597 : Nat := 431231779686199411887737

theorem tailTrace_1889597 : CollatzResearch.WordTrace tailWord_1889597 prefixEnd_1889597 431231779686199411887737 := by
  unfold tailWord_1889597
  simp only [CollatzResearch.WordTrace]
  refine ⟨68919264535320261319859045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45946176356880174213239363 68919264535320261319859045)
  ·
    refine ⟨12922362100372548997473571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68919264535320261319859045 12922362100372548997473571)
    ·
      refine ⟨19383543150558823496210357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12922362100372548997473571 19383543150558823496210357)
      ·
        refine ⟨1817207170364889702769721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19383543150558823496210357 1817207170364889702769721)
        ·
          refine ⟨1362905377773667277077291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1817207170364889702769721 1362905377773667277077291)
          ·
            refine ⟨2044358066660500915615937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1362905377773667277077291 2044358066660500915615937)
            ·
              refine ⟨1533268549995375686711953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2044358066660500915615937 1533268549995375686711953)
              ·
                refine ⟨1149951412496531765033965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1533268549995375686711953 1149951412496531765033965)
                ·
                  refine ⟨431231779686199411887737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1149951412496531765033965 431231779686199411887737)
                  ·
                    rfl

theorem cell21_1889597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 2, 2, 3].length) (baseStart_1889597 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1889597 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1889597 prefixEnd_1889597 := by exact prefixLift 1889597
  have htrace : WordTrace (prefixWord ++ tailWord_1889597) baseStart_1889597 baseEnd_1889597 := by
    simpa [prefixWord, tailWord_1889597, baseEnd_1889597] using wordTrace_append hprefix tailTrace_1889597
  have hstable : (prefixWord ++ tailWord_1889597).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1889597).length < 2 ^ (prefixWord ++ tailWord_1889597).sum := by decide
  have hdescent : baseEnd_1889597 < baseStart_1889597 := by decide
  rcases family_descends (prefixWord ++ tailWord_1889597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1889647 : List Nat := [1, 1, 2, 1, 3, 1, 3, 2, 7]
def baseStart_1889647 : Nat := 118140960795 + 1889647 * 2 ^ 59
def prefixEnd_1889647 : Nat := 4983230072969 + 3 ^ 40 * 1889647 * 2
def baseEnd_1889647 : Nat := 431243190367410436054301

theorem tailTrace_1889647 : CollatzResearch.WordTrace tailWord_1889647 prefixEnd_1889647 431243190367410436054301 := by
  unfold tailWord_1889647
  simp only [CollatzResearch.WordTrace]
  refine ⟨68921088185139119859179195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45947392123426079906119463 68921088185139119859179195)
  ·
    refine ⟨103381632277708679788768793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68921088185139119859179195 103381632277708679788768793)
    ·
      refine ⟨77536224208281509841576595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103381632277708679788768793 77536224208281509841576595)
      ·
        refine ⟨116304336312422264762364893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77536224208281509841576595 116304336312422264762364893)
        ·
          refine ⟨43614126117158349285886835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116304336312422264762364893 43614126117158349285886835)
          ·
            refine ⟨65421189175737523928830253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43614126117158349285886835 65421189175737523928830253)
            ·
              refine ⟨24532945940901571473311345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65421189175737523928830253 24532945940901571473311345)
              ·
                refine ⟨18399709455676178604983509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24532945940901571473311345 18399709455676178604983509)
                ·
                  refine ⟨431243190367410436054301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18399709455676178604983509 431243190367410436054301)
                  ·
                    rfl

theorem cell21_1889647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 2, 7].length) (baseStart_1889647 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1889647 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1889647 prefixEnd_1889647 := by exact prefixLift 1889647
  have htrace : WordTrace (prefixWord ++ tailWord_1889647) baseStart_1889647 baseEnd_1889647 := by
    simpa [prefixWord, tailWord_1889647, baseEnd_1889647] using wordTrace_append hprefix tailTrace_1889647
  have hstable : (prefixWord ++ tailWord_1889647).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1889647).length < 2 ^ (prefixWord ++ tailWord_1889647).sum := by decide
  have hdescent : baseEnd_1889647 < baseStart_1889647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1889647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1889653 : List Nat := [1, 3, 4, 1, 3, 2, 1, 2, 4]
def baseStart_1889653 : Nat := 118140960795 + 1889653 * 2 ^ 59
def prefixEnd_1889653 : Nat := 4983230072969 + 3 ^ 40 * 1889653 * 2
def baseEnd_1889653 : Nat := 431244559649155758954289

theorem tailTrace_1889653 : CollatzResearch.WordTrace tailWord_1889653 prefixEnd_1889653 431244559649155758954289 := by
  unfold tailWord_1889653
  simp only [CollatzResearch.WordTrace]
  refine ⟨68921307023117382883897613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45947538015411588589265075 68921307023117382883897613)
  ·
    refine ⟨25845490133669018581461605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68921307023117382883897613 25845490133669018581461605)
    ·
      refine ⟨4846029400062940984024051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25845490133669018581461605 4846029400062940984024051)
      ·
        refine ⟨7269044100094411476036077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4846029400062940984024051 7269044100094411476036077)
        ·
          refine ⟨2725891537535404303513529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7269044100094411476036077 2725891537535404303513529)
          ·
            refine ⟨2044418653151553227635147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2725891537535404303513529 2044418653151553227635147)
            ·
              refine ⟨3066627979727329841452721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2044418653151553227635147 3066627979727329841452721)
              ·
                refine ⟨2299970984795497381089541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3066627979727329841452721 2299970984795497381089541)
                ·
                  refine ⟨431244559649155758954289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2299970984795497381089541 431244559649155758954289)
                  ·
                    rfl

theorem cell21_1889653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 1, 2, 4].length) (baseStart_1889653 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1889653 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1889653 prefixEnd_1889653 := by exact prefixLift 1889653
  have htrace : WordTrace (prefixWord ++ tailWord_1889653) baseStart_1889653 baseEnd_1889653 := by
    simpa [prefixWord, tailWord_1889653, baseEnd_1889653] using wordTrace_append hprefix tailTrace_1889653
  have hstable : (prefixWord ++ tailWord_1889653).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1889653).length < 2 ^ (prefixWord ++ tailWord_1889653).sum := by decide
  have hdescent : baseEnd_1889653 < baseStart_1889653 := by decide
  rcases family_descends (prefixWord ++ tailWord_1889653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1889698 : List Nat := [3, 3, 1, 2, 1, 2, 3, 3, 3]
def baseStart_1889698 : Nat := 118140960795 + 1889698 * 2 ^ 59
def prefixEnd_1889698 : Nat := 4983230072969 + 3 ^ 40 * 1889698 * 2
def baseEnd_1889698 : Nat := 431254829262245680704197

theorem tailTrace_1889698 : CollatzResearch.WordTrace tailWord_1889698 prefixEnd_1889698 431254829262245680704197 := by
  unfold tailWord_1889698
  simp only [CollatzResearch.WordTrace]
  refine ⟨17230737076988588892321437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45948632205302903712857165 17230737076988588892321437)
  ·
    refine ⟨6461526403870720834620539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17230737076988588892321437 6461526403870720834620539)
    ·
      refine ⟨9692289605806081251930809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6461526403870720834620539 9692289605806081251930809)
      ·
        refine ⟨7269217204354560938948107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9692289605806081251930809 7269217204354560938948107)
        ·
          refine ⟨10903825806531841408422161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7269217204354560938948107 10903825806531841408422161)
          ·
            refine ⟨8177869354898881056316621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10903825806531841408422161 8177869354898881056316621)
            ·
              refine ⟨3066701008087080396118733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8177869354898881056316621 3066701008087080396118733)
              ·
                refine ⟨1150012878032655148544525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3066701008087080396118733 1150012878032655148544525)
                ·
                  refine ⟨431254829262245680704197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1150012878032655148544525 431254829262245680704197)
                  ·
                    rfl

theorem cell21_1889698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 3, 3, 3].length) (baseStart_1889698 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1889698 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1889698 prefixEnd_1889698 := by exact prefixLift 1889698
  have htrace : WordTrace (prefixWord ++ tailWord_1889698) baseStart_1889698 baseEnd_1889698 := by
    simpa [prefixWord, tailWord_1889698, baseEnd_1889698] using wordTrace_append hprefix tailTrace_1889698
  have hstable : (prefixWord ++ tailWord_1889698).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1889698).length < 2 ^ (prefixWord ++ tailWord_1889698).sum := by decide
  have hdescent : baseEnd_1889698 < baseStart_1889698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1889698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1889802 : List Nat := [3, 1, 2, 2, 2, 3, 3, 5]
def baseStart_1889802 : Nat := 118140960795 + 1889802 * 2 ^ 59
def prefixEnd_1889802 : Nat := 4983230072969 + 3 ^ 40 * 1889802 * 2
def baseEnd_1889802 : Nat := 143759521159721536990217

theorem tailTrace_1889802 : CollatzResearch.WordTrace tailWord_1889802 prefixEnd_1889802 143759521159721536990217 := by
  unfold tailWord_1889802
  simp only [CollatzResearch.WordTrace]
  refine ⟨17231685374894395332767915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45951160999718387554047773 17231685374894395332767915)
  ·
    refine ⟨25847528062341592999151873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17231685374894395332767915 25847528062341592999151873)
    ·
      refine ⟨19385646046756194749363905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25847528062341592999151873 19385646046756194749363905)
      ·
        refine ⟨14539234535067146062022929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19385646046756194749363905 14539234535067146062022929)
        ·
          refine ⟨10904425901300359546517197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14539234535067146062022929 10904425901300359546517197)
          ·
            refine ⟨4089159712987634829943949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10904425901300359546517197 4089159712987634829943949)
            ·
              refine ⟨1533434892370363061228981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4089159712987634829943949 1533434892370363061228981)
              ·
                refine ⟨143759521159721536990217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1533434892370363061228981 143759521159721536990217)
                ·
                  rfl

theorem cell21_1889802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 3, 5].length) (baseStart_1889802 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1889802 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1889802 prefixEnd_1889802 := by exact prefixLift 1889802
  have htrace : WordTrace (prefixWord ++ tailWord_1889802) baseStart_1889802 baseEnd_1889802 := by
    simpa [prefixWord, tailWord_1889802, baseEnd_1889802] using wordTrace_append hprefix tailTrace_1889802
  have hstable : (prefixWord ++ tailWord_1889802).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1889802).length < 2 ^ (prefixWord ++ tailWord_1889802).sum := by decide
  have hdescent : baseEnd_1889802 < baseStart_1889802 := by decide
  rcases family_descends (prefixWord ++ tailWord_1889802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1889822 : List Nat := [4, 3, 3, 1, 1, 1, 1, 1, 6]
def baseStart_1889822 : Nat := 118140960795 + 1889822 * 2 ^ 59
def prefixEnd_1889822 : Nat := 4983230072969 + 3 ^ 40 * 1889822 * 2
def baseEnd_1889822 : Nat := 431283127751649020637277

theorem tailTrace_1889822 : CollatzResearch.WordTrace tailWord_1889822 prefixEnd_1889822 431283127751649020637277 := by
  unfold tailWord_1889822
  simp only [CollatzResearch.WordTrace]
  refine ⟨8615933869938140593349965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45951647306336749831199813 8615933869938140593349965)
  ·
    refine ⟨3230975201226802722506237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8615933869938140593349965 3230975201226802722506237)
    ·
      refine ⟨1211615700460051020939839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3230975201226802722506237 1211615700460051020939839)
      ·
        refine ⟨1817423550690076531409759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1211615700460051020939839 1817423550690076531409759)
        ·
          refine ⟨2726135326035114797114639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1817423550690076531409759 2726135326035114797114639)
          ·
            refine ⟨4089202989052672195671959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2726135326035114797114639 4089202989052672195671959)
            ·
              refine ⟨6133804483579008293507939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4089202989052672195671959 6133804483579008293507939)
              ·
                refine ⟨9200706725368512440261909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6133804483579008293507939 9200706725368512440261909)
                ·
                  refine ⟨431283127751649020637277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9200706725368512440261909 431283127751649020637277)
                  ·
                    rfl

theorem cell21_1889822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 1, 6].length) (baseStart_1889822 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1889822 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1889822 prefixEnd_1889822 := by exact prefixLift 1889822
  have htrace : WordTrace (prefixWord ++ tailWord_1889822) baseStart_1889822 baseEnd_1889822 := by
    simpa [prefixWord, tailWord_1889822, baseEnd_1889822] using wordTrace_append hprefix tailTrace_1889822
  have hstable : (prefixWord ++ tailWord_1889822).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1889822).length < 2 ^ (prefixWord ++ tailWord_1889822).sum := by decide
  have hdescent : baseEnd_1889822 < baseStart_1889822 := by decide
  rcases family_descends (prefixWord ++ tailWord_1889822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1889892 : List Nat := [2, 3, 1, 1, 2, 3, 3, 1, 5]
def baseStart_1889892 : Nat := 118140960795 + 1889892 * 2 ^ 59
def prefixEnd_1889892 : Nat := 4983230072969 + 3 ^ 40 * 1889892 * 2
def baseEnd_1889892 : Nat := 431299102705344454470467

theorem tailTrace_1889892 : CollatzResearch.WordTrace tailWord_1889892 prefixEnd_1889892 431299102705344454470467 := by
  unfold tailWord_1889892
  simp only [CollatzResearch.WordTrace]
  refine ⟨34465012034625763350923965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45953349379501017801231953 34465012034625763350923965)
  ·
    refine ⟨12924379512984661256596487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34465012034625763350923965 12924379512984661256596487)
    ·
      refine ⟨19386569269476991884894731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12924379512984661256596487 19386569269476991884894731)
      ·
        refine ⟨29079853904215487827342097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19386569269476991884894731 29079853904215487827342097)
        ·
          refine ⟨21809890428161615870506573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29079853904215487827342097 21809890428161615870506573)
          ·
            refine ⟨8178708910560605951439965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21809890428161615870506573 8178708910560605951439965)
            ·
              refine ⟨3067015841460227231789987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8178708910560605951439965 3067015841460227231789987)
              ·
                refine ⟨4600523762190340847684981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3067015841460227231789987 4600523762190340847684981)
                ·
                  refine ⟨431299102705344454470467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4600523762190340847684981 431299102705344454470467)
                  ·
                    rfl

theorem cell21_1889892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 3, 1, 5].length) (baseStart_1889892 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1889892 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1889892 prefixEnd_1889892 := by exact prefixLift 1889892
  have htrace : WordTrace (prefixWord ++ tailWord_1889892) baseStart_1889892 baseEnd_1889892 := by
    simpa [prefixWord, tailWord_1889892, baseEnd_1889892] using wordTrace_append hprefix tailTrace_1889892
  have hstable : (prefixWord ++ tailWord_1889892).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1889892).length < 2 ^ (prefixWord ++ tailWord_1889892).sum := by decide
  have hdescent : baseEnd_1889892 < baseStart_1889892 := by decide
  rcases family_descends (prefixWord ++ tailWord_1889892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1889920 : List Nat := [2, 1, 1, 2, 1, 4, 1, 9]
def baseStart_1889920 : Nat := 118140960795 + 1889920 * 2 ^ 59
def prefixEnd_1889920 : Nat := 4983230072969 + 3 ^ 40 * 1889920 * 2
def baseEnd_1889920 : Nat := 143768497562274209334581

theorem tailTrace_1889920 : CollatzResearch.WordTrace tailWord_1889920 prefixEnd_1889920 143768497562274209334581 := by
  unfold tailWord_1889920
  simp only [CollatzResearch.WordTrace]
  refine ⟨34465522656575043741933607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45954030208766724989244809 34465522656575043741933607)
  ·
    refine ⟨51698283984862565612900411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34465522656575043741933607 51698283984862565612900411)
    ·
      refine ⟨77547425977293848419350617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51698283984862565612900411 77547425977293848419350617)
      ·
        refine ⟨58160569482970386314512963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77547425977293848419350617 58160569482970386314512963)
        ·
          refine ⟨87240854224455579471769445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58160569482970386314512963 87240854224455579471769445)
          ·
            refine ⟨16357660167085421150956771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87240854224455579471769445 16357660167085421150956771)
            ·
              refine ⟨24536490250628131726435157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16357660167085421150956771 24536490250628131726435157)
              ·
                refine ⟨143768497562274209334581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24536490250628131726435157 143768497562274209334581)
                ·
                  rfl

theorem cell21_1889920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 9].length) (baseStart_1889920 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1889920 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1889920 prefixEnd_1889920 := by exact prefixLift 1889920
  have htrace : WordTrace (prefixWord ++ tailWord_1889920) baseStart_1889920 baseEnd_1889920 := by
    simpa [prefixWord, tailWord_1889920, baseEnd_1889920] using wordTrace_append hprefix tailTrace_1889920
  have hstable : (prefixWord ++ tailWord_1889920).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1889920).length < 2 ^ (prefixWord ++ tailWord_1889920).sum := by decide
  have hdescent : baseEnd_1889920 < baseStart_1889920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1889920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1890027 : List Nat := [1, 1, 1, 1, 2, 4, 4, 2, 5]
def baseStart_1890027 : Nat := 118140960795 + 1890027 * 2 ^ 59
def prefixEnd_1890027 : Nat := 4983230072969 + 3 ^ 40 * 1890027 * 2
def baseEnd_1890027 : Nat := 431329911544614219720191

theorem tailTrace_1890027 : CollatzResearch.WordTrace tailWord_1890027 prefixEnd_1890027 431329911544614219720191 := by
  unfold tailWord_1890027
  simp only [CollatzResearch.WordTrace]
  refine ⟨68934947923762444758012335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45956631949174963172008223 68934947923762444758012335)
  ·
    refine ⟨103402421885643667137018503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68934947923762444758012335 103402421885643667137018503)
    ·
      refine ⟨155103632828465500705527755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103402421885643667137018503 155103632828465500705527755)
      ·
        refine ⟨232655449242698251058291633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155103632828465500705527755 232655449242698251058291633)
        ·
          refine ⟨174491586932023688293718725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232655449242698251058291633 174491586932023688293718725)
          ·
            refine ⟨32717172549754441555072261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 174491586932023688293718725 32717172549754441555072261)
            ·
              refine ⟨6134469853078957791576049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32717172549754441555072261 6134469853078957791576049)
              ·
                refine ⟨4600852389809218343682037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6134469853078957791576049 4600852389809218343682037)
                ·
                  refine ⟨431329911544614219720191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4600852389809218343682037 431329911544614219720191)
                  ·
                    rfl

theorem cell21_1890027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 2, 5].length) (baseStart_1890027 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1890027 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1890027 prefixEnd_1890027 := by exact prefixLift 1890027
  have htrace : WordTrace (prefixWord ++ tailWord_1890027) baseStart_1890027 baseEnd_1890027 := by
    simpa [prefixWord, tailWord_1890027, baseEnd_1890027] using wordTrace_append hprefix tailTrace_1890027
  have hstable : (prefixWord ++ tailWord_1890027).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1890027).length < 2 ^ (prefixWord ++ tailWord_1890027).sum := by decide
  have hdescent : baseEnd_1890027 < baseStart_1890027 := by decide
  rcases family_descends (prefixWord ++ tailWord_1890027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1890036 : List Nat := [2, 6, 1, 1, 1, 3, 1, 3, 3]
def baseStart_1890036 : Nat := 118140960795 + 1890036 * 2 ^ 59
def prefixEnd_1890036 : Nat := 4983230072969 + 3 ^ 40 * 1890036 * 2
def baseEnd_1890036 : Nat := 431331965467232204070173

theorem tailTrace_1890036 : CollatzResearch.WordTrace tailWord_1890036 prefixEnd_1890036 431331965467232204070173 := by
  unfold tailWord_1890036
  simp only [CollatzResearch.WordTrace]
  refine ⟨34467638090364919647544981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45956850787153226196726641 34467638090364919647544981)
  ·
    refine ⟨1615670535485855608478671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 34467638090364919647544981 1615670535485855608478671)
    ·
      refine ⟨2423505803228783412718007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1615670535485855608478671 2423505803228783412718007)
      ·
        refine ⟨3635258704843175119077011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2423505803228783412718007 3635258704843175119077011)
        ·
          refine ⟨5452888057264762678615517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3635258704843175119077011 5452888057264762678615517)
          ·
            refine ⟨2044833021474286004480819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5452888057264762678615517 2044833021474286004480819)
            ·
              refine ⟨3067249532211429006721229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2044833021474286004480819 3067249532211429006721229)
              ·
                refine ⟨1150218574579285877520461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3067249532211429006721229 1150218574579285877520461)
                ·
                  refine ⟨431331965467232204070173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1150218574579285877520461 431331965467232204070173)
                  ·
                    rfl

theorem cell21_1890036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_1890036 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1890036 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1890036 prefixEnd_1890036 := by exact prefixLift 1890036
  have htrace : WordTrace (prefixWord ++ tailWord_1890036) baseStart_1890036 baseEnd_1890036 := by
    simpa [prefixWord, tailWord_1890036, baseEnd_1890036] using wordTrace_append hprefix tailTrace_1890036
  have hstable : (prefixWord ++ tailWord_1890036).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1890036).length < 2 ^ (prefixWord ++ tailWord_1890036).sum := by decide
  have hdescent : baseEnd_1890036 < baseStart_1890036 := by decide
  rcases family_descends (prefixWord ++ tailWord_1890036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1890058 : List Nat := [3, 1, 2, 2, 1, 3, 2, 1, 6]
def baseStart_1890058 : Nat := 118140960795 + 1890058 * 2 ^ 59
def prefixEnd_1890058 : Nat := 4983230072969 + 3 ^ 40 * 1890058 * 2
def baseEnd_1890058 : Nat := 431336986166965054703461

theorem tailTrace_1890058 : CollatzResearch.WordTrace tailWord_1890058 prefixEnd_1890058 431336986166965054703461 := by
  unfold tailWord_1890058
  simp only [CollatzResearch.WordTrace]
  refine ⟨17234019646662534263097707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45957385724433424701593885 17234019646662534263097707)
  ·
    refine ⟨25851029469993801394646561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17234019646662534263097707 25851029469993801394646561)
    ·
      refine ⟨19388272102495351045984921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25851029469993801394646561 19388272102495351045984921)
      ·
        refine ⟨14541204076871513284488691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19388272102495351045984921 14541204076871513284488691)
        ·
          refine ⟨21811806115307269926733037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14541204076871513284488691 21811806115307269926733037)
          ·
            refine ⟨8179427293240226222524889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21811806115307269926733037 8179427293240226222524889)
            ·
              refine ⟨6134570469930169666893667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8179427293240226222524889 6134570469930169666893667)
              ·
                refine ⟨9201855704895254500340501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6134570469930169666893667 9201855704895254500340501)
                ·
                  refine ⟨431336986166965054703461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9201855704895254500340501 431336986166965054703461)
                  ·
                    rfl

theorem cell21_1890058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 1, 6].length) (baseStart_1890058 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1890058 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1890058 prefixEnd_1890058 := by exact prefixLift 1890058
  have htrace : WordTrace (prefixWord ++ tailWord_1890058) baseStart_1890058 baseEnd_1890058 := by
    simpa [prefixWord, tailWord_1890058, baseEnd_1890058] using wordTrace_append hprefix tailTrace_1890058
  have hstable : (prefixWord ++ tailWord_1890058).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1890058).length < 2 ^ (prefixWord ++ tailWord_1890058).sum := by decide
  have hdescent : baseEnd_1890058 < baseStart_1890058 := by decide
  rcases family_descends (prefixWord ++ tailWord_1890058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1890072 : List Nat := [2, 1, 2, 3, 1, 1, 3, 8]
def baseStart_1890072 : Nat := 118140960795 + 1890072 * 2 ^ 59
def prefixEnd_1890072 : Nat := 4983230072969 + 3 ^ 40 * 1890072 * 2
def baseEnd_1890072 : Nat := 143780060385901380490033

theorem tailTrace_1890072 : CollatzResearch.WordTrace tailWord_1890072 prefixEnd_1890072 143780060385901380490033 := by
  unfold tailWord_1890072
  simp only [CollatzResearch.WordTrace]
  refine ⟨34468294604299708721700235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45957726139066278295600313 34468294604299708721700235)
  ·
    refine ⟨51702441906449563082550353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34468294604299708721700235 51702441906449563082550353)
    ·
      refine ⟨38776831429837172311912765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51702441906449563082550353 38776831429837172311912765)
      ·
        refine ⟨14541311786188939616967287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38776831429837172311912765 14541311786188939616967287)
        ·
          refine ⟨21811967679283409425450931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14541311786188939616967287 21811967679283409425450931)
          ·
            refine ⟨32717951518925114138176397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21811967679283409425450931 32717951518925114138176397)
            ·
              refine ⟨12269231819596917801816149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32717951518925114138176397 12269231819596917801816149)
              ·
                refine ⟨143780060385901380490033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12269231819596917801816149 143780060385901380490033)
                ·
                  rfl

theorem cell21_1890072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 8].length) (baseStart_1890072 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1890072 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1890072 prefixEnd_1890072 := by exact prefixLift 1890072
  have htrace : WordTrace (prefixWord ++ tailWord_1890072) baseStart_1890072 baseEnd_1890072 := by
    simpa [prefixWord, tailWord_1890072, baseEnd_1890072] using wordTrace_append hprefix tailTrace_1890072
  have hstable : (prefixWord ++ tailWord_1890072).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1890072).length < 2 ^ (prefixWord ++ tailWord_1890072).sum := by decide
  have hdescent : baseEnd_1890072 < baseStart_1890072 := by decide
  rcases family_descends (prefixWord ++ tailWord_1890072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1890179 : List Nat := [1, 1, 1, 3, 4, 2, 1, 3, 5]
def baseStart_1890179 : Nat := 118140960795 + 1890179 * 2 ^ 59
def prefixEnd_1890179 : Nat := 4983230072969 + 3 ^ 40 * 1890179 * 2
def baseEnd_1890179 : Nat := 431364600015495733186547

theorem tailTrace_1890179 : CollatzResearch.WordTrace tailWord_1890179 prefixEnd_1890179 431364600015495733186547 := by
  unfold tailWord_1890179
  simp only [CollatzResearch.WordTrace]
  refine ⟨68940491819211774717545591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45960327879474516478363727 68940491819211774717545591)
  ·
    refine ⟨103410737728817662076318387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68940491819211774717545591 103410737728817662076318387)
    ·
      refine ⟨155116106593226493114477581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103410737728817662076318387 155116106593226493114477581)
      ·
        refine ⟨58168539972459934917929093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155116106593226493114477581 58168539972459934917929093)
        ·
          refine ⟨10906601244836237797111705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58168539972459934917929093 10906601244836237797111705)
          ·
            refine ⟨8179950933627178347833779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10906601244836237797111705 8179950933627178347833779)
            ·
              refine ⟨12269926400440767521750669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8179950933627178347833779 12269926400440767521750669)
              ·
                refine ⟨4601222400165287820656501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12269926400440767521750669 4601222400165287820656501)
                ·
                  refine ⟨431364600015495733186547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4601222400165287820656501 431364600015495733186547)
                  ·
                    rfl

theorem cell21_1890179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 3, 5].length) (baseStart_1890179 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1890179 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1890179 prefixEnd_1890179 := by exact prefixLift 1890179
  have htrace : WordTrace (prefixWord ++ tailWord_1890179) baseStart_1890179 baseEnd_1890179 := by
    simpa [prefixWord, tailWord_1890179, baseEnd_1890179] using wordTrace_append hprefix tailTrace_1890179
  have hstable : (prefixWord ++ tailWord_1890179).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1890179).length < 2 ^ (prefixWord ++ tailWord_1890179).sum := by decide
  have hdescent : baseEnd_1890179 < baseStart_1890179 := by decide
  rcases family_descends (prefixWord ++ tailWord_1890179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1890196 : List Nat := [2, 4, 2, 1, 1, 2, 2, 2, 5]
def baseStart_1890196 : Nat := 118140960795 + 1890196 * 2 ^ 59
def prefixEnd_1890196 : Nat := 4983230072969 + 3 ^ 40 * 1890196 * 2
def baseEnd_1890196 : Nat := 431368479647107481403179

theorem tailTrace_1890196 : CollatzResearch.WordTrace tailWord_1890196 prefixEnd_1890196 431368479647107481403179 := by
  unfold tailWord_1890196
  simp only [CollatzResearch.WordTrace]
  refine ⟨34470555930075093310457221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45960741240100124413942961 34470555930075093310457221)
  ·
    refine ⟨6463229236889079995710729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34470555930075093310457221 6463229236889079995710729)
    ·
      refine ⟨4847421927666809996783047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6463229236889079995710729 4847421927666809996783047)
      ·
        refine ⟨7271132891500214995174571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4847421927666809996783047 7271132891500214995174571)
        ·
          refine ⟨10906699337250322492761857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7271132891500214995174571 10906699337250322492761857)
          ·
            refine ⟨8180024502937741869571393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10906699337250322492761857 8180024502937741869571393)
            ·
              refine ⟨6135018377203306402178545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8180024502937741869571393 6135018377203306402178545)
              ·
                refine ⟨4601263782902479801633909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6135018377203306402178545 4601263782902479801633909)
                ·
                  refine ⟨431368479647107481403179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4601263782902479801633909 431368479647107481403179)
                  ·
                    rfl

theorem cell21_1890196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 2, 5].length) (baseStart_1890196 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1890196 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1890196 prefixEnd_1890196 := by exact prefixLift 1890196
  have htrace : WordTrace (prefixWord ++ tailWord_1890196) baseStart_1890196 baseEnd_1890196 := by
    simpa [prefixWord, tailWord_1890196, baseEnd_1890196] using wordTrace_append hprefix tailTrace_1890196
  have hstable : (prefixWord ++ tailWord_1890196).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1890196).length < 2 ^ (prefixWord ++ tailWord_1890196).sum := by decide
  have hdescent : baseEnd_1890196 < baseStart_1890196 := by decide
  rcases family_descends (prefixWord ++ tailWord_1890196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1890289 : List Nat := [1, 2, 2, 2, 5, 1, 1, 4, 3]
def baseStart_1890289 : Nat := 118140960795 + 1890289 * 2 ^ 59
def prefixEnd_1890289 : Nat := 4983230072969 + 3 ^ 40 * 1890289 * 2
def baseEnd_1890289 : Nat := 431389703514159986352989

theorem tailTrace_1890289 : CollatzResearch.WordTrace tailWord_1890289 prefixEnd_1890289 431389703514159986352989 := by
  unfold tailWord_1890289
  simp only [CollatzResearch.WordTrace]
  refine ⟨68944503848813263504049921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45963002565875509002699947 68944503848813263504049921)
  ·
    refine ⟨51708377886609947628037441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68944503848813263504049921 51708377886609947628037441)
    ·
      refine ⟨38781283414957460721028081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51708377886609947628037441 38781283414957460721028081)
      ·
        refine ⟨29085962561218095540771061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38781283414957460721028081 29085962561218095540771061)
        ·
          refine ⟨2726808990114196456947287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29085962561218095540771061 2726808990114196456947287)
          ·
            refine ⟨4090213485171294685420931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2726808990114196456947287 4090213485171294685420931)
            ·
              refine ⟨6135320227756942028131397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4090213485171294685420931 6135320227756942028131397)
              ·
                refine ⟨1150372542704426630274637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6135320227756942028131397 1150372542704426630274637)
                ·
                  refine ⟨431389703514159986352989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1150372542704426630274637 431389703514159986352989)
                  ·
                    rfl

theorem cell21_1890289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 4, 3].length) (baseStart_1890289 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1890289 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1890289 prefixEnd_1890289 := by exact prefixLift 1890289
  have htrace : WordTrace (prefixWord ++ tailWord_1890289) baseStart_1890289 baseEnd_1890289 := by
    simpa [prefixWord, tailWord_1890289, baseEnd_1890289] using wordTrace_append hprefix tailTrace_1890289
  have hstable : (prefixWord ++ tailWord_1890289).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1890289).length < 2 ^ (prefixWord ++ tailWord_1890289).sum := by decide
  have hdescent : baseEnd_1890289 < baseStart_1890289 := by decide
  rcases family_descends (prefixWord ++ tailWord_1890289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1890455 : List Nat := [1, 1, 3, 3, 4, 1, 2, 2, 4]
def baseStart_1890455 : Nat := 118140960795 + 1890455 * 2 ^ 59
def prefixEnd_1890455 : Nat := 4983230072969 + 3 ^ 40 * 1890455 * 2
def baseEnd_1890455 : Nat := 431427586975780586585983

theorem tailTrace_1890455 : CollatzResearch.WordTrace tailWord_1890455 prefixEnd_1890455 431427586975780586585983 := by
  unfold tailWord_1890455
  simp only [CollatzResearch.WordTrace]
  refine ⟨68950558366211873854592819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45967038910807915903061879 68950558366211873854592819)
  ·
    refine ⟨103425837549317810781889229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68950558366211873854592819 103425837549317810781889229)
    ·
      refine ⟨38784689080994179043208461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103425837549317810781889229 38784689080994179043208461)
      ·
        refine ⟨14544258405372817141203173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38784689080994179043208461 14544258405372817141203173)
        ·
          refine ⟨2727048451007403213975595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14544258405372817141203173 2727048451007403213975595)
          ·
            refine ⟨4090572676511104820963393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2727048451007403213975595 4090572676511104820963393)
            ·
              refine ⟨3067929507383328615722545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4090572676511104820963393 3067929507383328615722545)
              ·
                refine ⟨2300947130537496461791909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3067929507383328615722545 2300947130537496461791909)
                ·
                  refine ⟨431427586975780586585983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2300947130537496461791909 431427586975780586585983)
                  ·
                    rfl

theorem cell21_1890455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 2, 2, 4].length) (baseStart_1890455 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1890455 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1890455 prefixEnd_1890455 := by exact prefixLift 1890455
  have htrace : WordTrace (prefixWord ++ tailWord_1890455) baseStart_1890455 baseEnd_1890455 := by
    simpa [prefixWord, tailWord_1890455, baseEnd_1890455] using wordTrace_append hprefix tailTrace_1890455
  have hstable : (prefixWord ++ tailWord_1890455).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1890455).length < 2 ^ (prefixWord ++ tailWord_1890455).sum := by decide
  have hdescent : baseEnd_1890455 < baseStart_1890455 := by decide
  rcases family_descends (prefixWord ++ tailWord_1890455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1890511 : List Nat := [1, 1, 2, 1, 1, 3, 12]
def baseStart_1890511 : Nat := 118140960795 + 1890511 * 2 ^ 59
def prefixEnd_1890511 : Nat := 4983230072969 + 3 ^ 40 * 1890511 * 2
def baseEnd_1890511 : Nat := 47937818548748548183615

theorem tailTrace_1890511 : CollatzResearch.WordTrace tailWord_1890511 prefixEnd_1890511 47937818548748548183615 := by
  unfold tailWord_1890511
  simp only [CollatzResearch.WordTrace]
  refine ⟨68952600854008995418631387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45968400569339330279087591 68952600854008995418631387)
  ·
    refine ⟨103428901281013493127947081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68952600854008995418631387 103428901281013493127947081)
    ·
      refine ⟨77571675960760119845960311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103428901281013493127947081 77571675960760119845960311)
      ·
        refine ⟨116357513941140179768940467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77571675960760119845960311 116357513941140179768940467)
        ·
          refine ⟨174536270911710269653410701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116357513941140179768940467 174536270911710269653410701)
          ·
            refine ⟨65451101591891351120029013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 174536270911710269653410701 65451101591891351120029013)
            ·
              refine ⟨47937818548748548183615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 65451101591891351120029013 47937818548748548183615)
              ·
                rfl

theorem cell21_1890511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 12].length) (baseStart_1890511 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1890511 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1890511 prefixEnd_1890511 := by exact prefixLift 1890511
  have htrace : WordTrace (prefixWord ++ tailWord_1890511) baseStart_1890511 baseEnd_1890511 := by
    simpa [prefixWord, tailWord_1890511, baseEnd_1890511] using wordTrace_append hprefix tailTrace_1890511
  have hstable : (prefixWord ++ tailWord_1890511).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1890511).length < 2 ^ (prefixWord ++ tailWord_1890511).sum := by decide
  have hdescent : baseEnd_1890511 < baseStart_1890511 := by decide
  rcases family_descends (prefixWord ++ tailWord_1890511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1890514 : List Nat := [3, 2, 2, 2, 1, 3, 1, 1, 6]
def baseStart_1890514 : Nat := 118140960795 + 1890514 * 2 ^ 59
def prefixEnd_1890514 : Nat := 4983230072969 + 3 ^ 40 * 1890514 * 2
def baseEnd_1890514 : Nat := 431441051579609595102529

theorem tailTrace_1890514 : CollatzResearch.WordTrace tailWord_1890514 prefixEnd_1890514 431441051579609595102529 := by
  unfold tailWord_1890514
  simp only [CollatzResearch.WordTrace]
  refine ⟨17238177568249531732747649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45968473515332084620660397 17238177568249531732747649)
  ·
    refine ⟨12928633176187148799560737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17238177568249531732747649 12928633176187148799560737)
    ·
      refine ⟨9696474882140361599670553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12928633176187148799560737 9696474882140361599670553)
      ·
        refine ⟨7272356161605271199752915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9696474882140361599670553 7272356161605271199752915)
        ·
          refine ⟨10908534242407906799629373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7272356161605271199752915 10908534242407906799629373)
          ·
            refine ⟨4090700340902965049861015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10908534242407906799629373 4090700340902965049861015)
            ·
              refine ⟨6136050511354447574791523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4090700340902965049861015 6136050511354447574791523)
              ·
                refine ⟨9204075767031671362187285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6136050511354447574791523 9204075767031671362187285)
                ·
                  refine ⟨431441051579609595102529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9204075767031671362187285 431441051579609595102529)
                  ·
                    rfl

theorem cell21_1890514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 1, 6].length) (baseStart_1890514 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1890514 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1890514 prefixEnd_1890514 := by exact prefixLift 1890514
  have htrace : WordTrace (prefixWord ++ tailWord_1890514) baseStart_1890514 baseEnd_1890514 := by
    simpa [prefixWord, tailWord_1890514, baseEnd_1890514] using wordTrace_append hprefix tailTrace_1890514
  have hstable : (prefixWord ++ tailWord_1890514).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1890514).length < 2 ^ (prefixWord ++ tailWord_1890514).sum := by decide
  have hdescent : baseEnd_1890514 < baseStart_1890514 := by decide
  rcases family_descends (prefixWord ++ tailWord_1890514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1890587 : List Nat := [1, 1, 1, 1, 1, 1, 7, 8]
def baseStart_1890587 : Nat := 118140960795 + 1890587 * 2 ^ 59
def prefixEnd_1890587 : Nat := 4983230072969 + 3 ^ 40 * 1890587 * 2
def baseEnd_1890587 : Nat := 143819237058059230128571

theorem tailTrace_1890587 : CollatzResearch.WordTrace tailWord_1890587 prefixEnd_1890587 143819237058059230128571 := by
  unfold tailWord_1890587
  simp only [CollatzResearch.WordTrace]
  refine ⟨68955372801733660398398015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45970248534489106932265343 68955372801733660398398015)
  ·
    refine ⟨103433059202600490597597023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68955372801733660398398015 103433059202600490597597023)
    ·
      refine ⟨155149588803900735896395535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103433059202600490597597023 155149588803900735896395535)
      ·
        refine ⟨232724383205851103844593303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155149588803900735896395535 232724383205851103844593303)
        ·
          refine ⟨349086574808776655766889955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232724383205851103844593303 349086574808776655766889955)
          ·
            refine ⟨523629862213164983650334933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 349086574808776655766889955 523629862213164983650334933)
            ·
              refine ⟨12272574895621054304304725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 523629862213164983650334933 12272574895621054304304725)
              ·
                refine ⟨143819237058059230128571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12272574895621054304304725 143819237058059230128571)
                ·
                  rfl

theorem cell21_1890587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 8].length) (baseStart_1890587 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1890587 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1890587 prefixEnd_1890587 := by exact prefixLift 1890587
  have htrace : WordTrace (prefixWord ++ tailWord_1890587) baseStart_1890587 baseEnd_1890587 := by
    simpa [prefixWord, tailWord_1890587, baseEnd_1890587] using wordTrace_append hprefix tailTrace_1890587
  have hstable : (prefixWord ++ tailWord_1890587).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1890587).length < 2 ^ (prefixWord ++ tailWord_1890587).sum := by decide
  have hdescent : baseEnd_1890587 < baseStart_1890587 := by decide
  rcases family_descends (prefixWord ++ tailWord_1890587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1890745 : List Nat := [1, 2, 1, 4, 3, 2, 3, 2, 3]
def baseStart_1890745 : Nat := 118140960795 + 1890745 * 2 ^ 59
def prefixEnd_1890745 : Nat := 4983230072969 + 3 ^ 40 * 1890745 * 2
def baseEnd_1890745 : Nat := 431493768926804526752057

theorem tailTrace_1890745 : CollatzResearch.WordTrace tailWord_1890745 prefixEnd_1890745 431493768926804526752057 := by
  unfold tailWord_1890745
  simp only [CollatzResearch.WordTrace]
  refine ⟨68961135535161253382649689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45974090356774168921766459 68961135535161253382649689)
  ·
    refine ⟨51720851651370940036987267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68961135535161253382649689 51720851651370940036987267)
    ·
      refine ⟨77581277477056410055480901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51720851651370940036987267 77581277477056410055480901)
      ·
        refine ⟨14546489526948076885402669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77581277477056410055480901 14546489526948076885402669)
        ·
          refine ⟨5454933572605528832026001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14546489526948076885402669 5454933572605528832026001)
          ·
            refine ⟨4091200179454146624019501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5454933572605528832026001 4091200179454146624019501)
            ·
              refine ⟨1534200067295304984007313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4091200179454146624019501 1534200067295304984007313)
              ·
                refine ⟨1150650050471478738005485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1534200067295304984007313 1150650050471478738005485)
                ·
                  refine ⟨431493768926804526752057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1150650050471478738005485 431493768926804526752057)
                  ·
                    rfl

theorem cell21_1890745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 3, 2, 3].length) (baseStart_1890745 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1890745 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1890745 prefixEnd_1890745 := by exact prefixLift 1890745
  have htrace : WordTrace (prefixWord ++ tailWord_1890745) baseStart_1890745 baseEnd_1890745 := by
    simpa [prefixWord, tailWord_1890745, baseEnd_1890745] using wordTrace_append hprefix tailTrace_1890745
  have hstable : (prefixWord ++ tailWord_1890745).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1890745).length < 2 ^ (prefixWord ++ tailWord_1890745).sum := by decide
  have hdescent : baseEnd_1890745 < baseStart_1890745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1890745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1890759 : List Nat := [1, 1, 4, 1, 1, 6, 2, 1, 4]
def baseStart_1890759 : Nat := 118140960795 + 1890759 * 2 ^ 59
def prefixEnd_1890759 : Nat := 4983230072969 + 3 ^ 40 * 1890759 * 2
def baseEnd_1890759 : Nat := 431496963917543613518695

theorem tailTrace_1890759 : CollatzResearch.WordTrace tailWord_1890759 prefixEnd_1890759 431496963917543613518695 := by
  unfold tailWord_1890759
  simp only [CollatzResearch.WordTrace]
  refine ⟨68961646157110533773659331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45974430771407022515772887 68961646157110533773659331)
  ·
    refine ⟨103442469235665800660488997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68961646157110533773659331 103442469235665800660488997)
    ·
      refine ⟨19395462981687337623841687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103442469235665800660488997 19395462981687337623841687)
      ·
        refine ⟨29093194472531006435762531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19395462981687337623841687 29093194472531006435762531)
        ·
          refine ⟨43639791708796509653643797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29093194472531006435762531 43639791708796509653643797)
          ·
            refine ⟨2045615236349836390014553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 43639791708796509653643797 2045615236349836390014553)
            ·
              refine ⟨1534211427262377292510915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2045615236349836390014553 1534211427262377292510915)
              ·
                refine ⟨2301317140893565938766373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1534211427262377292510915 2301317140893565938766373)
                ·
                  refine ⟨431496963917543613518695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2301317140893565938766373 431496963917543613518695)
                  ·
                    rfl

theorem cell21_1890759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 2, 1, 4].length) (baseStart_1890759 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1890759 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1890759 prefixEnd_1890759 := by exact prefixLift 1890759
  have htrace : WordTrace (prefixWord ++ tailWord_1890759) baseStart_1890759 baseEnd_1890759 := by
    simpa [prefixWord, tailWord_1890759, baseEnd_1890759] using wordTrace_append hprefix tailTrace_1890759
  have hstable : (prefixWord ++ tailWord_1890759).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1890759).length < 2 ^ (prefixWord ++ tailWord_1890759).sum := by decide
  have hdescent : baseEnd_1890759 < baseStart_1890759 := by decide
  rcases family_descends (prefixWord ++ tailWord_1890759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1890852 : List Nat := [2, 3, 1, 5, 1, 2, 1, 2, 4]
def baseStart_1890852 : Nat := 118140960795 + 1890852 * 2 ^ 59
def prefixEnd_1890852 : Nat := 4983230072969 + 3 ^ 40 * 1890852 * 2
def baseEnd_1890852 : Nat := 431518187784596118468505

theorem tailTrace_1890852 : CollatzResearch.WordTrace tailWord_1890852 prefixEnd_1890852 431518187784596118468505 := by
  unfold tailWord_1890852
  simp only [CollatzResearch.WordTrace]
  refine ⟨34482519072886805328397405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45976692097182407104529873 34482519072886805328397405)
  ·
    refine ⟨12930944652332551998149027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34482519072886805328397405 12930944652332551998149027)
    ·
      refine ⟨19396416978498827997223541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12930944652332551998149027 19396416978498827997223541)
      ·
        refine ⟨1818414091734265124739707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19396416978498827997223541 1818414091734265124739707)
        ·
          refine ⟨2727621137601397687109561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1818414091734265124739707 2727621137601397687109561)
          ·
            refine ⟨2045715853201048265332171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2727621137601397687109561 2045715853201048265332171)
            ·
              refine ⟨3068573779801572397998257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2045715853201048265332171 3068573779801572397998257)
              ·
                refine ⟨2301430334851179298498693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3068573779801572397998257 2301430334851179298498693)
                ·
                  refine ⟨431518187784596118468505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2301430334851179298498693 431518187784596118468505)
                  ·
                    rfl

theorem cell21_1890852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 1, 2, 4].length) (baseStart_1890852 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1890852 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1890852 prefixEnd_1890852 := by exact prefixLift 1890852
  have htrace : WordTrace (prefixWord ++ tailWord_1890852) baseStart_1890852 baseEnd_1890852 := by
    simpa [prefixWord, tailWord_1890852, baseEnd_1890852] using wordTrace_append hprefix tailTrace_1890852
  have hstable : (prefixWord ++ tailWord_1890852).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1890852).length < 2 ^ (prefixWord ++ tailWord_1890852).sum := by decide
  have hdescent : baseEnd_1890852 < baseStart_1890852 := by decide
  rcases family_descends (prefixWord ++ tailWord_1890852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1890914 : List Nat := [3, 3, 2, 3, 2, 1, 1, 1, 5]
def baseStart_1890914 : Nat := 118140960795 + 1890914 * 2 ^ 59
def prefixEnd_1890914 : Nat := 4983230072969 + 3 ^ 40 * 1890914 * 2
def baseEnd_1890914 : Nat := 431532337029297788435045

theorem tailTrace_1890914 : CollatzResearch.WordTrace tailWord_1890914 prefixEnd_1890914 431532337029297788435045 := by
  unfold tailWord_1890914
  simp only [CollatzResearch.WordTrace]
  refine ⟨17241824867887248811387949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45978199647699330163701197 17241824867887248811387949)
  ·
    refine ⟨6465684325457718304270481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17241824867887248811387949 6465684325457718304270481)
    ·
      refine ⟨4849263244093288728202861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6465684325457718304270481 4849263244093288728202861)
      ·
        refine ⟨1818473716534983273076073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4849263244093288728202861 1818473716534983273076073)
        ·
          refine ⟨1363855287401237454807055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1818473716534983273076073 1363855287401237454807055)
          ·
            refine ⟨2045782931101856182210583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1363855287401237454807055 2045782931101856182210583)
            ·
              refine ⟨3068674396652784273315875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2045782931101856182210583 3068674396652784273315875)
              ·
                refine ⟨4603011594979176409973813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3068674396652784273315875 4603011594979176409973813)
                ·
                  refine ⟨431532337029297788435045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4603011594979176409973813 431532337029297788435045)
                  ·
                    rfl

theorem cell21_1890914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 1, 1, 5].length) (baseStart_1890914 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1890914 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1890914 prefixEnd_1890914 := by exact prefixLift 1890914
  have htrace : WordTrace (prefixWord ++ tailWord_1890914) baseStart_1890914 baseEnd_1890914 := by
    simpa [prefixWord, tailWord_1890914, baseEnd_1890914] using wordTrace_append hprefix tailTrace_1890914
  have hstable : (prefixWord ++ tailWord_1890914).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1890914).length < 2 ^ (prefixWord ++ tailWord_1890914).sum := by decide
  have hdescent : baseEnd_1890914 < baseStart_1890914 := by decide
  rcases family_descends (prefixWord ++ tailWord_1890914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1890928 : List Nat := [2, 1, 1, 1, 8, 1, 2, 1, 4]
def baseStart_1890928 : Nat := 118140960795 + 1890928 * 2 ^ 59
def prefixEnd_1890928 : Nat := 4983230072969 + 3 ^ 40 * 1890928 * 2
def baseEnd_1890928 : Nat := 431535532020036875201683

theorem tailTrace_1890928 : CollatzResearch.WordTrace tailWord_1890928 prefixEnd_1890928 431535532020036875201683 := by
  unfold tailWord_1890928
  simp only [CollatzResearch.WordTrace]
  refine ⟨34483905046749137818280719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45978540062332183757707625 34483905046749137818280719)
  ·
    refine ⟨51725857570123706727421079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34483905046749137818280719 51725857570123706727421079)
    ·
      refine ⟨77588786355185560091131619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51725857570123706727421079 77588786355185560091131619)
      ·
        refine ⟨116383179532778340136697429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77588786355185560091131619 116383179532778340136697429)
        ·
          refine ⟨1363865385149746173476923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 116383179532778340136697429 1363865385149746173476923)
          ·
            refine ⟨2045798077724619260215385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1363865385149746173476923 2045798077724619260215385)
            ·
              refine ⟨1534348558293464445161539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2045798077724619260215385 1534348558293464445161539)
              ·
                refine ⟨2301522837440196667742309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1534348558293464445161539 2301522837440196667742309)
                ·
                  refine ⟨431535532020036875201683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2301522837440196667742309 431535532020036875201683)
                  ·
                    rfl

theorem cell21_1890928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 2, 1, 4].length) (baseStart_1890928 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1890928 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1890928 prefixEnd_1890928 := by exact prefixLift 1890928
  have htrace : WordTrace (prefixWord ++ tailWord_1890928) baseStart_1890928 baseEnd_1890928 := by
    simpa [prefixWord, tailWord_1890928, baseEnd_1890928] using wordTrace_append hprefix tailTrace_1890928
  have hstable : (prefixWord ++ tailWord_1890928).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1890928).length < 2 ^ (prefixWord ++ tailWord_1890928).sum := by decide
  have hdescent : baseEnd_1890928 < baseStart_1890928 := by decide
  rcases family_descends (prefixWord ++ tailWord_1890928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1891021 : List Nat := [1, 6, 2, 1, 3, 1, 1, 2, 4]
def baseStart_1891021 : Nat := 118140960795 + 1891021 * 2 ^ 59
def prefixEnd_1891021 : Nat := 4983230072969 + 3 ^ 40 * 1891021 * 2
def baseEnd_1891021 : Nat := 431556755887089380151493

theorem tailTrace_1891021 : CollatzResearch.WordTrace tailWord_1891021 prefixEnd_1891021 431556755887089380151493 := by
  unfold tailWord_1891021
  simp only [CollatzResearch.WordTrace]
  refine ⟨68971202082161352519696917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45980801388107568346464611 68971202082161352519696917)
  ·
    refine ⟨3233025097601313399360793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 68971202082161352519696917 3233025097601313399360793)
    ·
      refine ⟨2424768823200985049520595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3233025097601313399360793 2424768823200985049520595)
      ·
        refine ⟨3637153234801477574280893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2424768823200985049520595 3637153234801477574280893)
        ·
          refine ⟨1363932463050554090355335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3637153234801477574280893 1363932463050554090355335)
          ·
            refine ⟨2045898694575831135533003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1363932463050554090355335 2045898694575831135533003)
            ·
              refine ⟨3068848041863746703299505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2045898694575831135533003 3068848041863746703299505)
              ·
                refine ⟨2301636031397810027474629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3068848041863746703299505 2301636031397810027474629)
                ·
                  refine ⟨431556755887089380151493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2301636031397810027474629 431556755887089380151493)
                  ·
                    rfl

theorem cell21_1891021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 1, 2, 4].length) (baseStart_1891021 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1891021 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1891021 prefixEnd_1891021 := by exact prefixLift 1891021
  have htrace : WordTrace (prefixWord ++ tailWord_1891021) baseStart_1891021 baseEnd_1891021 := by
    simpa [prefixWord, tailWord_1891021, baseEnd_1891021] using wordTrace_append hprefix tailTrace_1891021
  have hstable : (prefixWord ++ tailWord_1891021).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1891021).length < 2 ^ (prefixWord ++ tailWord_1891021).sum := by decide
  have hdescent : baseEnd_1891021 < baseStart_1891021 := by decide
  rcases family_descends (prefixWord ++ tailWord_1891021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1891105 : List Nat := [1, 2, 3, 2, 1, 2, 3, 3, 4]
def baseStart_1891105 : Nat := 118140960795 + 1891105 * 2 ^ 59
def prefixEnd_1891105 : Nat := 4983230072969 + 3 ^ 40 * 1891105 * 2
def baseEnd_1891105 : Nat := 431575925831523900751321

theorem tailTrace_1891105 : CollatzResearch.WordTrace tailWord_1891105 prefixEnd_1891105 431575925831523900751321 := by
  unfold tailWord_1891105
  simp only [CollatzResearch.WordTrace]
  refine ⟨68974265813857034865754769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45982843875904689910503179 68974265813857034865754769)
  ·
    refine ⟨51730699360392776149316077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68974265813857034865754769 51730699360392776149316077)
    ·
      refine ⟨19399012260147291055993529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51730699360392776149316077 19399012260147291055993529)
      ·
        refine ⟨14549259195110468291995147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19399012260147291055993529 14549259195110468291995147)
        ·
          refine ⟨21823888792665702437992721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14549259195110468291995147 21823888792665702437992721)
          ·
            refine ⟨16367916594499276828494541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21823888792665702437992721 16367916594499276828494541)
            ·
              refine ⟨6137968722937228810685453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16367916594499276828494541 6137968722937228810685453)
              ·
                refine ⟨2301738271101460804007045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6137968722937228810685453 2301738271101460804007045)
                ·
                  refine ⟨431575925831523900751321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2301738271101460804007045 431575925831523900751321)
                  ·
                    rfl

theorem cell21_1891105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 3, 4].length) (baseStart_1891105 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1891105 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1891105 prefixEnd_1891105 := by exact prefixLift 1891105
  have htrace : WordTrace (prefixWord ++ tailWord_1891105) baseStart_1891105 baseEnd_1891105 := by
    simpa [prefixWord, tailWord_1891105, baseEnd_1891105] using wordTrace_append hprefix tailTrace_1891105
  have hstable : (prefixWord ++ tailWord_1891105).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1891105).length < 2 ^ (prefixWord ++ tailWord_1891105).sum := by decide
  have hdescent : baseEnd_1891105 < baseStart_1891105 := by decide
  rcases family_descends (prefixWord ++ tailWord_1891105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1891142 : List Nat := [6, 1, 1, 2, 2, 1, 1, 4, 3]
def baseStart_1891142 : Nat := 118140960795 + 1891142 * 2 ^ 59
def prefixEnd_1891142 : Nat := 4983230072969 + 3 ^ 40 * 1891142 * 2
def baseEnd_1891142 : Nat := 431584369735620058634579

theorem tailTrace_1891142 : CollatzResearch.WordTrace tailWord_1891142 prefixEnd_1891142 431584369735620058634579 := by
  unfold tailWord_1891142
  simp only [CollatzResearch.WordTrace]
  refine ⟨2155487978585093443276615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 45983743543148660123234453 2155487978585093443276615)
  ·
    refine ⟨3233231967877640164914923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2155487978585093443276615 3233231967877640164914923)
    ·
      refine ⟨4849847951816460247372385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3233231967877640164914923 4849847951816460247372385)
      ·
        refine ⟨3637385963862345185529289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4849847951816460247372385 3637385963862345185529289)
        ·
          refine ⟨2728039472896758889146967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3637385963862345185529289 2728039472896758889146967)
          ·
            refine ⟨4092059209345138333720451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2728039472896758889146967 4092059209345138333720451)
            ·
              refine ⟨6138088814017707500580677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4092059209345138333720451 6138088814017707500580677)
              ·
                refine ⟨1150891652628320156358877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6138088814017707500580677 1150891652628320156358877)
                ·
                  refine ⟨431584369735620058634579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1150891652628320156358877 431584369735620058634579)
                  ·
                    rfl

theorem cell21_1891142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 4, 3].length) (baseStart_1891142 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1891142 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1891142 prefixEnd_1891142 := by exact prefixLift 1891142
  have htrace : WordTrace (prefixWord ++ tailWord_1891142) baseStart_1891142 baseEnd_1891142 := by
    simpa [prefixWord, tailWord_1891142, baseEnd_1891142] using wordTrace_append hprefix tailTrace_1891142
  have hstable : (prefixWord ++ tailWord_1891142).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1891142).length < 2 ^ (prefixWord ++ tailWord_1891142).sum := by decide
  have hdescent : baseEnd_1891142 < baseStart_1891142 := by decide
  rcases family_descends (prefixWord ++ tailWord_1891142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1891153 : List Nat := [1, 2, 2, 1, 7, 1, 1, 6]
def baseStart_1891153 : Nat := 118140960795 + 1891153 * 2 ^ 59
def prefixEnd_1891153 : Nat := 4983230072969 + 3 ^ 40 * 1891153 * 2
def baseEnd_1891153 : Nat := 143862293361828827983741

theorem tailTrace_1891153 : CollatzResearch.WordTrace tailWord_1891153 prefixEnd_1891153 143862293361828827983741 := by
  unfold tailWord_1891153
  simp only [CollatzResearch.WordTrace]
  refine ⟨68976016517683139063502113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45984011011788759375668075 68976016517683139063502113)
  ·
    refine ⟨51732012388262354297626585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68976016517683139063502113 51732012388262354297626585)
    ·
      refine ⟨38799009291196765723219939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51732012388262354297626585 38799009291196765723219939)
      ·
        refine ⟨58198513936795148584829909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38799009291196765723219939 58198513936795148584829909)
        ·
          refine ⟨1364027670393636294956951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 58198513936795148584829909 1364027670393636294956951)
          ·
            refine ⟨2046041505590454442435427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1364027670393636294956951 2046041505590454442435427)
            ·
              refine ⟨3069062258385681663653141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2046041505590454442435427 3069062258385681663653141)
              ·
                refine ⟨143862293361828827983741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3069062258385681663653141 143862293361828827983741)
                ·
                  rfl

theorem cell21_1891153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 1, 6].length) (baseStart_1891153 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1891153 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1891153 prefixEnd_1891153 := by exact prefixLift 1891153
  have htrace : WordTrace (prefixWord ++ tailWord_1891153) baseStart_1891153 baseEnd_1891153 := by
    simpa [prefixWord, tailWord_1891153, baseEnd_1891153] using wordTrace_append hprefix tailTrace_1891153
  have hstable : (prefixWord ++ tailWord_1891153).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1891153).length < 2 ^ (prefixWord ++ tailWord_1891153).sum := by decide
  have hdescent : baseEnd_1891153 < baseStart_1891153 := by decide
  rcases family_descends (prefixWord ++ tailWord_1891153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1891367 : List Nat := [1, 1, 7, 1, 1, 3, 1, 2, 4]
def baseStart_1891367 : Nat := 118140960795 + 1891367 * 2 ^ 59
def prefixEnd_1891367 : Nat := 4983230072969 + 3 ^ 40 * 1891367 * 2
def baseEnd_1891367 : Nat := 431635717801069667384119

theorem tailTrace_1891367 : CollatzResearch.WordTrace tailWord_1891367 prefixEnd_1891367 431635717801069667384119 := by
  unfold tailWord_1891367
  simp only [CollatzResearch.WordTrace]
  refine ⟨68983821738907853611792355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45989214492605235741194903 68983821738907853611792355)
  ·
    refine ⟨103475732608361780417688533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68983821738907853611792355 103475732608361780417688533)
    ·
      refine ⟨2425212483008479228539575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 103475732608361780417688533 2425212483008479228539575)
      ·
        refine ⟨3637818724512718842809363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2425212483008479228539575 3637818724512718842809363)
        ·
          refine ⟨5456728086769078264214045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3637818724512718842809363 5456728086769078264214045)
          ·
            refine ⟨2046273032538404349080267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5456728086769078264214045 2046273032538404349080267)
            ·
              refine ⟨3069409548807606523620401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2046273032538404349080267 3069409548807606523620401)
              ·
                refine ⟨2302057161605704892715301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3069409548807606523620401 2302057161605704892715301)
                ·
                  refine ⟨431635717801069667384119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2302057161605704892715301 431635717801069667384119)
                  ·
                    rfl

theorem cell21_1891367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 1, 2, 4].length) (baseStart_1891367 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1891367 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1891367 prefixEnd_1891367 := by exact prefixLift 1891367
  have htrace : WordTrace (prefixWord ++ tailWord_1891367) baseStart_1891367 baseEnd_1891367 := by
    simpa [prefixWord, tailWord_1891367, baseEnd_1891367] using wordTrace_append hprefix tailTrace_1891367
  have hstable : (prefixWord ++ tailWord_1891367).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1891367).length < 2 ^ (prefixWord ++ tailWord_1891367).sum := by decide
  have hdescent : baseEnd_1891367 < baseStart_1891367 := by decide
  rcases family_descends (prefixWord ++ tailWord_1891367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1891378 : List Nat := [3, 2, 1, 1, 2, 2, 4, 1, 5]
def baseStart_1891378 : Nat := 118140960795 + 1891378 * 2 ^ 59
def prefixEnd_1891378 : Nat := 4983230072969 + 3 ^ 40 * 1891378 * 2
def baseEnd_1891378 : Nat := 431638228150936092700763

theorem tailTrace_1891378 : CollatzResearch.WordTrace tailWord_1891378 prefixEnd_1891378 431638228150936092700763 := by
  unfold tailWord_1891378
  simp only [CollatzResearch.WordTrace]
  refine ⟨17246055735467000622610697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45989481961245334993628525 17246055735467000622610697)
  ·
    refine ⟨12934541801600250466958023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17246055735467000622610697 12934541801600250466958023)
    ·
      refine ⟨19401812702400375700437035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12934541801600250466958023 19401812702400375700437035)
      ·
        refine ⟨29102719053600563550655553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19401812702400375700437035 29102719053600563550655553)
        ·
          refine ⟨21827039290200422662991665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29102719053600563550655553 21827039290200422662991665)
          ·
            refine ⟨16370279467650316997243749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21827039290200422662991665 16370279467650316997243749)
            ·
              refine ⟨3069427400184434436983203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16370279467650316997243749 3069427400184434436983203)
              ·
                refine ⟨4604141100276651655474805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3069427400184434436983203 4604141100276651655474805)
                ·
                  refine ⟨431638228150936092700763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4604141100276651655474805 431638228150936092700763)
                  ·
                    rfl

theorem cell21_1891378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 4, 1, 5].length) (baseStart_1891378 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1891378 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1891378 prefixEnd_1891378 := by exact prefixLift 1891378
  have htrace : WordTrace (prefixWord ++ tailWord_1891378) baseStart_1891378 baseEnd_1891378 := by
    simpa [prefixWord, tailWord_1891378, baseEnd_1891378] using wordTrace_append hprefix tailTrace_1891378
  have hstable : (prefixWord ++ tailWord_1891378).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1891378).length < 2 ^ (prefixWord ++ tailWord_1891378).sum := by decide
  have hdescent : baseEnd_1891378 < baseStart_1891378 := by decide
  rcases family_descends (prefixWord ++ tailWord_1891378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1891398 : List Nat := [6, 1, 1, 1, 1, 4, 2, 5]
def baseStart_1891398 : Nat := 118140960795 + 1891398 * 2 ^ 59
def prefixEnd_1891398 : Nat := 4983230072969 + 3 ^ 40 * 1891398 * 2
def baseEnd_1891398 : Nat := 143880930807806834122463

theorem tailTrace_1891398 : CollatzResearch.WordTrace tailWord_1891398 prefixEnd_1891398 143880930807806834122463 := by
  unfold tailWord_1891398
  simp only [CollatzResearch.WordTrace]
  refine ⟨2155779762556110809567839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 45989968267863697270780565 2155779762556110809567839)
  ·
    refine ⟨3233669643834166214351759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2155779762556110809567839 3233669643834166214351759)
    ·
      refine ⟨4850504465751249321527639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3233669643834166214351759 4850504465751249321527639)
      ·
        refine ⟨7275756698626873982291459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4850504465751249321527639 7275756698626873982291459)
        ·
          refine ⟨10913635047940310973437189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7275756698626873982291459 10913635047940310973437189)
          ·
            refine ⟨2046306571488808307519473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10913635047940310973437189 2046306571488808307519473)
            ·
              refine ⟨1534729928616606230639605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2046306571488808307519473 1534729928616606230639605)
              ·
                refine ⟨143880930807806834122463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1534729928616606230639605 143880930807806834122463)
                ·
                  rfl

theorem cell21_1891398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 2, 5].length) (baseStart_1891398 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1891398 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1891398 prefixEnd_1891398 := by exact prefixLift 1891398
  have htrace : WordTrace (prefixWord ++ tailWord_1891398) baseStart_1891398 baseEnd_1891398 := by
    simpa [prefixWord, tailWord_1891398, baseEnd_1891398] using wordTrace_append hprefix tailTrace_1891398
  have hstable : (prefixWord ++ tailWord_1891398).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1891398).length < 2 ^ (prefixWord ++ tailWord_1891398).sum := by decide
  have hdescent : baseEnd_1891398 < baseStart_1891398 := by decide
  rcases family_descends (prefixWord ++ tailWord_1891398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1891485 : List Nat := [1, 4, 2, 1, 1, 2, 4, 2, 4]
def baseStart_1891485 : Nat := 118140960795 + 1891485 * 2 ^ 59
def prefixEnd_1891485 : Nat := 4983230072969 + 3 ^ 40 * 1891485 * 2
def baseEnd_1891485 : Nat := 431662647008727684417211

theorem tailTrace_1891485 : CollatzResearch.WordTrace tailWord_1891485 prefixEnd_1891485 431662647008727684417211 := by
  unfold tailWord_1891485
  simp only [CollatzResearch.WordTrace]
  refine ⟨68988125552480359764587909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45992083701653573176391939 68988125552480359764587909)
  ·
    refine ⟨12935273541090067455860233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68988125552480359764587909 12935273541090067455860233)
    ·
      refine ⟨9701455155817550591895175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12935273541090067455860233 9701455155817550591895175)
      ·
        refine ⟨14552182733726325887842763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9701455155817550591895175 14552182733726325887842763)
        ·
          refine ⟨21828274100589488831764145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14552182733726325887842763 21828274100589488831764145)
          ·
            refine ⟨16371205575442116623823109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21828274100589488831764145 16371205575442116623823109)
            ·
              refine ⟨3069601045395396866966833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16371205575442116623823109 3069601045395396866966833)
              ·
                refine ⟨2302200784046547650225125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3069601045395396866966833 2302200784046547650225125)
                ·
                  refine ⟨431662647008727684417211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2302200784046547650225125 431662647008727684417211)
                  ·
                    rfl

theorem cell21_1891485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 4, 2, 4].length) (baseStart_1891485 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1891485 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1891485 prefixEnd_1891485 := by exact prefixLift 1891485
  have htrace : WordTrace (prefixWord ++ tailWord_1891485) baseStart_1891485 baseEnd_1891485 := by
    simpa [prefixWord, tailWord_1891485, baseEnd_1891485] using wordTrace_append hprefix tailTrace_1891485
  have hstable : (prefixWord ++ tailWord_1891485).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1891485).length < 2 ^ (prefixWord ++ tailWord_1891485).sum := by decide
  have hdescent : baseEnd_1891485 < baseStart_1891485 := by decide
  rcases family_descends (prefixWord ++ tailWord_1891485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1891513 : List Nat := [1, 2, 1, 4, 1, 3, 1, 1, 7]
def baseStart_1891513 : Nat := 118140960795 + 1891513 * 2 ^ 59
def prefixEnd_1891513 : Nat := 4983230072969 + 3 ^ 40 * 1891513 * 2
def baseEnd_1891513 : Nat := 431669036990205857950487

theorem tailTrace_1891513 : CollatzResearch.WordTrace tailWord_1891513 prefixEnd_1891513 431669036990205857950487 := by
  unfold tailWord_1891513
  simp only [CollatzResearch.WordTrace]
  refine ⟨68989146796378920546607193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45992764530919280364404795 68989146796378920546607193)
  ·
    refine ⟨51741860097284190409955395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68989146796378920546607193 51741860097284190409955395)
    ·
      refine ⟨77612790145926285614933093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51741860097284190409955395 77612790145926285614933093)
      ·
        refine ⟨14552398152361178552799955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77612790145926285614933093 14552398152361178552799955)
        ·
          refine ⟨21828597228541767829199933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14552398152361178552799955 21828597228541767829199933)
          ·
            refine ⟨8185723960703162935949975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21828597228541767829199933 8185723960703162935949975)
            ·
              refine ⟨12278585941054744403924963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8185723960703162935949975 12278585941054744403924963)
              ·
                refine ⟨18417878911582116605887445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12278585941054744403924963 18417878911582116605887445)
                ·
                  refine ⟨431669036990205857950487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18417878911582116605887445 431669036990205857950487)
                  ·
                    rfl

theorem cell21_1891513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 1, 7].length) (baseStart_1891513 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1891513 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1891513 prefixEnd_1891513 := by exact prefixLift 1891513
  have htrace : WordTrace (prefixWord ++ tailWord_1891513) baseStart_1891513 baseEnd_1891513 := by
    simpa [prefixWord, tailWord_1891513, baseEnd_1891513] using wordTrace_append hprefix tailTrace_1891513
  have hstable : (prefixWord ++ tailWord_1891513).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1891513).length < 2 ^ (prefixWord ++ tailWord_1891513).sum := by decide
  have hdescent : baseEnd_1891513 < baseStart_1891513 := by decide
  rcases family_descends (prefixWord ++ tailWord_1891513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1891516 : List Nat := [2, 2, 2, 3, 2, 2, 3, 5]
def baseStart_1891516 : Nat := 118140960795 + 1891516 * 2 ^ 59
def prefixEnd_1891516 : Nat := 4983230072969 + 3 ^ 40 * 1891516 * 2
def baseEnd_1891516 : Nat := 143889907210359506466827

theorem tailTrace_1891516 : CollatzResearch.WordTrace tailWord_1891516 prefixEnd_1891516 143889907210359506466827 := by
  unfold tailWord_1891516
  simp only [CollatzResearch.WordTrace]
  refine ⟨34494628107684026029483201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45992837476912034705977601 34494628107684026029483201)
  ·
    refine ⟨25870971080763019522112401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34494628107684026029483201 25870971080763019522112401)
    ·
      refine ⟨19403228310572264641584301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25870971080763019522112401 19403228310572264641584301)
      ·
        refine ⟨7276210616464599240594113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19403228310572264641584301 7276210616464599240594113)
        ·
          refine ⟨5457157962348449430445585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7276210616464599240594113 5457157962348449430445585)
          ·
            refine ⟨4092868471761337072834189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5457157962348449430445585 4092868471761337072834189)
            ·
              refine ⟨1534825676910501402312821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4092868471761337072834189 1534825676910501402312821)
              ·
                refine ⟨143889907210359506466827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1534825676910501402312821 143889907210359506466827)
                ·
                  rfl

theorem cell21_1891516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 3, 5].length) (baseStart_1891516 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1891516 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1891516 prefixEnd_1891516 := by exact prefixLift 1891516
  have htrace : WordTrace (prefixWord ++ tailWord_1891516) baseStart_1891516 baseEnd_1891516 := by
    simpa [prefixWord, tailWord_1891516, baseEnd_1891516] using wordTrace_append hprefix tailTrace_1891516
  have hstable : (prefixWord ++ tailWord_1891516).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1891516).length < 2 ^ (prefixWord ++ tailWord_1891516).sum := by decide
  have hdescent : baseEnd_1891516 < baseStart_1891516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1891516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1891522 : List Nat := [3, 5, 1, 1, 2, 1, 2, 3, 3]
def baseStart_1891522 : Nat := 118140960795 + 1891522 * 2 ^ 59
def prefixEnd_1891522 : Nat := 4983230072969 + 3 ^ 40 * 1891522 * 2
def baseEnd_1891522 : Nat := 431671090912823842300469

theorem tailTrace_1891522 : CollatzResearch.WordTrace tailWord_1891522 prefixEnd_1891522 431671090912823842300469 := by
  unfold tailWord_1891522
  simp only [CollatzResearch.WordTrace]
  refine ⟨17247368763336578770921205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45992983368897543389123213 17247368763336578770921205)
  ·
    refine ⟨1616940821562804259773863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17247368763336578770921205 1616940821562804259773863)
    ·
      refine ⟨2425411232344206389660795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1616940821562804259773863 2425411232344206389660795)
      ·
        refine ⟨3638116848516309584491193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2425411232344206389660795 3638116848516309584491193)
        ·
          refine ⟨2728587636387232188368395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3638116848516309584491193 2728587636387232188368395)
          ·
            refine ⟨4092881454580848282552593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2728587636387232188368395 4092881454580848282552593)
            ·
              refine ⟨3069661090935636211914445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4092881454580848282552593 3069661090935636211914445)
              ·
                refine ⟨1151122909100863579467917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3069661090935636211914445 1151122909100863579467917)
                ·
                  refine ⟨431671090912823842300469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1151122909100863579467917 431671090912823842300469)
                  ·
                    rfl

theorem cell21_1891522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_1891522 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1891522 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1891522 prefixEnd_1891522 := by exact prefixLift 1891522
  have htrace : WordTrace (prefixWord ++ tailWord_1891522) baseStart_1891522 baseEnd_1891522 := by
    simpa [prefixWord, tailWord_1891522, baseEnd_1891522] using wordTrace_append hprefix tailTrace_1891522
  have hstable : (prefixWord ++ tailWord_1891522).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1891522).length < 2 ^ (prefixWord ++ tailWord_1891522).sum := by decide
  have hdescent : baseEnd_1891522 < baseStart_1891522 := by decide
  rcases family_descends (prefixWord ++ tailWord_1891522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1891533 : List Nat := [1, 6, 2, 2, 1, 1, 8]
def baseStart_1891533 : Nat := 118140960795 + 1891533 * 2 ^ 59
def prefixEnd_1891533 : Nat := 4983230072969 + 3 ^ 40 * 1891533 * 2
def baseEnd_1891533 : Nat := 47963733473632251957457

theorem tailTrace_1891533 : CollatzResearch.WordTrace tailWord_1891533 prefixEnd_1891533 47963733473632251957457 := by
  unfold tailWord_1891533
  simp only [CollatzResearch.WordTrace]
  refine ⟨68989876256306463962335253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45993250837537642641556835 68989876256306463962335253)
  ·
    refine ⟨3233900449514365498234465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 68989876256306463962335253 3233900449514365498234465)
    ·
      refine ⟨2425425337135774123675849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3233900449514365498234465 2425425337135774123675849)
      ·
        refine ⟨1819069002851830592756887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2425425337135774123675849 1819069002851830592756887)
        ·
          refine ⟨2728603504277745889135331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1819069002851830592756887 2728603504277745889135331)
          ·
            refine ⟨4092905256416618833702997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2728603504277745889135331 4092905256416618833702997)
            ·
              refine ⟨47963733473632251957457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4092905256416618833702997 47963733473632251957457)
              ·
                rfl

theorem cell21_1891533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 8].length) (baseStart_1891533 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1891533 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1891533 prefixEnd_1891533 := by exact prefixLift 1891533
  have htrace : WordTrace (prefixWord ++ tailWord_1891533) baseStart_1891533 baseEnd_1891533 := by
    simpa [prefixWord, tailWord_1891533, baseEnd_1891533] using wordTrace_append hprefix tailTrace_1891533
  have hstable : (prefixWord ++ tailWord_1891533).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1891533).length < 2 ^ (prefixWord ++ tailWord_1891533).sum := by decide
  have hdescent : baseEnd_1891533 < baseStart_1891533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1891533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1891592 : List Nat := [2, 1, 3, 2, 5, 1, 7]
def baseStart_1891592 : Nat := 118140960795 + 1891592 * 2 ^ 59
def prefixEnd_1891592 : Nat := 4983230072969 + 3 ^ 40 * 1891592 * 2
def baseEnd_1891592 : Nat := 47965229540724364014851

theorem tailTrace_1891592 : CollatzResearch.WordTrace tailWord_1891592 prefixEnd_1891592 47965229540724364014851 := by
  unfold tailWord_1891592
  simp only [CollatzResearch.WordTrace]
  refine ⟨34496014081546358519366515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45994685442061811359155353 34496014081546358519366515)
  ·
    refine ⟨51744021122319537779049773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34496014081546358519366515 51744021122319537779049773)
    ·
      refine ⟨19404007920869826667143665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51744021122319537779049773 19404007920869826667143665)
      ·
        refine ⟨14553005940652370000357749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19404007920869826667143665 14553005940652370000357749)
        ·
          refine ⟨1364344306936159687533539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14553005940652370000357749 1364344306936159687533539)
          ·
            refine ⟨2046516460404239531300309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1364344306936159687533539 2046516460404239531300309)
            ·
              refine ⟨47965229540724364014851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2046516460404239531300309 47965229540724364014851)
              ·
                rfl

theorem cell21_1891592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 7].length) (baseStart_1891592 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1891592 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1891592 prefixEnd_1891592 := by exact prefixLift 1891592
  have htrace : WordTrace (prefixWord ++ tailWord_1891592) baseStart_1891592 baseEnd_1891592 := by
    simpa [prefixWord, tailWord_1891592, baseEnd_1891592] using wordTrace_append hprefix tailTrace_1891592
  have hstable : (prefixWord ++ tailWord_1891592).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1891592).length < 2 ^ (prefixWord ++ tailWord_1891592).sum := by decide
  have hdescent : baseEnd_1891592 < baseStart_1891592 := by decide
  rcases family_descends (prefixWord ++ tailWord_1891592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1891665 : List Nat := [1, 2, 2, 1, 4, 1, 2, 3, 5]
def baseStart_1891665 : Nat := 118140960795 + 1891665 * 2 ^ 59
def prefixEnd_1891665 : Nat := 4983230072969 + 3 ^ 40 * 1891665 * 2
def baseEnd_1891665 : Nat := 431703725461087371416843

theorem tailTrace_1891665 : CollatzResearch.WordTrace tailWord_1891665 prefixEnd_1891665 431703725461087371416843 := by
  unfold tailWord_1891665
  simp only [CollatzResearch.WordTrace]
  refine ⟨68994690691828250506140449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45996460461218833670760299 68994690691828250506140449)
  ·
    refine ⟨51746018018871187879605337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68994690691828250506140449 51746018018871187879605337)
    ·
      refine ⟨38809513514153390909704003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51746018018871187879605337 38809513514153390909704003)
      ·
        refine ⟨58214270271230086364556005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38809513514153390909704003 58214270271230086364556005)
        ·
          refine ⟨10915175675855641193354251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58214270271230086364556005 10915175675855641193354251)
          ·
            refine ⟨16372763513783461790031377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10915175675855641193354251 16372763513783461790031377)
            ·
              refine ⟨12279572635337596342523533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16372763513783461790031377 12279572635337596342523533)
              ·
                refine ⟨4604839738251598628446325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12279572635337596342523533 4604839738251598628446325)
                ·
                  refine ⟨431703725461087371416843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4604839738251598628446325 431703725461087371416843)
                  ·
                    rfl

theorem cell21_1891665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 3, 5].length) (baseStart_1891665 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1891665 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1891665 prefixEnd_1891665 := by exact prefixLift 1891665
  have htrace : WordTrace (prefixWord ++ tailWord_1891665) baseStart_1891665 baseEnd_1891665 := by
    simpa [prefixWord, tailWord_1891665, baseEnd_1891665] using wordTrace_append hprefix tailTrace_1891665
  have hstable : (prefixWord ++ tailWord_1891665).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1891665).length < 2 ^ (prefixWord ++ tailWord_1891665).sum := by decide
  have hdescent : baseEnd_1891665 < baseStart_1891665 := by decide
  rcases family_descends (prefixWord ++ tailWord_1891665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1891679 : List Nat := [1, 1, 2, 3, 1, 2, 1, 2, 8]
def baseStart_1891679 : Nat := 118140960795 + 1891679 * 2 ^ 59
def prefixEnd_1891679 : Nat := 4983230072969 + 3 ^ 40 * 1891679 * 2
def baseEnd_1891679 : Nat := 431706920451826458183481

theorem tailTrace_1891679 : CollatzResearch.WordTrace tailWord_1891679 prefixEnd_1891679 431706920451826458183481 := by
  unfold tailWord_1891679
  simp only [CollatzResearch.WordTrace]
  refine ⟨68995201313777530897150091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45996800875851687264766727 68995201313777530897150091)
  ·
    refine ⟨103492801970666296345725137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68995201313777530897150091 103492801970666296345725137)
    ·
      refine ⟨77619601477999722259293853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103492801970666296345725137 77619601477999722259293853)
      ·
        refine ⟨29107350554249895847235195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77619601477999722259293853 29107350554249895847235195)
        ·
          refine ⟨43661025831374843770852793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29107350554249895847235195 43661025831374843770852793)
          ·
            refine ⟨32745769373531132828139595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43661025831374843770852793 32745769373531132828139595)
            ·
              refine ⟨49118654060296699242209393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32745769373531132828139595 49118654060296699242209393)
              ·
                refine ⟨36838990545222524431657045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49118654060296699242209393 36838990545222524431657045)
                ·
                  refine ⟨431706920451826458183481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36838990545222524431657045 431706920451826458183481)
                  ·
                    rfl

theorem cell21_1891679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 2, 8].length) (baseStart_1891679 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1891679 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1891679 prefixEnd_1891679 := by exact prefixLift 1891679
  have htrace : WordTrace (prefixWord ++ tailWord_1891679) baseStart_1891679 baseEnd_1891679 := by
    simpa [prefixWord, tailWord_1891679, baseEnd_1891679] using wordTrace_append hprefix tailTrace_1891679
  have hstable : (prefixWord ++ tailWord_1891679).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1891679).length < 2 ^ (prefixWord ++ tailWord_1891679).sum := by decide
  have hdescent : baseEnd_1891679 < baseStart_1891679 := by decide
  rcases family_descends (prefixWord ++ tailWord_1891679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1891682 : List Nat := [3, 3, 2, 1, 1, 1, 3, 2, 5]
def baseStart_1891682 : Nat := 118140960795 + 1891682 * 2 ^ 59
def prefixEnd_1891682 : Nat := 4983230072969 + 3 ^ 40 * 1891682 * 2
def baseEnd_1891682 : Nat := 431707605092699119633475

theorem tailTrace_1891682 : CollatzResearch.WordTrace tailWord_1891682 prefixEnd_1891682 431707605092699119633475 := by
  unfold tailWord_1891682
  simp only [CollatzResearch.WordTrace]
  refine ⟨17248827683191665602377325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45996873821844441606339533 17248827683191665602377325)
  ·
    refine ⟨6468310381196874600891497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17248827683191665602377325 6468310381196874600891497)
    ·
      refine ⟨4851232785897655950668623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6468310381196874600891497 4851232785897655950668623)
      ·
        refine ⟨7276849178846483926002935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4851232785897655950668623 7276849178846483926002935)
        ·
          refine ⟨10915273768269725889004403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7276849178846483926002935 10915273768269725889004403)
          ·
            refine ⟨16372910652404588833506605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10915273768269725889004403 16372910652404588833506605)
            ·
              refine ⟨6139841494651720812564977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16372910652404588833506605 6139841494651720812564977)
              ·
                refine ⟨4604881120988790609423733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6139841494651720812564977 4604881120988790609423733)
                ·
                  refine ⟨431707605092699119633475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4604881120988790609423733 431707605092699119633475)
                  ·
                    rfl

theorem cell21_1891682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 2, 5].length) (baseStart_1891682 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1891682 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1891682 prefixEnd_1891682 := by exact prefixLift 1891682
  have htrace : WordTrace (prefixWord ++ tailWord_1891682) baseStart_1891682 baseEnd_1891682 := by
    simpa [prefixWord, tailWord_1891682, baseEnd_1891682] using wordTrace_append hprefix tailTrace_1891682
  have hstable : (prefixWord ++ tailWord_1891682).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1891682).length < 2 ^ (prefixWord ++ tailWord_1891682).sum := by decide
  have hdescent : baseEnd_1891682 < baseStart_1891682 := by decide
  rcases family_descends (prefixWord ++ tailWord_1891682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1891713 : List Nat := [1, 2, 4, 3, 2, 1, 1, 1, 6]
def baseStart_1891713 : Nat := 118140960795 + 1891713 * 2 ^ 59
def prefixEnd_1891713 : Nat := 4983230072969 + 3 ^ 40 * 1891713 * 2
def baseEnd_1891713 : Nat := 431714679715049954616745

theorem tailTrace_1891713 : CollatzResearch.WordTrace tailWord_1891713 prefixEnd_1891713 431714679715049954616745 := by
  unfold tailWord_1891713
  simp only [CollatzResearch.WordTrace]
  refine ⟨68996441395654354703887793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45997627597102903135925195 68996441395654354703887793)
  ·
    refine ⟨51747331046740766027915845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68996441395654354703887793 51747331046740766027915845)
    ·
      refine ⟨9702624571263893630234221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51747331046740766027915845 9702624571263893630234221)
      ·
        refine ⟨3638484214223960111337833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9702624571263893630234221 3638484214223960111337833)
        ·
          refine ⟨2728863160667970083503375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3638484214223960111337833 2728863160667970083503375)
          ·
            refine ⟨4093294741001955125255063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2728863160667970083503375 4093294741001955125255063)
            ·
              refine ⟨6139942111502932687882595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4093294741001955125255063 6139942111502932687882595)
              ·
                refine ⟨9209913167254399031823893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6139942111502932687882595 9209913167254399031823893)
                ·
                  refine ⟨431714679715049954616745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9209913167254399031823893 431714679715049954616745)
                  ·
                    rfl

theorem cell21_1891713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 1, 6].length) (baseStart_1891713 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1891713 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1891713 prefixEnd_1891713 := by exact prefixLift 1891713
  have htrace : WordTrace (prefixWord ++ tailWord_1891713) baseStart_1891713 baseEnd_1891713 := by
    simpa [prefixWord, tailWord_1891713, baseEnd_1891713] using wordTrace_append hprefix tailTrace_1891713
  have hstable : (prefixWord ++ tailWord_1891713).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1891713).length < 2 ^ (prefixWord ++ tailWord_1891713).sum := by decide
  have hdescent : baseEnd_1891713 < baseStart_1891713 := by decide
  rcases family_descends (prefixWord ++ tailWord_1891713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1891786 : List Nat := [3, 1, 2, 1, 2, 3, 1, 8]
def baseStart_1891786 : Nat := 118140960795 + 1891786 * 2 ^ 59
def prefixEnd_1891786 : Nat := 4983230072969 + 3 ^ 40 * 1891786 * 2
def baseEnd_1891786 : Nat := 143910446436539349966643

theorem tailTrace_1891786 : CollatzResearch.WordTrace tailWord_1891786 prefixEnd_1891786 143910446436539349966643 := by
  unfold tailWord_1891786
  simp only [CollatzResearch.WordTrace]
  refine ⟨17249775981097472042823803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45999402616259925447530141 17249775981097472042823803)
  ·
    refine ⟨25874663971646208064235705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17249775981097472042823803 25874663971646208064235705)
    ·
      refine ⟨19405997978734656048176779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25874663971646208064235705 19405997978734656048176779)
      ·
        refine ⟨29108996968101984072265169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19405997978734656048176779 29108996968101984072265169)
        ·
          refine ⟨21831747726076488054198877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29108996968101984072265169 21831747726076488054198877)
          ·
            refine ⟨8186905397278683020324579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21831747726076488054198877 8186905397278683020324579)
            ·
              refine ⟨12280358095918024530486869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8186905397278683020324579 12280358095918024530486869)
              ·
                refine ⟨143910446436539349966643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12280358095918024530486869 143910446436539349966643)
                ·
                  rfl

theorem cell21_1891786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 8].length) (baseStart_1891786 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1891786 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1891786 prefixEnd_1891786 := by exact prefixLift 1891786
  have htrace : WordTrace (prefixWord ++ tailWord_1891786) baseStart_1891786 baseEnd_1891786 := by
    simpa [prefixWord, tailWord_1891786, baseEnd_1891786] using wordTrace_append hprefix tailTrace_1891786
  have hstable : (prefixWord ++ tailWord_1891786).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1891786).length < 2 ^ (prefixWord ++ tailWord_1891786).sum := by decide
  have hdescent : baseEnd_1891786 < baseStart_1891786 := by decide
  rcases family_descends (prefixWord ++ tailWord_1891786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1891834 : List Nat := [3, 1, 1, 1, 1, 2, 5, 4, 3]
def baseStart_1891834 : Nat := 118140960795 + 1891834 * 2 ^ 59
def prefixEnd_1891834 : Nat := 4983230072969 + 3 ^ 40 * 1891834 * 2
def baseEnd_1891834 : Nat := 431742293563580633099831

theorem tailTrace_1891834 : CollatzResearch.WordTrace tailWord_1891834 prefixEnd_1891834 431742293563580633099831 := by
  unfold tailWord_1891834
  simp only [CollatzResearch.WordTrace]
  refine ⟨17250213657053998092260639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46000569752143994912695037 17250213657053998092260639)
  ·
    refine ⟨25875320485580997138390959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17250213657053998092260639 25875320485580997138390959)
    ·
      refine ⟨38812980728371495707586439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25875320485580997138390959 38812980728371495707586439)
      ·
        refine ⟨58219471092557243561379659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38812980728371495707586439 58219471092557243561379659)
        ·
          refine ⟨87329206638835865342069489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58219471092557243561379659 87329206638835865342069489)
          ·
            refine ⟨65496904979126899006552117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87329206638835865342069489 65496904979126899006552117)
            ·
              refine ⟨6140334841793146781864261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65496904979126899006552117 6140334841793146781864261)
              ·
                refine ⟨1151312782836215021599549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6140334841793146781864261 1151312782836215021599549)
                ·
                  refine ⟨431742293563580633099831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1151312782836215021599549 431742293563580633099831)
                  ·
                    rfl

theorem cell21_1891834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 4, 3].length) (baseStart_1891834 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1891834 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1891834 prefixEnd_1891834 := by exact prefixLift 1891834
  have htrace : WordTrace (prefixWord ++ tailWord_1891834) baseStart_1891834 baseEnd_1891834 := by
    simpa [prefixWord, tailWord_1891834, baseEnd_1891834] using wordTrace_append hprefix tailTrace_1891834
  have hstable : (prefixWord ++ tailWord_1891834).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1891834).length < 2 ^ (prefixWord ++ tailWord_1891834).sum := by decide
  have hdescent : baseEnd_1891834 < baseStart_1891834 := by decide
  rcases family_descends (prefixWord ++ tailWord_1891834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1891848 : List Nat := [2, 1, 3, 2, 1, 1, 4, 3, 4]
def baseStart_1891848 : Nat := 118140960795 + 1891848 * 2 ^ 59
def prefixEnd_1891848 : Nat := 4983230072969 + 3 ^ 40 * 1891848 * 2
def baseEnd_1891848 : Nat := 431745488554319719866469

theorem tailTrace_1891848 : CollatzResearch.WordTrace tailWord_1891848 prefixEnd_1891848 431745488554319719866469 := by
  unfold tailWord_1891848
  simp only [CollatzResearch.WordTrace]
  refine ⟨34500682625082636380026099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46000910166776848506701465 34500682625082636380026099)
  ·
    refine ⟨51751023937623954570039149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34500682625082636380026099 51751023937623954570039149)
    ·
      refine ⟨19406633976608982963764681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51751023937623954570039149 19406633976608982963764681)
      ·
        refine ⟨14554975482456737222823511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19406633976608982963764681 14554975482456737222823511)
        ·
          refine ⟨21832463223685105834235267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14554975482456737222823511 21832463223685105834235267)
          ·
            refine ⟨32748694835527658751352901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21832463223685105834235267 32748694835527658751352901)
            ·
              refine ⟨6140380281661436015878669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32748694835527658751352901 6140380281661436015878669)
              ·
                refine ⟨2302642605623038505954501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6140380281661436015878669 2302642605623038505954501)
                ·
                  refine ⟨431745488554319719866469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2302642605623038505954501 431745488554319719866469)
                  ·
                    rfl

theorem cell21_1891848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 3, 4].length) (baseStart_1891848 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1891848 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1891848 prefixEnd_1891848 := by exact prefixLift 1891848
  have htrace : WordTrace (prefixWord ++ tailWord_1891848) baseStart_1891848 baseEnd_1891848 := by
    simpa [prefixWord, tailWord_1891848, baseEnd_1891848] using wordTrace_append hprefix tailTrace_1891848
  have hstable : (prefixWord ++ tailWord_1891848).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1891848).length < 2 ^ (prefixWord ++ tailWord_1891848).sum := by decide
  have hdescent : baseEnd_1891848 < baseStart_1891848 := by decide
  rcases family_descends (prefixWord ++ tailWord_1891848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1891893 : List Nat := [1, 3, 3, 1, 1, 3, 1, 3, 5]
def baseStart_1891893 : Nat := 118140960795 + 1891893 * 2 ^ 59
def prefixEnd_1891893 : Nat := 4983230072969 + 3 ^ 40 * 1891893 * 2
def baseEnd_1891893 : Nat := 431755758167409641616377

theorem tailTrace_1891893 : CollatzResearch.WordTrace tailWord_1891893 prefixEnd_1891893 431755758167409641616377 := by
  unfold tailWord_1891893
  simp only [CollatzResearch.WordTrace]
  refine ⟨69003006535002245445440333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46002004356668163630293555 69003006535002245445440333)
  ·
    refine ⟨25876127450625842042040125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69003006535002245445440333 25876127450625842042040125)
    ·
      refine ⟨9703547793984690765765047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25876127450625842042040125 9703547793984690765765047)
      ·
        refine ⟨14555321690977036148647571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9703547793984690765765047 14555321690977036148647571)
        ·
          refine ⟨21832982536465554222971357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14555321690977036148647571 21832982536465554222971357)
          ·
            refine ⟨8187368451174582833614259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21832982536465554222971357 8187368451174582833614259)
            ·
              refine ⟨12281052676761874250421389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8187368451174582833614259 12281052676761874250421389)
              ·
                refine ⟨4605394753785702843908021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12281052676761874250421389 4605394753785702843908021)
                ·
                  refine ⟨431755758167409641616377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4605394753785702843908021 431755758167409641616377)
                  ·
                    rfl

theorem cell21_1891893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 3, 5].length) (baseStart_1891893 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1891893 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1891893 prefixEnd_1891893 := by exact prefixLift 1891893
  have htrace : WordTrace (prefixWord ++ tailWord_1891893) baseStart_1891893 baseEnd_1891893 := by
    simpa [prefixWord, tailWord_1891893, baseEnd_1891893] using wordTrace_append hprefix tailTrace_1891893
  have hstable : (prefixWord ++ tailWord_1891893).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1891893).length < 2 ^ (prefixWord ++ tailWord_1891893).sum := by decide
  have hdescent : baseEnd_1891893 < baseStart_1891893 := by decide
  rcases family_descends (prefixWord ++ tailWord_1891893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1891927 : List Nat := [1, 1, 3, 2, 2, 5, 1, 3, 3]
def baseStart_1891927 : Nat := 118140960795 + 1891927 * 2 ^ 59
def prefixEnd_1891927 : Nat := 4983230072969 + 3 ^ 40 * 1891927 * 2
def baseEnd_1891927 : Nat := 431763517430633138049641

theorem tailTrace_1891927 : CollatzResearch.WordTrace tailWord_1891927 prefixEnd_1891927 431763517430633138049641 := by
  unfold tailWord_1891927
  simp only [CollatzResearch.WordTrace]
  refine ⟨69004246616879069252178035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46002831077919379501452023 69004246616879069252178035)
  ·
    refine ⟨103506369925318603878267053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69004246616879069252178035 103506369925318603878267053)
    ·
      refine ⟨38814888721994476454350145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103506369925318603878267053 38814888721994476454350145)
      ·
        refine ⟨29111166541495857340762609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38814888721994476454350145 29111166541495857340762609)
        ·
          refine ⟨21833374906121893005571957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29111166541495857340762609 21833374906121893005571957)
          ·
            refine ⟨2046878897448927469272371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21833374906121893005571957 2046878897448927469272371)
            ·
              refine ⟨3070318346173391203908557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2046878897448927469272371 3070318346173391203908557)
              ·
                refine ⟨1151369379815021701465709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3070318346173391203908557 1151369379815021701465709)
                ·
                  refine ⟨431763517430633138049641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1151369379815021701465709 431763517430633138049641)
                  ·
                    rfl

theorem cell21_1891927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 1, 3, 3].length) (baseStart_1891927 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1891927 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1891927 prefixEnd_1891927 := by exact prefixLift 1891927
  have htrace : WordTrace (prefixWord ++ tailWord_1891927) baseStart_1891927 baseEnd_1891927 := by
    simpa [prefixWord, tailWord_1891927, baseEnd_1891927] using wordTrace_append hprefix tailTrace_1891927
  have hstable : (prefixWord ++ tailWord_1891927).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1891927).length < 2 ^ (prefixWord ++ tailWord_1891927).sum := by decide
  have hdescent : baseEnd_1891927 < baseStart_1891927 := by decide
  rcases family_descends (prefixWord ++ tailWord_1891927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1891944 : List Nat := [2, 1, 4, 3, 1, 2, 3, 2, 3]
def baseStart_1891944 : Nat := 118140960795 + 1891944 * 2 ^ 59
def prefixEnd_1891944 : Nat := 4983230072969 + 3 ^ 40 * 1891944 * 2
def baseEnd_1891944 : Nat := 431767397062244886266273

theorem tailTrace_1891944 : CollatzResearch.WordTrace tailWord_1891944 prefixEnd_1891944 431767397062244886266273 := by
  unfold tailWord_1891944
  simp only [CollatzResearch.WordTrace]
  refine ⟨34502433328908740577773443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46003244438544987437031257 34502433328908740577773443)
  ·
    refine ⟨51753649993363110866660165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34502433328908740577773443 51753649993363110866660165)
    ·
      refine ⟨9703809373755583287498781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51753649993363110866660165 9703809373755583287498781)
      ·
        refine ⟨3638928515158343732812043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9703809373755583287498781 3638928515158343732812043)
        ·
          refine ⟨5458392772737515599218065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3638928515158343732812043 5458392772737515599218065)
          ·
            refine ⟨4093794579553136699413549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5458392772737515599218065 4093794579553136699413549)
            ·
              refine ⟨1535172967332426262280081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4093794579553136699413549 1535172967332426262280081)
              ·
                refine ⟨1151379725499319696710061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1535172967332426262280081 1151379725499319696710061)
                ·
                  refine ⟨431767397062244886266273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1151379725499319696710061 431767397062244886266273)
                  ·
                    rfl

theorem cell21_1891944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 3, 2, 3].length) (baseStart_1891944 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1891944 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1891944 prefixEnd_1891944 := by exact prefixLift 1891944
  have htrace : WordTrace (prefixWord ++ tailWord_1891944) baseStart_1891944 baseEnd_1891944 := by
    simpa [prefixWord, tailWord_1891944, baseEnd_1891944] using wordTrace_append hprefix tailTrace_1891944
  have hstable : (prefixWord ++ tailWord_1891944).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1891944).length < 2 ^ (prefixWord ++ tailWord_1891944).sum := by decide
  have hdescent : baseEnd_1891944 < baseStart_1891944 := by decide
  rcases family_descends (prefixWord ++ tailWord_1891944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1891958 : List Nat := [5, 1, 1, 2, 2, 1, 4, 1, 4]
def baseStart_1891958 : Nat := 118140960795 + 1891958 * 2 ^ 59
def prefixEnd_1891958 : Nat := 4983230072969 + 3 ^ 40 * 1891958 * 2
def baseEnd_1891958 : Nat := 431770592052983973032911

theorem tailTrace_1891958 : CollatzResearch.WordTrace tailWord_1891958 prefixEnd_1891958 431770592052983973032911 := by
  unfold tailWord_1891958
  simp only [CollatzResearch.WordTrace]
  refine ⟨4312836079985422596659783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46003584853177841031037685 4312836079985422596659783)
  ·
    refine ⟨6469254119978133894989675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4312836079985422596659783 6469254119978133894989675)
    ·
      refine ⟨9703881179967200842484513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6469254119978133894989675 9703881179967200842484513)
      ·
        refine ⟨7277910884975400631863385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9703881179967200842484513 7277910884975400631863385)
        ·
          refine ⟨5458433163731550473897539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7277910884975400631863385 5458433163731550473897539)
          ·
            refine ⟨8187649745597325710846309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5458433163731550473897539 8187649745597325710846309)
            ·
              refine ⟨1535184327299498570783683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8187649745597325710846309 1535184327299498570783683)
              ·
                refine ⟨2302776490949247856175525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1535184327299498570783683 2302776490949247856175525)
                ·
                  refine ⟨431770592052983973032911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2302776490949247856175525 431770592052983973032911)
                  ·
                    rfl

theorem cell21_1891958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 4, 1, 4].length) (baseStart_1891958 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1891958 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1891958 prefixEnd_1891958 := by exact prefixLift 1891958
  have htrace : WordTrace (prefixWord ++ tailWord_1891958) baseStart_1891958 baseEnd_1891958 := by
    simpa [prefixWord, tailWord_1891958, baseEnd_1891958] using wordTrace_append hprefix tailTrace_1891958
  have hstable : (prefixWord ++ tailWord_1891958).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1891958).length < 2 ^ (prefixWord ++ tailWord_1891958).sum := by decide
  have hdescent : baseEnd_1891958 < baseStart_1891958 := by decide
  rcases family_descends (prefixWord ++ tailWord_1891958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1892000 : List Nat := [2, 1, 1, 4, 3, 1, 1, 4, 4]
def baseStart_1892000 : Nat := 118140960795 + 1892000 * 2 ^ 59
def prefixEnd_1892000 : Nat := 4983230072969 + 3 ^ 40 * 1892000 * 2
def baseEnd_1892000 : Nat := 431780177025201233332825

theorem tailTrace_1892000 : CollatzResearch.WordTrace tailWord_1892000 prefixEnd_1892000 431780177025201233332825 := by
  unfold tailWord_1892000
  simp only [CollatzResearch.WordTrace]
  refine ⟨34503454572807301359792727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46004606097076401813056969 34503454572807301359792727)
  ·
    refine ⟨51755181859210952039689091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34503454572807301359792727 51755181859210952039689091)
    ·
      refine ⟨77632772788816428059533637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51755181859210952039689091 77632772788816428059533637)
      ·
        refine ⟨14556144897903080261162557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77632772788816428059533637 14556144897903080261162557)
        ·
          refine ⟨5458554336713655097935959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14556144897903080261162557 5458554336713655097935959)
          ·
            refine ⟨8187831505070482646903939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5458554336713655097935959 8187831505070482646903939)
            ·
              refine ⟨12281747257605723970355909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8187831505070482646903939 12281747257605723970355909)
              ·
                refine ⟨2302827610801073244441733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12281747257605723970355909 2302827610801073244441733)
                ·
                  refine ⟨431780177025201233332825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2302827610801073244441733 431780177025201233332825)
                  ·
                    rfl

theorem cell21_1892000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 4, 4].length) (baseStart_1892000 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1892000 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1892000 prefixEnd_1892000 := by exact prefixLift 1892000
  have htrace : WordTrace (prefixWord ++ tailWord_1892000) baseStart_1892000 baseEnd_1892000 := by
    simpa [prefixWord, tailWord_1892000, baseEnd_1892000] using wordTrace_append hprefix tailTrace_1892000
  have hstable : (prefixWord ++ tailWord_1892000).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1892000).length < 2 ^ (prefixWord ++ tailWord_1892000).sum := by decide
  have hdescent : baseEnd_1892000 < baseStart_1892000 := by decide
  rcases family_descends (prefixWord ++ tailWord_1892000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1892073 : List Nat := [1, 2, 1, 1, 1, 2, 3, 10]
def baseStart_1892073 : Nat := 118140960795 + 1892073 * 2 ^ 59
def prefixEnd_1892073 : Nat := 4983230072969 + 3 ^ 40 * 1892073 * 2
def baseEnd_1892073 : Nat := 143932278873256442872003

theorem tailTrace_1892073 : CollatzResearch.WordTrace tailWord_1892073 prefixEnd_1892073 143932278873256442872003 := by
  unfold tailWord_1892073
  simp only [CollatzResearch.WordTrace]
  refine ⟨69009571674350136186992873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46006381116233424124661915 69009571674350136186992873)
  ·
    refine ⟨51757178755762602140244655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69009571674350136186992873 51757178755762602140244655)
    ·
      refine ⟨77635768133643903210366983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51757178755762602140244655 77635768133643903210366983)
      ·
        refine ⟨116453652200465854815550475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77635768133643903210366983 116453652200465854815550475)
        ·
          refine ⟨174680478300698782223325713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116453652200465854815550475 174680478300698782223325713)
          ·
            refine ⟨131010358725524086667494285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174680478300698782223325713 131010358725524086667494285)
            ·
              refine ⟨49128884522071532500310357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131010358725524086667494285 49128884522071532500310357)
              ·
                refine ⟨143932278873256442872003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 49128884522071532500310357 143932278873256442872003)
                ·
                  rfl

theorem cell21_1892073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 10].length) (baseStart_1892073 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1892073 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1892073 prefixEnd_1892073 := by exact prefixLift 1892073
  have htrace : WordTrace (prefixWord ++ tailWord_1892073) baseStart_1892073 baseEnd_1892073 := by
    simpa [prefixWord, tailWord_1892073, baseEnd_1892073] using wordTrace_append hprefix tailTrace_1892073
  have hstable : (prefixWord ++ tailWord_1892073).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1892073).length < 2 ^ (prefixWord ++ tailWord_1892073).sum := by decide
  have hdescent : baseEnd_1892073 < baseStart_1892073 := by decide
  rcases family_descends (prefixWord ++ tailWord_1892073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1892172 : List Nat := [2, 2, 1, 3, 4, 2, 2, 2, 3]
def baseStart_1892172 : Nat := 118140960795 + 1892172 * 2 ^ 59
def prefixEnd_1892172 : Nat := 4983230072969 + 3 ^ 40 * 1892172 * 2
def baseEnd_1892172 : Nat := 431819429768567156465807

theorem tailTrace_1892172 : CollatzResearch.WordTrace tailWord_1892172 prefixEnd_1892172 431819429768567156465807 := by
  unfold tailWord_1892172
  simp only [CollatzResearch.WordTrace]
  refine ⟨34506591250495738047423385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46008788333994317396564513 34506591250495738047423385)
  ·
    refine ⟨25879943437871803535567539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34506591250495738047423385 25879943437871803535567539)
    ·
      refine ⟨38819915156807705303351309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25879943437871803535567539 38819915156807705303351309)
      ·
        refine ⟨14557468183802889488756741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38819915156807705303351309 14557468183802889488756741)
        ·
          refine ⟨2729525284463041779141889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14557468183802889488756741 2729525284463041779141889)
          ·
            refine ⟨2047143963347281334356417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2729525284463041779141889 2047143963347281334356417)
            ·
              refine ⟨1535357972510461000767313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2047143963347281334356417 1535357972510461000767313)
              ·
                refine ⟨1151518479382845750575485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1535357972510461000767313 1151518479382845750575485)
                ·
                  refine ⟨431819429768567156465807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1151518479382845750575485 431819429768567156465807)
                  ·
                    rfl

theorem cell21_1892172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 2, 2, 3].length) (baseStart_1892172 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1892172 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1892172 prefixEnd_1892172 := by exact prefixLift 1892172
  have htrace : WordTrace (prefixWord ++ tailWord_1892172) baseStart_1892172 baseEnd_1892172 := by
    simpa [prefixWord, tailWord_1892172, baseEnd_1892172] using wordTrace_append hprefix tailTrace_1892172
  have hstable : (prefixWord ++ tailWord_1892172).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1892172).length < 2 ^ (prefixWord ++ tailWord_1892172).sum := by decide
  have hdescent : baseEnd_1892172 < baseStart_1892172 := by decide
  rcases family_descends (prefixWord ++ tailWord_1892172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1892183 : List Nat := [1, 1, 3, 2, 5, 2, 1, 6]
def baseStart_1892183 : Nat := 118140960795 + 1892183 * 2 ^ 59
def prefixEnd_1892183 : Nat := 4983230072969 + 3 ^ 40 * 1892183 * 2
def baseEnd_1892183 : Nat := 143940646706144527260817

theorem tailTrace_1892183 : CollatzResearch.WordTrace tailWord_1892183 prefixEnd_1892183 143940646706144527260817 := by
  unfold tailWord_1892183
  simp only [CollatzResearch.WordTrace]
  refine ⟨69013583703951624973497203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46009055802634416648998135 69013583703951624973497203)
  ·
    refine ⟨103520375555927437460245805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69013583703951624973497203 103520375555927437460245805)
    ·
      refine ⟨38820140833472789047592177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103520375555927437460245805 38820140833472789047592177)
      ·
        refine ⟨29115105625104591785694133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38820140833472789047592177 29115105625104591785694133)
        ·
          refine ⟨2729541152353555479908825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29115105625104591785694133 2729541152353555479908825)
          ·
            refine ⟨2047155864265166609931619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2729541152353555479908825 2047155864265166609931619)
            ·
              refine ⟨3070733796397749914897429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2047155864265166609931619 3070733796397749914897429)
              ·
                refine ⟨143940646706144527260817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3070733796397749914897429 143940646706144527260817)
                ·
                  rfl

theorem cell21_1892183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 1, 6].length) (baseStart_1892183 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1892183 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1892183 prefixEnd_1892183 := by exact prefixLift 1892183
  have htrace : WordTrace (prefixWord ++ tailWord_1892183) baseStart_1892183 baseEnd_1892183 := by
    simpa [prefixWord, tailWord_1892183, baseEnd_1892183] using wordTrace_append hprefix tailTrace_1892183
  have hstable : (prefixWord ++ tailWord_1892183).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1892183).length < 2 ^ (prefixWord ++ tailWord_1892183).sum := by decide
  have hdescent : baseEnd_1892183 < baseStart_1892183 := by decide
  rcases family_descends (prefixWord ++ tailWord_1892183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1892228 : List Nat := [2, 3, 2, 1, 1, 1, 5, 2, 4]
def baseStart_1892228 : Nat := 118140960795 + 1892228 * 2 ^ 59
def prefixEnd_1892228 : Nat := 4983230072969 + 3 ^ 40 * 1892228 * 2
def baseEnd_1892228 : Nat := 431832209731523503532359

theorem tailTrace_1892228 : CollatzResearch.WordTrace tailWord_1892228 prefixEnd_1892228 431832209731523503532359 := by
  unfold tailWord_1892228
  simp only [CollatzResearch.WordTrace]
  refine ⟨34507612494394298829442669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46010149992525731772590225 34507612494394298829442669)
  ·
    refine ⟨12940354685397862061041001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34507612494394298829442669 12940354685397862061041001)
    ·
      refine ⟨9705266014048396545780751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12940354685397862061041001 9705266014048396545780751)
      ·
        refine ⟨14557899021072594818671127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9705266014048396545780751 14557899021072594818671127)
        ·
          refine ⟨21836848531608892228006691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14557899021072594818671127 21836848531608892228006691)
          ·
            refine ⟨32755272797413338342010037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21836848531608892228006691 32755272797413338342010037)
            ·
              refine ⟨3070806824757500469563441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32755272797413338342010037 3070806824757500469563441)
              ·
                refine ⟨2303105118568125352172581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3070806824757500469563441 2303105118568125352172581)
                ·
                  refine ⟨431832209731523503532359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2303105118568125352172581 431832209731523503532359)
                  ·
                    rfl

theorem cell21_1892228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 5, 2, 4].length) (baseStart_1892228 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1892228 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1892228 prefixEnd_1892228 := by exact prefixLift 1892228
  have htrace : WordTrace (prefixWord ++ tailWord_1892228) baseStart_1892228 baseEnd_1892228 := by
    simpa [prefixWord, tailWord_1892228, baseEnd_1892228] using wordTrace_append hprefix tailTrace_1892228
  have hstable : (prefixWord ++ tailWord_1892228).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1892228).length < 2 ^ (prefixWord ++ tailWord_1892228).sum := by decide
  have hdescent : baseEnd_1892228 < baseStart_1892228 := by decide
  rcases family_descends (prefixWord ++ tailWord_1892228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1892276 : List Nat := [2, 5, 2, 1, 2, 2, 7]
def baseStart_1892276 : Nat := 118140960795 + 1892276 * 2 ^ 59
def prefixEnd_1892276 : Nat := 4983230072969 + 3 ^ 40 * 1892276 * 2
def baseEnd_1892276 : Nat := 47982573776165120748029

theorem tailTrace_1892276 : CollatzResearch.WordTrace tailWord_1892276 prefixEnd_1892276 47982573776165120748029 := by
  unfold tailWord_1892276
  simp only [CollatzResearch.WordTrace]
  refine ⟨34508487846307350928316341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46011317128409801237755121 34508487846307350928316341)
  ·
    refine ⟨3235170735591314149529657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34508487846307350928316341 3235170735591314149529657)
    ·
      refine ⟨2426378051693485612147243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3235170735591314149529657 2426378051693485612147243)
      ·
        refine ⟨3639567077540228418220865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2426378051693485612147243 3639567077540228418220865)
        ·
          refine ⟨2729675308155171313665649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3639567077540228418220865 2729675308155171313665649)
          ·
            refine ⟨2047256481116378485249237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2729675308155171313665649 2047256481116378485249237)
            ·
              refine ⟨47982573776165120748029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2047256481116378485249237 47982573776165120748029)
              ·
                rfl

theorem cell21_1892276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 7].length) (baseStart_1892276 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1892276 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1892276 prefixEnd_1892276 := by exact prefixLift 1892276
  have htrace : WordTrace (prefixWord ++ tailWord_1892276) baseStart_1892276 baseEnd_1892276 := by
    simpa [prefixWord, tailWord_1892276, baseEnd_1892276] using wordTrace_append hprefix tailTrace_1892276
  have hstable : (prefixWord ++ tailWord_1892276).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1892276).length < 2 ^ (prefixWord ++ tailWord_1892276).sum := by decide
  have hdescent : baseEnd_1892276 < baseStart_1892276 := by decide
  rcases family_descends (prefixWord ++ tailWord_1892276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1892287 : List Nat := [1, 1, 2, 2, 2, 1, 4, 4, 4]
def baseStart_1892287 : Nat := 118140960795 + 1892287 * 2 ^ 59
def prefixEnd_1892287 : Nat := 4983230072969 + 3 ^ 40 * 1892287 * 2
def baseEnd_1892287 : Nat := 431845674335352512048905

theorem tailTrace_1892287 : CollatzResearch.WordTrace tailWord_1892287 prefixEnd_1892287 431845674335352512048905 := by
  unfold tailWord_1892287
  simp only [CollatzResearch.WordTrace]
  refine ⟨69017376895574850735283115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46011584597049900490188743 69017376895574850735283115)
  ·
    refine ⟨103526065343362276102924673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69017376895574850735283115 103526065343362276102924673)
    ·
      refine ⟨77644549007521707077193505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103526065343362276102924673 77644549007521707077193505)
      ·
        refine ⟨58233411755641280307895129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77644549007521707077193505 58233411755641280307895129)
        ·
          refine ⟨43675058816730960230921347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58233411755641280307895129 43675058816730960230921347)
          ·
            refine ⟨65512588225096440346382021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43675058816730960230921347 65512588225096440346382021)
            ·
              refine ⟨12283610292205582564946629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65512588225096440346382021 12283610292205582564946629)
              ·
                refine ⟨2303176929788546730927493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12283610292205582564946629 2303176929788546730927493)
                ·
                  refine ⟨431845674335352512048905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2303176929788546730927493 431845674335352512048905)
                  ·
                    rfl

theorem cell21_1892287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 4, 4].length) (baseStart_1892287 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1892287 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1892287 prefixEnd_1892287 := by exact prefixLift 1892287
  have htrace : WordTrace (prefixWord ++ tailWord_1892287) baseStart_1892287 baseEnd_1892287 := by
    simpa [prefixWord, tailWord_1892287, baseEnd_1892287] using wordTrace_append hprefix tailTrace_1892287
  have hstable : (prefixWord ++ tailWord_1892287).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1892287).length < 2 ^ (prefixWord ++ tailWord_1892287).sum := by decide
  have hdescent : baseEnd_1892287 < baseStart_1892287 := by decide
  rcases family_descends (prefixWord ++ tailWord_1892287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1892304 : List Nat := [2, 1, 1, 1, 1, 2, 8, 1, 4]
def baseStart_1892304 : Nat := 118140960795 + 1892304 * 2 ^ 59
def prefixEnd_1892304 : Nat := 4983230072969 + 3 ^ 40 * 1892304 * 2
def baseEnd_1892304 : Nat := 431849553966964260265537

theorem tailTrace_1892304 : CollatzResearch.WordTrace tailWord_1892304 prefixEnd_1892304 431849553966964260265537 := by
  unfold tailWord_1892304
  simp only [CollatzResearch.WordTrace]
  refine ⟨34508998468256631319325983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46011997957675508425767977 34508998468256631319325983)
  ·
    refine ⟨51763497702384946978988975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34508998468256631319325983 51763497702384946978988975)
    ·
      refine ⟨77645246553577420468483463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51763497702384946978988975 77645246553577420468483463)
      ·
        refine ⟨116467869830366130702725195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77645246553577420468483463 116467869830366130702725195)
        ·
          refine ⟨174701804745549196054087793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116467869830366130702725195 174701804745549196054087793)
          ·
            refine ⟨131026353559161897040565845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174701804745549196054087793 131026353559161897040565845)
            ·
              refine ⟨1535465080771428480944131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 131026353559161897040565845 1535465080771428480944131)
              ·
                refine ⟨2303197621157142721416197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1535465080771428480944131 2303197621157142721416197)
                ·
                  refine ⟨431849553966964260265537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2303197621157142721416197 431849553966964260265537)
                  ·
                    rfl

theorem cell21_1892304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 8, 1, 4].length) (baseStart_1892304 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1892304 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1892304 prefixEnd_1892304 := by exact prefixLift 1892304
  have htrace : WordTrace (prefixWord ++ tailWord_1892304) baseStart_1892304 baseEnd_1892304 := by
    simpa [prefixWord, tailWord_1892304, baseEnd_1892304] using wordTrace_append hprefix tailTrace_1892304
  have hstable : (prefixWord ++ tailWord_1892304).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1892304).length < 2 ^ (prefixWord ++ tailWord_1892304).sum := by decide
  have hdescent : baseEnd_1892304 < baseStart_1892304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1892304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1892363 : List Nat := [1, 1, 1, 1, 6, 1, 1, 5, 4]
def baseStart_1892363 : Nat := 118140960795 + 1892363 * 2 ^ 59
def prefixEnd_1892363 : Nat := 4983230072969 + 3 ^ 40 * 1892363 * 2
def baseEnd_1892363 : Nat := 431863018570793268782083

theorem tailTrace_1892363 : CollatzResearch.WordTrace tailWord_1892363 prefixEnd_1892363 431863018570793268782083 := by
  unfold tailWord_1892363
  simp only [CollatzResearch.WordTrace]
  refine ⟨69020148843299515715049743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46013432562199677143366495 69020148843299515715049743)
  ·
    refine ⟨103530223264949273572574615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69020148843299515715049743 103530223264949273572574615)
    ·
      refine ⟨155295334897423910358861923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103530223264949273572574615 155295334897423910358861923)
      ·
        refine ⟨232943002346135865538292885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155295334897423910358861923 232943002346135865538292885)
        ·
          refine ⟨10919203234975118697107479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 232943002346135865538292885 10919203234975118697107479)
          ·
            refine ⟨16378804852462678045661219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10919203234975118697107479 16378804852462678045661219)
            ·
              refine ⟨24568207278694017068491829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16378804852462678045661219 24568207278694017068491829)
              ·
                refine ⟨2303269432377564100171109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24568207278694017068491829 2303269432377564100171109)
                ·
                  refine ⟨431863018570793268782083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2303269432377564100171109 431863018570793268782083)
                  ·
                    rfl

theorem cell21_1892363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 5, 4].length) (baseStart_1892363 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1892363 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1892363 prefixEnd_1892363 := by exact prefixLift 1892363
  have htrace : WordTrace (prefixWord ++ tailWord_1892363) baseStart_1892363 baseEnd_1892363 := by
    simpa [prefixWord, tailWord_1892363, baseEnd_1892363] using wordTrace_append hprefix tailTrace_1892363
  have hstable : (prefixWord ++ tailWord_1892363).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1892363).length < 2 ^ (prefixWord ++ tailWord_1892363).sum := by decide
  have hdescent : baseEnd_1892363 < baseStart_1892363 := by decide
  rcases family_descends (prefixWord ++ tailWord_1892363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1892394 : List Nat := [3, 1, 4, 1, 2, 2, 8]
def baseStart_1892394 : Nat := 118140960795 + 1892394 * 2 ^ 59
def prefixEnd_1892394 : Nat := 4983230072969 + 3 ^ 40 * 1892394 * 2
def baseEnd_1892394 : Nat := 47985565910349344862817

theorem tailTrace_1892394 : CollatzResearch.WordTrace tailWord_1892394 prefixEnd_1892394 47985565910349344862817 := by
  unfold tailWord_1892394
  simp only [CollatzResearch.WordTrace]
  refine ⟨17255319876546802002357059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46014186337458138672952157 17255319876546802002357059)
  ·
    refine ⟨25882979814820203003535589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17255319876546802002357059 25882979814820203003535589)
    ·
      refine ⟨4853058715278788063162923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25882979814820203003535589 4853058715278788063162923)
      ·
        refine ⟨7279588072918182094744385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4853058715278788063162923 7279588072918182094744385)
        ·
          refine ⟨5459691054688636571058289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7279588072918182094744385 5459691054688636571058289)
          ·
            refine ⟨4094768291016477428293717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5459691054688636571058289 4094768291016477428293717)
            ·
              refine ⟨47985565910349344862817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4094768291016477428293717 47985565910349344862817)
              ·
                rfl

theorem cell21_1892394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 8].length) (baseStart_1892394 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1892394 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1892394 prefixEnd_1892394 := by exact prefixLift 1892394
  have htrace : WordTrace (prefixWord ++ tailWord_1892394) baseStart_1892394 baseEnd_1892394 := by
    simpa [prefixWord, tailWord_1892394, baseEnd_1892394] using wordTrace_append hprefix tailTrace_1892394
  have hstable : (prefixWord ++ tailWord_1892394).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1892394).length < 2 ^ (prefixWord ++ tailWord_1892394).sum := by decide
  have hdescent : baseEnd_1892394 < baseStart_1892394 := by decide
  rcases family_descends (prefixWord ++ tailWord_1892394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1892414 : List Nat := [4, 2, 1, 3, 2, 1, 3, 1, 4]
def baseStart_1892414 : Nat := 118140960795 + 1892414 * 2 ^ 59
def prefixEnd_1892414 : Nat := 4983230072969 + 3 ^ 40 * 1892414 * 2
def baseEnd_1892414 : Nat := 431874657465628513431979

theorem tailTrace_1892414 : CollatzResearch.WordTrace tailWord_1892414 prefixEnd_1892414 431874657465628513431979 := by
  unfold tailWord_1892414
  simp only [CollatzResearch.WordTrace]
  refine ⟨8627751120764343928144537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46014672644076500950104197 8627751120764343928144537)
  ·
    refine ⟨6470813340573257946108403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8627751120764343928144537 6470813340573257946108403)
    ·
      refine ⟨9706220010859886919162605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6470813340573257946108403 9706220010859886919162605)
      ·
        refine ⟨3639832504072457594685977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9706220010859886919162605 3639832504072457594685977)
        ·
          refine ⟨2729874378054343196014483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3639832504072457594685977 2729874378054343196014483)
          ·
            refine ⟨4094811567081514794021725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2729874378054343196014483 4094811567081514794021725)
            ·
              refine ⟨1535554337655568047758147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4094811567081514794021725 1535554337655568047758147)
              ·
                refine ⟨2303331506483352071637221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1535554337655568047758147 2303331506483352071637221)
                ·
                  refine ⟨431874657465628513431979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2303331506483352071637221 431874657465628513431979)
                  ·
                    rfl

theorem cell21_1892414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 3, 1, 4].length) (baseStart_1892414 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1892414 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1892414 prefixEnd_1892414 := by exact prefixLift 1892414
  have htrace : WordTrace (prefixWord ++ tailWord_1892414) baseStart_1892414 baseEnd_1892414 := by
    simpa [prefixWord, tailWord_1892414, baseEnd_1892414] using wordTrace_append hprefix tailTrace_1892414
  have hstable : (prefixWord ++ tailWord_1892414).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1892414).length < 2 ^ (prefixWord ++ tailWord_1892414).sum := by decide
  have hdescent : baseEnd_1892414 < baseStart_1892414 := by decide
  rcases family_descends (prefixWord ++ tailWord_1892414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1892453 : List Nat := [1, 3, 1, 3, 2, 2, 9]
def baseStart_1892453 : Nat := 118140960795 + 1892453 * 2 ^ 59
def prefixEnd_1892453 : Nat := 4983230072969 + 3 ^ 40 * 1892453 * 2
def baseEnd_1892453 : Nat := 47987061977441456920211

theorem tailTrace_1892453 : CollatzResearch.WordTrace tailWord_1892453 prefixEnd_1892453 47987061977441456920211 := by
  unfold tailWord_1892453
  simp only [CollatzResearch.WordTrace]
  refine ⟨69023431412973461085826013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46015620941982307390550675 69023431412973461085826013)
  ·
    refine ⟨25883786779865047907184755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69023431412973461085826013 25883786779865047907184755)
    ·
      refine ⟨38825680169797571860777133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25883786779865047907184755 38825680169797571860777133)
      ·
        refine ⟨14559630063674089447791425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38825680169797571860777133 14559630063674089447791425)
        ·
          refine ⟨10919722547755567085843569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14559630063674089447791425 10919722547755567085843569)
          ·
            refine ⟨8189791910816675314382677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10919722547755567085843569 8189791910816675314382677)
            ·
              refine ⟨47987061977441456920211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8189791910816675314382677 47987061977441456920211)
              ·
                rfl

theorem cell21_1892453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 9].length) (baseStart_1892453 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1892453 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1892453 prefixEnd_1892453 := by exact prefixLift 1892453
  have htrace : WordTrace (prefixWord ++ tailWord_1892453) baseStart_1892453 baseEnd_1892453 := by
    simpa [prefixWord, tailWord_1892453, baseEnd_1892453] using wordTrace_append hprefix tailTrace_1892453
  have hstable : (prefixWord ++ tailWord_1892453).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1892453).length < 2 ^ (prefixWord ++ tailWord_1892453).sum := by decide
  have hdescent : baseEnd_1892453 < baseStart_1892453 := by decide
  rcases family_descends (prefixWord ++ tailWord_1892453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1892470 : List Nat := [5, 1, 1, 2, 1, 2, 1, 8]
def baseStart_1892470 : Nat := 118140960795 + 1892470 * 2 ^ 59
def prefixEnd_1892470 : Nat := 4983230072969 + 3 ^ 40 * 1892470 * 2
def baseEnd_1892470 : Nat := 143962479142861620166177

theorem tailTrace_1892470 : CollatzResearch.WordTrace tailWord_1892470 prefixEnd_1892470 143962479142861620166177 := by
  unfold tailWord_1892470
  simp only [CollatzResearch.WordTrace]
  refine ⟨4314003215869492061824679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46016034302607915326129909 4314003215869492061824679)
  ·
    refine ⟨6471004823804238092737019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4314003215869492061824679 6471004823804238092737019)
    ·
      refine ⟨9706507235706357139105529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6471004823804238092737019 9706507235706357139105529)
      ·
        refine ⟨7279880426779767854329147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9706507235706357139105529 7279880426779767854329147)
        ·
          refine ⟨10919820640169651781493721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7279880426779767854329147 10919820640169651781493721)
          ·
            refine ⟨8189865480127238836120291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10919820640169651781493721 8189865480127238836120291)
            ·
              refine ⟨12284798220190858254180437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8189865480127238836120291 12284798220190858254180437)
              ·
                refine ⟨143962479142861620166177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12284798220190858254180437 143962479142861620166177)
                ·
                  rfl

theorem cell21_1892470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 8].length) (baseStart_1892470 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1892470 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1892470 prefixEnd_1892470 := by exact prefixLift 1892470
  have htrace : WordTrace (prefixWord ++ tailWord_1892470) baseStart_1892470 baseEnd_1892470 := by
    simpa [prefixWord, tailWord_1892470, baseEnd_1892470] using wordTrace_append hprefix tailTrace_1892470
  have hstable : (prefixWord ++ tailWord_1892470).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1892470).length < 2 ^ (prefixWord ++ tailWord_1892470).sum := by decide
  have hdescent : baseEnd_1892470 < baseStart_1892470 := by decide
  rcases family_descends (prefixWord ++ tailWord_1892470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1892473 : List Nat := [1, 2, 1, 3, 4, 3, 2, 1, 4]
def baseStart_1892473 : Nat := 118140960795 + 1892473 * 2 ^ 59
def prefixEnd_1892473 : Nat := 4983230072969 + 3 ^ 40 * 1892473 * 2
def baseEnd_1892473 : Nat := 431888122069457521948525

theorem tailTrace_1892473 : CollatzResearch.WordTrace tailWord_1892473 prefixEnd_1892473 431888122069457521948525 := by
  unfold tailWord_1892473
  simp only [CollatzResearch.WordTrace]
  refine ⟨69024160872901004501554073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46016107248600669667702715 69024160872901004501554073)
  ·
    refine ⟨51768120654675753376165555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69024160872901004501554073 51768120654675753376165555)
    ·
      refine ⟨77652180982013630064248333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51768120654675753376165555 77652180982013630064248333)
      ·
        refine ⟨29119567868255111274093125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77652180982013630064248333 29119567868255111274093125)
        ·
          refine ⟨5459918975297833363892461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29119567868255111274093125 5459918975297833363892461)
          ·
            refine ⟨2047469615736687511459673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5459918975297833363892461 2047469615736687511459673)
            ·
              refine ⟨1535602211802515633594755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2047469615736687511459673 1535602211802515633594755)
              ·
                refine ⟨2303403317703773450392133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1535602211802515633594755 2303403317703773450392133)
                ·
                  refine ⟨431888122069457521948525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2303403317703773450392133 431888122069457521948525)
                  ·
                    rfl

theorem cell21_1892473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 2, 1, 4].length) (baseStart_1892473 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1892473 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1892473 prefixEnd_1892473 := by exact prefixLift 1892473
  have htrace : WordTrace (prefixWord ++ tailWord_1892473) baseStart_1892473 baseEnd_1892473 := by
    simpa [prefixWord, tailWord_1892473, baseEnd_1892473] using wordTrace_append hprefix tailTrace_1892473
  have hstable : (prefixWord ++ tailWord_1892473).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1892473).length < 2 ^ (prefixWord ++ tailWord_1892473).sum := by decide
  have hdescent : baseEnd_1892473 < baseStart_1892473 := by decide
  rcases family_descends (prefixWord ++ tailWord_1892473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1892484 : List Nat := [2, 3, 2, 1, 2, 1, 2, 1, 7]
def baseStart_1892484 : Nat := 118140960795 + 1892484 * 2 ^ 59
def prefixEnd_1892484 : Nat := 4983230072969 + 3 ^ 40 * 1892484 * 2
def baseEnd_1892484 : Nat := 431890632419323947265169

theorem tailTrace_1892484 : CollatzResearch.WordTrace tailWord_1892484 prefixEnd_1892484 431890632419323947265169 := by
  unfold tailWord_1892484
  simp only [CollatzResearch.WordTrace]
  refine ⟨34512281037930576690102253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46016374717240768920136337 34512281037930576690102253)
  ·
    refine ⟨12942105389223966258788345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34512281037930576690102253 12942105389223966258788345)
    ·
      refine ⟨9706579041917974694091259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12942105389223966258788345 9706579041917974694091259)
      ·
        refine ⟨14559868562876962041136889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9706579041917974694091259 14559868562876962041136889)
        ·
          refine ⟨10919901422157721530852667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14559868562876962041136889 10919901422157721530852667)
          ·
            refine ⟨16379852133236582296279001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10919901422157721530852667 16379852133236582296279001)
            ·
              refine ⟨12284889099927436722209251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16379852133236582296279001 12284889099927436722209251)
              ·
                refine ⟨18427333649891155083313877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12284889099927436722209251 18427333649891155083313877)
                ·
                  refine ⟨431890632419323947265169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18427333649891155083313877 431890632419323947265169)
                  ·
                    rfl

theorem cell21_1892484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 1, 7].length) (baseStart_1892484 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1892484 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1892484 prefixEnd_1892484 := by exact prefixLift 1892484
  have htrace : WordTrace (prefixWord ++ tailWord_1892484) baseStart_1892484 baseEnd_1892484 := by
    simpa [prefixWord, tailWord_1892484, baseEnd_1892484] using wordTrace_append hprefix tailTrace_1892484
  have hstable : (prefixWord ++ tailWord_1892484).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1892484).length < 2 ^ (prefixWord ++ tailWord_1892484).sum := by decide
  have hdescent : baseEnd_1892484 < baseStart_1892484 := by decide
  rcases family_descends (prefixWord ++ tailWord_1892484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1892501 : List Nat := [1, 3, 2, 1, 1, 1, 4, 5, 3]
def baseStart_1892501 : Nat := 118140960795 + 1892501 * 2 ^ 59
def prefixEnd_1892501 : Nat := 4983230072969 + 3 ^ 40 * 1892501 * 2
def baseEnd_1892501 : Nat := 431894512050935695481801

theorem tailTrace_1892501 : CollatzResearch.WordTrace tailWord_1892501 prefixEnd_1892501 431894512050935695481801 := by
  unfold tailWord_1892501
  simp only [CollatzResearch.WordTrace]
  refine ⟨69025182116799565283573357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46016788077866376855715571 69025182116799565283573357)
  ·
    refine ⟨25884443293799836981340009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69025182116799565283573357 25884443293799836981340009)
    ·
      refine ⟨19413332470349877736005007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25884443293799836981340009 19413332470349877736005007)
      ·
        refine ⟨29119998705524816604007511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19413332470349877736005007 29119998705524816604007511)
        ·
          refine ⟨43679998058287224906011267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29119998705524816604007511 43679998058287224906011267)
          ·
            refine ⟨65519997087430837359016901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43679998058287224906011267 65519997087430837359016901)
            ·
              refine ⟨12284999453893282004815669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65519997087430837359016901 12284999453893282004815669)
              ·
                refine ⟨1151718698802495187951469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12284999453893282004815669 1151718698802495187951469)
                ·
                  refine ⟨431894512050935695481801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1151718698802495187951469 431894512050935695481801)
                  ·
                    rfl

theorem cell21_1892501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 5, 3].length) (baseStart_1892501 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1892501 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1892501 prefixEnd_1892501 := by exact prefixLift 1892501
  have htrace : WordTrace (prefixWord ++ tailWord_1892501) baseStart_1892501 baseEnd_1892501 := by
    simpa [prefixWord, tailWord_1892501, baseEnd_1892501] using wordTrace_append hprefix tailTrace_1892501
  have hstable : (prefixWord ++ tailWord_1892501).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1892501).length < 2 ^ (prefixWord ++ tailWord_1892501).sum := by decide
  have hdescent : baseEnd_1892501 < baseStart_1892501 := by decide
  rcases family_descends (prefixWord ++ tailWord_1892501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1892566 : List Nat := [5, 2, 1, 2, 1, 3, 1, 2, 4]
def baseStart_1892566 : Nat := 118140960795 + 1892566 * 2 ^ 59
def prefixEnd_1892566 : Nat := 4983230072969 + 3 ^ 40 * 1892566 * 2
def baseEnd_1892566 : Nat := 431909345936510026898335

theorem tailTrace_1892566 : CollatzResearch.WordTrace tailWord_1892566 prefixEnd_1892566 431909345936510026898335 := by
  unfold tailWord_1892566
  simp only [CollatzResearch.WordTrace]
  refine ⟨4314222053847755086543097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46018368574376054256459701 4314222053847755086543097)
  ·
    refine ⟨3235666540385816314907323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4314222053847755086543097 3235666540385816314907323)
    ·
      refine ⟨4853499810578724472360985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3235666540385816314907323 4853499810578724472360985)
      ·
        refine ⟨3640124857934043354270739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4853499810578724472360985 3640124857934043354270739)
        ·
          refine ⟨5460187286901065031406109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3640124857934043354270739 5460187286901065031406109)
          ·
            refine ⟨2047570232587899386777291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5460187286901065031406109 2047570232587899386777291)
            ·
              refine ⟨3071355348881849080165937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2047570232587899386777291 3071355348881849080165937)
              ·
                refine ⟨2303516511661386810124453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3071355348881849080165937 2303516511661386810124453)
                ·
                  refine ⟨431909345936510026898335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2303516511661386810124453 431909345936510026898335)
                  ·
                    rfl

theorem cell21_1892566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_1892566 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1892566 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1892566 prefixEnd_1892566 := by exact prefixLift 1892566
  have htrace : WordTrace (prefixWord ++ tailWord_1892566) baseStart_1892566 baseEnd_1892566 := by
    simpa [prefixWord, tailWord_1892566, baseEnd_1892566] using wordTrace_append hprefix tailTrace_1892566
  have hstable : (prefixWord ++ tailWord_1892566).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1892566).length < 2 ^ (prefixWord ++ tailWord_1892566).sum := by decide
  have hdescent : baseEnd_1892566 < baseStart_1892566 := by decide
  rcases family_descends (prefixWord ++ tailWord_1892566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1892577 : List Nat := [1, 2, 3, 1, 3, 1, 1, 6, 3]
def baseStart_1892577 : Nat := 118140960795 + 1892577 * 2 ^ 59
def prefixEnd_1892577 : Nat := 4983230072969 + 3 ^ 40 * 1892577 * 2
def baseEnd_1892577 : Nat := 431911856286376452214979

theorem tailTrace_1892577 : CollatzResearch.WordTrace tailWord_1892577 prefixEnd_1892577 431911856286376452214979 := by
  unfold tailWord_1892577
  simp only [CollatzResearch.WordTrace]
  refine ⟨69027954064524230263339985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46018636043016153508893323 69027954064524230263339985)
  ·
    refine ⟨51770965548393172697504989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69027954064524230263339985 51770965548393172697504989)
    ·
      refine ⟨19414112080647439761564371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51770965548393172697504989 19414112080647439761564371)
      ·
        refine ⟨29121168120971159642346557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19414112080647439761564371 29121168120971159642346557)
        ·
          refine ⟨10920438045364184865879959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29121168120971159642346557 10920438045364184865879959)
          ·
            refine ⟨16380657068046277298819939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10920438045364184865879959 16380657068046277298819939)
            ·
              refine ⟨24570985602069415948229909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16380657068046277298819939 24570985602069415948229909)
              ·
                refine ⟨1151764950097003872573277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 24570985602069415948229909 1151764950097003872573277)
                ·
                  refine ⟨431911856286376452214979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1151764950097003872573277 431911856286376452214979)
                  ·
                    rfl

theorem cell21_1892577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 6, 3].length) (baseStart_1892577 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1892577 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1892577 prefixEnd_1892577 := by exact prefixLift 1892577
  have htrace : WordTrace (prefixWord ++ tailWord_1892577) baseStart_1892577 baseEnd_1892577 := by
    simpa [prefixWord, tailWord_1892577, baseEnd_1892577] using wordTrace_append hprefix tailTrace_1892577
  have hstable : (prefixWord ++ tailWord_1892577).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1892577).length < 2 ^ (prefixWord ++ tailWord_1892577).sum := by decide
  have hdescent : baseEnd_1892577 < baseStart_1892577 := by decide
  rcases family_descends (prefixWord ++ tailWord_1892577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1892712 : List Nat := [2, 1, 4, 2, 2, 1, 1, 1, 7]
def baseStart_1892712 : Nat := 118140960795 + 1892712 * 2 ^ 59
def prefixEnd_1892712 : Nat := 4983230072969 + 3 ^ 40 * 1892712 * 2
def baseEnd_1892712 : Nat := 431942665125646217464703

theorem tailTrace_1892712 : CollatzResearch.WordTrace tailWord_1892712 prefixEnd_1892712 431942665125646217464703 := by
  unfold tailWord_1892712
  simp only [CollatzResearch.WordTrace]
  refine ⟨34516438959517574159752195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46021918612690098879669593 34516438959517574159752195)
  ·
    refine ⟨51774658439276361239628293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34516438959517574159752195 51774658439276361239628293)
    ·
      refine ⟨9707748457364317732430305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51774658439276361239628293 9707748457364317732430305)
      ·
        refine ⟨7280811343023238299322729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9707748457364317732430305 7280811343023238299322729)
        ·
          refine ⟨5460608507267428724492047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7280811343023238299322729 5460608507267428724492047)
          ·
            refine ⟨8190912760901143086738071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5460608507267428724492047 8190912760901143086738071)
            ·
              refine ⟨12286369141351714630107107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8190912760901143086738071 12286369141351714630107107)
              ·
                refine ⟨18429553712027571945160661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12286369141351714630107107 18429553712027571945160661)
                ·
                  refine ⟨431942665125646217464703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18429553712027571945160661 431942665125646217464703)
                  ·
                    rfl

theorem cell21_1892712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 1, 7].length) (baseStart_1892712 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1892712 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1892712 prefixEnd_1892712 := by exact prefixLift 1892712
  have htrace : WordTrace (prefixWord ++ tailWord_1892712) baseStart_1892712 baseEnd_1892712 := by
    simpa [prefixWord, tailWord_1892712, baseEnd_1892712] using wordTrace_append hprefix tailTrace_1892712
  have hstable : (prefixWord ++ tailWord_1892712).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1892712).length < 2 ^ (prefixWord ++ tailWord_1892712).sum := by decide
  have hdescent : baseEnd_1892712 < baseStart_1892712 := by decide
  rcases family_descends (prefixWord ++ tailWord_1892712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1892746 : List Nat := [3, 1, 2, 5, 1, 1, 2, 1, 5]
def baseStart_1892746 : Nat := 118140960795 + 1892746 * 2 ^ 59
def prefixEnd_1892746 : Nat := 4983230072969 + 3 ^ 40 * 1892746 * 2
def baseEnd_1892746 : Nat := 431950424388869713897967

theorem tailTrace_1892746 : CollatzResearch.WordTrace tailWord_1892746 prefixEnd_1892746 431950424388869713897967 := by
  unfold tailWord_1892746
  simp only [CollatzResearch.WordTrace]
  refine ⟨17258529500227993031560523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46022745333941314750828061 17258529500227993031560523)
  ·
    refine ⟨25887794250341989547340785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17258529500227993031560523 25887794250341989547340785)
    ·
      refine ⟨19415845687756492160505589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25887794250341989547340785 19415845687756492160505589)
      ·
        refine ⟨1820235533227171140047399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19415845687756492160505589 1820235533227171140047399)
        ·
          refine ⟨2730353299840756710071099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1820235533227171140047399 2730353299840756710071099)
          ·
            refine ⟨4095529949761135065106649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2730353299840756710071099 4095529949761135065106649)
            ·
              refine ⟨3071647462320851298829987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4095529949761135065106649 3071647462320851298829987)
              ·
                refine ⟨4607471193481276948244981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3071647462320851298829987 4607471193481276948244981)
                ·
                  refine ⟨431950424388869713897967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4607471193481276948244981 431950424388869713897967)
                  ·
                    rfl

theorem cell21_1892746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 2, 1, 5].length) (baseStart_1892746 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1892746 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1892746 prefixEnd_1892746 := by exact prefixLift 1892746
  have htrace : WordTrace (prefixWord ++ tailWord_1892746) baseStart_1892746 baseEnd_1892746 := by
    simpa [prefixWord, tailWord_1892746, baseEnd_1892746] using wordTrace_append hprefix tailTrace_1892746
  have hstable : (prefixWord ++ tailWord_1892746).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1892746).length < 2 ^ (prefixWord ++ tailWord_1892746).sum := by decide
  have hdescent : baseEnd_1892746 < baseStart_1892746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1892746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1892850 : List Nat := [3, 2, 1, 4, 3, 8]
def baseStart_1892850 : Nat := 118140960795 + 1892850 * 2 ^ 59
def prefixEnd_1892850 : Nat := 4983230072969 + 3 ^ 40 * 1892850 * 2
def baseEnd_1892850 : Nat := 15999042911325505339423

theorem tailTrace_1892850 : CollatzResearch.WordTrace tailWord_1892850 prefixEnd_1892850 15999042911325505339423 := by
  unfold tailWord_1892850
  simp only [CollatzResearch.WordTrace]
  refine ⟨17259477798133799472007001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46025274128356798592018669 17259477798133799472007001)
  ·
    refine ⟨12944608348600349604005251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17259477798133799472007001 12944608348600349604005251)
    ·
      refine ⟨19416912522900524406007877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12944608348600349604005251 19416912522900524406007877)
      ·
        refine ⟨3640671098043848326126477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19416912522900524406007877 3640671098043848326126477)
        ·
          refine ⟨1365251661766443122297429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3640671098043848326126477 1365251661766443122297429)
          ·
            refine ⟨15999042911325505339423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1365251661766443122297429 15999042911325505339423)
            ·
              rfl

theorem cell21_1892850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 8].length) (baseStart_1892850 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1892850 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1892850 prefixEnd_1892850 := by exact prefixLift 1892850
  have htrace : WordTrace (prefixWord ++ tailWord_1892850) baseStart_1892850 baseEnd_1892850 := by
    simpa [prefixWord, tailWord_1892850, baseEnd_1892850] using wordTrace_append hprefix tailTrace_1892850
  have hstable : (prefixWord ++ tailWord_1892850).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1892850).length < 2 ^ (prefixWord ++ tailWord_1892850).sum := by decide
  have hdescent : baseEnd_1892850 < baseStart_1892850 := by decide
  rcases family_descends (prefixWord ++ tailWord_1892850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1892853 : List Nat := [1, 3, 5, 1, 2, 1, 2, 2, 4]
def baseStart_1892853 : Nat := 118140960795 + 1892853 * 2 ^ 59
def prefixEnd_1892853 : Nat := 4983230072969 + 3 ^ 40 * 1892853 * 2
def baseEnd_1892853 : Nat := 431974843246661305614415

theorem tailTrace_1892853 : CollatzResearch.WordTrace tailWord_1892853 prefixEnd_1892853 431974843246661305614415 := by
  unfold tailWord_1892853
  simp only [CollatzResearch.WordTrace]
  refine ⟨69038020611524329400387213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46025347074349552933591475 69038020611524329400387213)
  ·
    refine ⟨25889257729321623525145205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69038020611524329400387213 25889257729321623525145205)
    ·
      refine ⟨2427117912123902205482363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25889257729321623525145205 2427117912123902205482363)
      ·
        refine ⟨3640676868185853308223545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2427117912123902205482363 3640676868185853308223545)
        ·
          refine ⟨2730507651139389981167659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3640676868185853308223545 2730507651139389981167659)
          ·
            refine ⟨4095761476709084971751489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2730507651139389981167659 4095761476709084971751489)
            ·
              refine ⟨3071821107531813728813617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4095761476709084971751489 3071821107531813728813617)
              ·
                refine ⟨2303865830648860296610213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3071821107531813728813617 2303865830648860296610213)
                ·
                  refine ⟨431974843246661305614415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2303865830648860296610213 431974843246661305614415)
                  ·
                    rfl

theorem cell21_1892853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 2, 2, 4].length) (baseStart_1892853 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1892853 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1892853 prefixEnd_1892853 := by exact prefixLift 1892853
  have htrace : WordTrace (prefixWord ++ tailWord_1892853) baseStart_1892853 baseEnd_1892853 := by
    simpa [prefixWord, tailWord_1892853, baseEnd_1892853] using wordTrace_append hprefix tailTrace_1892853
  have hstable : (prefixWord ++ tailWord_1892853).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1892853).length < 2 ^ (prefixWord ++ tailWord_1892853).sum := by decide
  have hdescent : baseEnd_1892853 < baseStart_1892853 := by decide
  rcases family_descends (prefixWord ++ tailWord_1892853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1892870 : List Nat := [6, 2, 1, 1, 1, 1, 2, 3, 4]
def baseStart_1892870 : Nat := 118140960795 + 1892870 * 2 ^ 59
def prefixEnd_1892870 : Nat := 4983230072969 + 3 ^ 40 * 1892870 * 2
def baseEnd_1892870 : Nat := 431978722878273053831047

theorem tailTrace_1892870 : CollatzResearch.WordTrace tailWord_1892870 prefixEnd_1892870 431978722878273053831047 := by
  unfold tailWord_1892870
  simp only [CollatzResearch.WordTrace]
  refine ⟨2157457520389460665742377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 46025760434975160869170709 2157457520389460665742377)
  ·
    refine ⟨1618093140292095499306783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2157457520389460665742377 1618093140292095499306783)
    ·
      refine ⟨2427139710438143248960175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1618093140292095499306783 2427139710438143248960175)
      ·
        refine ⟨3640709565657214873440263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2427139710438143248960175 3640709565657214873440263)
        ·
          refine ⟨5461064348485822310160395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3640709565657214873440263 5461064348485822310160395)
          ·
            refine ⟨8191596522728733465240593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5461064348485822310160395 8191596522728733465240593)
            ·
              refine ⟨6143697392046550098930445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8191596522728733465240593 6143697392046550098930445)
              ·
                refine ⟨2303886522017456287098917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6143697392046550098930445 2303886522017456287098917)
                ·
                  refine ⟨431978722878273053831047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2303886522017456287098917 431978722878273053831047)
                  ·
                    rfl

theorem cell21_1892870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_1892870 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1892870 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1892870 prefixEnd_1892870 := by exact prefixLift 1892870
  have htrace : WordTrace (prefixWord ++ tailWord_1892870) baseStart_1892870 baseEnd_1892870 := by
    simpa [prefixWord, tailWord_1892870, baseEnd_1892870] using wordTrace_append hprefix tailTrace_1892870
  have hstable : (prefixWord ++ tailWord_1892870).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1892870).length < 2 ^ (prefixWord ++ tailWord_1892870).sum := by decide
  have hdescent : baseEnd_1892870 < baseStart_1892870 := by decide
  rcases family_descends (prefixWord ++ tailWord_1892870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1892985 : List Nat := [1, 2, 1, 3, 3, 3, 2, 6]
def baseStart_1892985 : Nat := 118140960795 + 1892985 * 2 ^ 59
def prefixEnd_1892985 : Nat := 4983230072969 + 3 ^ 40 * 1892985 * 2
def baseEnd_1892985 : Nat := 144001655815019469804715

theorem tailTrace_1892985 : CollatzResearch.WordTrace tailWord_1892985 prefixEnd_1892985 144001655815019469804715 := by
  unfold tailWord_1892985
  simp only [CollatzResearch.WordTrace]
  refine ⟨69042835047046115944192409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46028556698030743962794939 69042835047046115944192409)
  ·
    refine ⟨51782126285284586958144307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69042835047046115944192409 51782126285284586958144307)
    ·
      refine ⟨77673189427926880437216461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51782126285284586958144307 77673189427926880437216461)
      ·
        refine ⟨29127446035472580163956173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77673189427926880437216461 29127446035472580163956173)
        ·
          refine ⟨10922792263302217561483565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29127446035472580163956173 10922792263302217561483565)
          ·
            refine ⟨4096047098738331585556337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10922792263302217561483565 4096047098738331585556337)
            ·
              refine ⟨3072035324053748689167253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4096047098738331585556337 3072035324053748689167253)
              ·
                refine ⟨144001655815019469804715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3072035324053748689167253 144001655815019469804715)
                ·
                  rfl

theorem cell21_1892985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 2, 6].length) (baseStart_1892985 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1892985 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1892985 prefixEnd_1892985 := by exact prefixLift 1892985
  have htrace : WordTrace (prefixWord ++ tailWord_1892985) baseStart_1892985 baseEnd_1892985 := by
    simpa [prefixWord, tailWord_1892985, baseEnd_1892985] using wordTrace_append hprefix tailTrace_1892985
  have hstable : (prefixWord ++ tailWord_1892985).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1892985).length < 2 ^ (prefixWord ++ tailWord_1892985).sum := by decide
  have hdescent : baseEnd_1892985 < baseStart_1892985 := by decide
  rcases family_descends (prefixWord ++ tailWord_1892985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1892999 : List Nat := [1, 1, 4, 2, 1, 2, 2, 1, 7]
def baseStart_1892999 : Nat := 118140960795 + 1892999 * 2 ^ 59
def prefixEnd_1892999 : Nat := 4983230072969 + 3 ^ 40 * 1892999 * 2
def baseEnd_1892999 : Nat := 432008162435797496180783

theorem tailTrace_1892999 : CollatzResearch.WordTrace tailWord_1892999 prefixEnd_1892999 432008162435797496180783 := by
  unfold tailWord_1892999
  simp only [CollatzResearch.WordTrace]
  refine ⟨69043345668995396335202051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46028897112663597556801367 69043345668995396335202051)
  ·
    refine ⟨103565018503493094502803077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69043345668995396335202051 103565018503493094502803077)
    ·
      refine ⟨19418440969404955219275577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103565018503493094502803077 19418440969404955219275577)
      ·
        refine ⟨14563830727053716414456683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19418440969404955219275577 14563830727053716414456683)
        ·
          refine ⟨21845746090580574621685025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14563830727053716414456683 21845746090580574621685025)
          ·
            refine ⟨16384309567935430966263769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21845746090580574621685025 16384309567935430966263769)
            ·
              refine ⟨12288232175951573224697827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16384309567935430966263769 12288232175951573224697827)
              ·
                refine ⟨18432348263927359837046741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12288232175951573224697827 18432348263927359837046741)
                ·
                  refine ⟨432008162435797496180783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18432348263927359837046741 432008162435797496180783)
                  ·
                    rfl

theorem cell21_1892999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 1, 7].length) (baseStart_1892999 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1892999 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1892999 prefixEnd_1892999 := by exact prefixLift 1892999
  have htrace : WordTrace (prefixWord ++ tailWord_1892999) baseStart_1892999 baseEnd_1892999 := by
    simpa [prefixWord, tailWord_1892999, baseEnd_1892999] using wordTrace_append hprefix tailTrace_1892999
  have hstable : (prefixWord ++ tailWord_1892999).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1892999).length < 2 ^ (prefixWord ++ tailWord_1892999).sum := by decide
  have hdescent : baseEnd_1892999 < baseStart_1892999 := by decide
  rcases family_descends (prefixWord ++ tailWord_1892999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1893092 : List Nat := [2, 3, 1, 1, 1, 5, 2, 1, 5]
def baseStart_1893092 : Nat := 118140960795 + 1893092 * 2 ^ 59
def prefixEnd_1893092 : Nat := 4983230072969 + 3 ^ 40 * 1893092 * 2
def baseEnd_1893092 : Nat := 432029386302850001130593

theorem tailTrace_1893092 : CollatzResearch.WordTrace tailWord_1893092 prefixEnd_1893092 432029386302850001130593 := by
  unfold tailWord_1893092
  simp only [CollatzResearch.WordTrace]
  refine ⟨34523368828829236609168765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46031158438438982145558353 34523368828829236609168765)
  ·
    refine ⟨12946263310810963728438287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34523368828829236609168765 12946263310810963728438287)
    ·
      refine ⟨19419394966216445592657431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12946263310810963728438287 19419394966216445592657431)
      ·
        refine ⟨29129092449324668388986147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19419394966216445592657431 29129092449324668388986147)
        ·
          refine ⟨43693638673987002583479221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29129092449324668388986147 43693638673987002583479221)
          ·
            refine ⟨4096278625686281492201177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43693638673987002583479221 4096278625686281492201177)
            ·
              refine ⟨3072208969264711119150883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4096278625686281492201177 3072208969264711119150883)
              ·
                refine ⟨4608313453897066678726325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3072208969264711119150883 4608313453897066678726325)
                ·
                  refine ⟨432029386302850001130593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4608313453897066678726325 432029386302850001130593)
                  ·
                    rfl

theorem cell21_1893092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 2, 1, 5].length) (baseStart_1893092 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1893092 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1893092 prefixEnd_1893092 := by exact prefixLift 1893092
  have htrace : WordTrace (prefixWord ++ tailWord_1893092) baseStart_1893092 baseEnd_1893092 := by
    simpa [prefixWord, tailWord_1893092, baseEnd_1893092] using wordTrace_append hprefix tailTrace_1893092
  have hstable : (prefixWord ++ tailWord_1893092).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1893092).length < 2 ^ (prefixWord ++ tailWord_1893092).sum := by decide
  have hdescent : baseEnd_1893092 < baseStart_1893092 := by decide
  rcases family_descends (prefixWord ++ tailWord_1893092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1893196 : List Nat := [2, 2, 1, 3, 3, 10]
def baseStart_1893196 : Nat := 118140960795 + 1893196 * 2 ^ 59
def prefixEnd_1893196 : Nat := 4983230072969 + 3 ^ 40 * 1893196 * 2
def baseEnd_1893196 : Nat := 16001967426658108570261

theorem tailTrace_1893196 : CollatzResearch.WordTrace tailWord_1893196 prefixEnd_1893196 16001967426658108570261 := by
  unfold tailWord_1893196
  simp only [CollatzResearch.WordTrace]
  refine ⟨34525265424640849490061721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46033687232854465986748961 34525265424640849490061721)
  ·
    refine ⟨25893949068480637117546291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34525265424640849490061721 25893949068480637117546291)
    ·
      refine ⟨38840923602720955676319437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25893949068480637117546291 38840923602720955676319437)
      ·
        refine ⟨14565346351020358378619789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38840923602720955676319437 14565346351020358378619789)
        ·
          refine ⟨5462004881632634391982421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14565346351020358378619789 5462004881632634391982421)
          ·
            refine ⟨16001967426658108570261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5462004881632634391982421 16001967426658108570261)
            ·
              rfl

theorem cell21_1893196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 10].length) (baseStart_1893196 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1893196 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1893196 prefixEnd_1893196 := by exact prefixLift 1893196
  have htrace : WordTrace (prefixWord ++ tailWord_1893196) baseStart_1893196 baseEnd_1893196 := by
    simpa [prefixWord, tailWord_1893196, baseEnd_1893196] using wordTrace_append hprefix tailTrace_1893196
  have hstable : (prefixWord ++ tailWord_1893196).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1893196).length < 2 ^ (prefixWord ++ tailWord_1893196).sum := by decide
  have hdescent : baseEnd_1893196 < baseStart_1893196 := by decide
  rcases family_descends (prefixWord ++ tailWord_1893196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1893250 : List Nat := [3, 4, 2, 2, 1, 2, 1, 2, 4]
def baseStart_1893250 : Nat := 118140960795 + 1893250 * 2 ^ 59
def prefixEnd_1893250 : Nat := 4983230072969 + 3 ^ 40 * 1893250 * 2
def baseEnd_1893250 : Nat := 432065444055476837496937

theorem tailTrace_1893250 : CollatzResearch.WordTrace tailWord_1893250 prefixEnd_1893250 432065444055476837496937 := by
  unfold tailWord_1893250
  simp only [CollatzResearch.WordTrace]
  refine ⟨17263125097771516550647301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46035000260724044135059469 17263125097771516550647301)
  ·
    refine ⟨3236835955832159353246369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17263125097771516550647301 3236835955832159353246369)
    ·
      refine ⟨2427626966874119514934777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3236835955832159353246369 2427626966874119514934777)
      ·
        refine ⟨1820720225155589636201083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2427626966874119514934777 1820720225155589636201083)
        ·
          refine ⟨2731080337733384454301625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1820720225155589636201083 2731080337733384454301625)
          ·
            refine ⟨2048310253300038340726219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2731080337733384454301625 2048310253300038340726219)
            ·
              refine ⟨3072465379950057511089329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2048310253300038340726219 3072465379950057511089329)
              ·
                refine ⟨2304349034962543133316997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3072465379950057511089329 2304349034962543133316997)
                ·
                  refine ⟨432065444055476837496937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2304349034962543133316997 432065444055476837496937)
                  ·
                    rfl

theorem cell21_1893250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_1893250 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1893250 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1893250 prefixEnd_1893250 := by exact prefixLift 1893250
  have htrace : WordTrace (prefixWord ++ tailWord_1893250) baseStart_1893250 baseEnd_1893250 := by
    simpa [prefixWord, tailWord_1893250, baseEnd_1893250] using wordTrace_append hprefix tailTrace_1893250
  have hstable : (prefixWord ++ tailWord_1893250).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1893250).length < 2 ^ (prefixWord ++ tailWord_1893250).sum := by decide
  have hdescent : baseEnd_1893250 < baseStart_1893250 := by decide
  rcases family_descends (prefixWord ++ tailWord_1893250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1893365 : List Nat := [1, 3, 5, 2, 10]
def baseStart_1893365 : Nat := 118140960795 + 1893365 * 2 ^ 59
def prefixEnd_1893365 : Nat := 4983230072969 + 3 ^ 40 * 1893365 * 2
def baseEnd_1893365 : Nat := 5334465291632866581235

theorem tailTrace_1893365 : CollatzResearch.WordTrace tailWord_1893365 prefixEnd_1893365 5334465291632866581235 := by
  unfold tailWord_1893365
  simp only [CollatzResearch.WordTrace]
  refine ⟨69056694785669440843025549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46037796523779627228683699 69056694785669440843025549)
  ·
    refine ⟨25896260544626040316134581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69056694785669440843025549 25896260544626040316134581)
    ·
      refine ⟨2427774426058691279637617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25896260544626040316134581 2427774426058691279637617)
      ·
        refine ⟨1820830819544018459728213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2427774426058691279637617 1820830819544018459728213)
        ·
          refine ⟨5334465291632866581235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1820830819544018459728213 5334465291632866581235)
          ·
            rfl

theorem cell21_1893365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 10].length) (baseStart_1893365 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1893365 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1893365 prefixEnd_1893365 := by exact prefixLift 1893365
  have htrace : WordTrace (prefixWord ++ tailWord_1893365) baseStart_1893365 baseEnd_1893365 := by
    simpa [prefixWord, tailWord_1893365, baseEnd_1893365] using wordTrace_append hprefix tailTrace_1893365
  have hstable : (prefixWord ++ tailWord_1893365).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1893365).length < 2 ^ (prefixWord ++ tailWord_1893365).sum := by decide
  have hdescent : baseEnd_1893365 < baseStart_1893365 := by decide
  rcases family_descends (prefixWord ++ tailWord_1893365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1893458 : List Nat := [3, 2, 2, 1, 3, 3, 2, 5]
def baseStart_1893458 : Nat := 118140960795 + 1893458 * 2 ^ 59
def prefixEnd_1893458 : Nat := 4983230072969 + 3 ^ 40 * 1893458 * 2
def baseEnd_1893458 : Nat := 144037637496438232676615

theorem tailTrace_1893458 : CollatzResearch.WordTrace tailWord_1893458 prefixEnd_1893458 144037637496438232676615 := by
  unfold tailWord_1893458
  simp only [CollatzResearch.WordTrace]
  refine ⟨17265021693583129431540257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46040057849555011817440685 17265021693583129431540257)
  ·
    refine ⟨12948766270187347073655193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17265021693583129431540257 12948766270187347073655193)
    ·
      refine ⟨9711574702640510305241395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12948766270187347073655193 9711574702640510305241395)
      ·
        refine ⟨14567362053960765457862093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9711574702640510305241395 14567362053960765457862093)
        ·
          refine ⟨5462760770235287046698285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14567362053960765457862093 5462760770235287046698285)
          ·
            refine ⟨2048535288838232642511857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5462760770235287046698285 2048535288838232642511857)
            ·
              refine ⟨1536401466628674481883893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2048535288838232642511857 1536401466628674481883893)
              ·
                refine ⟨144037637496438232676615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1536401466628674481883893 144037637496438232676615)
                ·
                  rfl

theorem cell21_1893458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 2, 5].length) (baseStart_1893458 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1893458 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1893458 prefixEnd_1893458 := by exact prefixLift 1893458
  have htrace : WordTrace (prefixWord ++ tailWord_1893458) baseStart_1893458 baseEnd_1893458 := by
    simpa [prefixWord, tailWord_1893458, baseEnd_1893458] using wordTrace_append hprefix tailTrace_1893458
  have hstable : (prefixWord ++ tailWord_1893458).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1893458).length < 2 ^ (prefixWord ++ tailWord_1893458).sum := by decide
  have hdescent : baseEnd_1893458 < baseStart_1893458 := by decide
  rcases family_descends (prefixWord ++ tailWord_1893458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1893486 : List Nat := [4, 1, 2, 2, 1, 2, 2, 1, 6]
def baseStart_1893486 : Nat := 118140960795 + 1893486 * 2 ^ 59
def prefixEnd_1893486 : Nat := 4983230072969 + 3 ^ 40 * 1893486 * 2
def baseEnd_1893486 : Nat := 432119302470792871563121

theorem tailTrace_1893486 : CollatzResearch.WordTrace tailWord_1893486 prefixEnd_1893486 432119302470792871563121 := by
  unfold tailWord_1893486
  simp only [CollatzResearch.WordTrace]
  refine ⟨8632638502278884813522539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46040738678820719005453541 8632638502278884813522539)
  ·
    refine ⟨12948957753418327220283809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8632638502278884813522539 12948957753418327220283809)
    ·
      refine ⟨9711718315063745415212857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12948957753418327220283809 9711718315063745415212857)
      ·
        refine ⟨7283788736297809061409643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9711718315063745415212857 7283788736297809061409643)
        ·
          refine ⟨10925683104446713592114465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7283788736297809061409643 10925683104446713592114465)
          ·
            refine ⟨8194262328335035194085849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10925683104446713592114465 8194262328335035194085849)
            ·
              refine ⟨6145696746251276395564387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8194262328335035194085849 6145696746251276395564387)
              ·
                refine ⟨9218545119376914593346581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6145696746251276395564387 9218545119376914593346581)
                ·
                  refine ⟨432119302470792871563121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9218545119376914593346581 432119302470792871563121)
                  ·
                    rfl

theorem cell21_1893486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 1, 6].length) (baseStart_1893486 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1893486 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1893486 prefixEnd_1893486 := by exact prefixLift 1893486
  have htrace : WordTrace (prefixWord ++ tailWord_1893486) baseStart_1893486 baseEnd_1893486 := by
    simpa [prefixWord, tailWord_1893486, baseEnd_1893486] using wordTrace_append hprefix tailTrace_1893486
  have hstable : (prefixWord ++ tailWord_1893486).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1893486).length < 2 ^ (prefixWord ++ tailWord_1893486).sum := by decide
  have hdescent : baseEnd_1893486 < baseStart_1893486 := by decide
  rcases family_descends (prefixWord ++ tailWord_1893486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1893500 : List Nat := [2, 2, 2, 1, 1, 3, 4, 6]
def baseStart_1893500 : Nat := 118140960795 + 1893500 * 2 ^ 59
def prefixEnd_1893500 : Nat := 4983230072969 + 3 ^ 40 * 1893500 * 2
def baseEnd_1893500 : Nat := 144040832487177319443253

theorem tailTrace_1893500 : CollatzResearch.WordTrace tailWord_1893500 prefixEnd_1893500 144040832487177319443253 := by
  unfold tailWord_1893500
  simp only [CollatzResearch.WordTrace]
  refine ⟨34530809320090179449594977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46041079093453572599459969 34530809320090179449594977)
  ·
    refine ⟨25898106990067634587196233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34530809320090179449594977 25898106990067634587196233)
    ·
      refine ⟨19423580242550725940397175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25898106990067634587196233 19423580242550725940397175)
      ·
        refine ⟨29135370363826088910595763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19423580242550725940397175 29135370363826088910595763)
        ·
          refine ⟨43703055545739133365893645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29135370363826088910595763 43703055545739133365893645)
          ·
            refine ⟨16388645829652175012210117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43703055545739133365893645 16388645829652175012210117)
            ·
              refine ⟨3072871093059782814789397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16388645829652175012210117 3072871093059782814789397)
              ·
                refine ⟨144040832487177319443253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3072871093059782814789397 144040832487177319443253)
                ·
                  rfl

theorem cell21_1893500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 4, 6].length) (baseStart_1893500 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1893500 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1893500 prefixEnd_1893500 := by exact prefixLift 1893500
  have htrace : WordTrace (prefixWord ++ tailWord_1893500) baseStart_1893500 baseEnd_1893500 := by
    simpa [prefixWord, tailWord_1893500, baseEnd_1893500] using wordTrace_append hprefix tailTrace_1893500
  have hstable : (prefixWord ++ tailWord_1893500).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1893500).length < 2 ^ (prefixWord ++ tailWord_1893500).sum := by decide
  have hdescent : baseEnd_1893500 < baseStart_1893500 := by decide
  rcases family_descends (prefixWord ++ tailWord_1893500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1893672 : List Nat := [2, 1, 5, 1, 2, 3, 2, 1, 4]
def baseStart_1893672 : Nat := 118140960795 + 1893672 * 2 ^ 59
def prefixEnd_1893672 : Nat := 4983230072969 + 3 ^ 40 * 1893672 * 2
def baseEnd_1893672 : Nat := 432161750204897881462741

theorem tailTrace_1893672 : CollatzResearch.WordTrace tailWord_1893672 prefixEnd_1893672 432161750204897881462741 := by
  unfold tailWord_1893672
  simp only [CollatzResearch.WordTrace]
  refine ⟨34533945997778616137225635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46045261330371488182967513 34533945997778616137225635)
  ·
    refine ⟨51800918996667924205838453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34533945997778616137225635 51800918996667924205838453)
    ·
      refine ⟨4856336155937617894297355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 51800918996667924205838453 4856336155937617894297355)
      ·
        refine ⟨7284504233906426841446033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4856336155937617894297355 7284504233906426841446033)
        ·
          refine ⟨5463378175429820131084525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7284504233906426841446033 5463378175429820131084525)
          ·
            refine ⟨2048766815786182549156697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5463378175429820131084525 2048766815786182549156697)
            ·
              refine ⟨1536575111839636911867523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2048766815786182549156697 1536575111839636911867523)
              ·
                refine ⟨2304862667759455367801285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1536575111839636911867523 2304862667759455367801285)
                ·
                  refine ⟨432161750204897881462741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2304862667759455367801285 432161750204897881462741)
                  ·
                    rfl

theorem cell21_1893672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 2, 1, 4].length) (baseStart_1893672 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1893672 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1893672 prefixEnd_1893672 := by exact prefixLift 1893672
  have htrace : WordTrace (prefixWord ++ tailWord_1893672) baseStart_1893672 baseEnd_1893672 := by
    simpa [prefixWord, tailWord_1893672, baseEnd_1893672] using wordTrace_append hprefix tailTrace_1893672
  have hstable : (prefixWord ++ tailWord_1893672).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1893672).length < 2 ^ (prefixWord ++ tailWord_1893672).sum := by decide
  have hdescent : baseEnd_1893672 < baseStart_1893672 := by decide
  rcases family_descends (prefixWord ++ tailWord_1893672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1893717 : List Nat := [1, 3, 2, 2, 3, 1, 4, 2, 3]
def baseStart_1893717 : Nat := 118140960795 + 1893717 * 2 ^ 59
def prefixEnd_1893717 : Nat := 4983230072969 + 3 ^ 40 * 1893717 * 2
def baseEnd_1893717 : Nat := 432172019817987803212649

theorem tailTrace_1893717 : CollatzResearch.WordTrace tailWord_1893717 prefixEnd_1893717 432172019817987803212649 := by
  unfold tailWord_1893717
  simp only [CollatzResearch.WordTrace]
  refine ⟨69069533280394204959839405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46046355520262803306559603 69069533280394204959839405)
  ·
    refine ⟨25901074980147826859939777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69069533280394204959839405 25901074980147826859939777)
    ·
      refine ⟨19425806235110870144954833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25901074980147826859939777 19425806235110870144954833)
      ·
        refine ⟨14569354676333152608716125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19425806235110870144954833 14569354676333152608716125)
        ·
          refine ⟨5463508003624932228268547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14569354676333152608716125 5463508003624932228268547)
          ·
            refine ⟨8195262005437398342402821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5463508003624932228268547 8195262005437398342402821)
            ·
              refine ⟨1536611626019512189200529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8195262005437398342402821 1536611626019512189200529)
              ·
                refine ⟨1152458719514634141900397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1536611626019512189200529 1152458719514634141900397)
                ·
                  refine ⟨432172019817987803212649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1152458719514634141900397 432172019817987803212649)
                  ·
                    rfl

theorem cell21_1893717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 4, 2, 3].length) (baseStart_1893717 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1893717 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1893717 prefixEnd_1893717 := by exact prefixLift 1893717
  have htrace : WordTrace (prefixWord ++ tailWord_1893717) baseStart_1893717 baseEnd_1893717 := by
    simpa [prefixWord, tailWord_1893717, baseEnd_1893717] using wordTrace_append hprefix tailTrace_1893717
  have hstable : (prefixWord ++ tailWord_1893717).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1893717).length < 2 ^ (prefixWord ++ tailWord_1893717).sum := by decide
  have hdescent : baseEnd_1893717 < baseStart_1893717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1893717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1893728 : List Nat := [2, 1, 1, 3, 4, 1, 3, 6]
def baseStart_1893728 : Nat := 118140960795 + 1893728 * 2 ^ 59
def prefixEnd_1893728 : Nat := 4983230072969 + 3 ^ 40 * 1893728 * 2
def baseEnd_1893728 : Nat := 144058176722618076176431

theorem tailTrace_1893728 : CollatzResearch.WordTrace tailWord_1893728 prefixEnd_1893728 144058176722618076176431 := by
  unfold tailWord_1893728
  simp only [CollatzResearch.WordTrace]
  refine ⟨34534967241677176919244919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46046622988902902558993225 34534967241677176919244919)
  ·
    refine ⟨51802450862515765378867379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34534967241677176919244919 51802450862515765378867379)
    ·
      refine ⟨77703676293773648068301069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51802450862515765378867379 77703676293773648068301069)
      ·
        refine ⟨29138878610165118025612901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77703676293773648068301069 29138878610165118025612901)
        ·
          refine ⟨5463539739405959629802419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29138878610165118025612901 5463539739405959629802419)
          ·
            refine ⟨8195309609108939444703629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5463539739405959629802419 8195309609108939444703629)
            ·
              refine ⟨3073241103415852291763861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8195309609108939444703629 3073241103415852291763861)
              ·
                refine ⟨144058176722618076176431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3073241103415852291763861 144058176722618076176431)
                ·
                  rfl

theorem cell21_1893728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 3, 6].length) (baseStart_1893728 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1893728 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1893728 prefixEnd_1893728 := by exact prefixLift 1893728
  have htrace : WordTrace (prefixWord ++ tailWord_1893728) baseStart_1893728 baseEnd_1893728 := by
    simpa [prefixWord, tailWord_1893728, baseEnd_1893728] using wordTrace_append hprefix tailTrace_1893728
  have hstable : (prefixWord ++ tailWord_1893728).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1893728).length < 2 ^ (prefixWord ++ tailWord_1893728).sum := by decide
  have hdescent : baseEnd_1893728 < baseStart_1893728 := by decide
  rcases family_descends (prefixWord ++ tailWord_1893728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1893804 : List Nat := [2, 2, 1, 1, 1, 1, 8, 5]
def baseStart_1893804 : Nat := 118140960795 + 1893804 * 2 ^ 59
def prefixEnd_1893804 : Nat := 4983230072969 + 3 ^ 40 * 1893804 * 2
def baseEnd_1893804 : Nat := 144063958134431661754157

theorem tailTrace_1893804 : CollatzResearch.WordTrace tailWord_1893804 prefixEnd_1893804 144063958134431661754157 := by
  unfold tailWord_1893804
  simp only [CollatzResearch.WordTrace]
  refine ⟨34536353215539509409128233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46048470954052679212170977 34536353215539509409128233)
  ·
    refine ⟨25902264911654632056846175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34536353215539509409128233 25902264911654632056846175)
    ·
      refine ⟨38853397367481948085269263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25902264911654632056846175 38853397367481948085269263)
      ·
        refine ⟨58280096051222922127903895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38853397367481948085269263 58280096051222922127903895)
        ·
          refine ⟨87420144076834383191855843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58280096051222922127903895 87420144076834383191855843)
          ·
            refine ⟨131130216115251574787783765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87420144076834383191855843 131130216115251574787783765)
            ·
              refine ⟨1536682220100604392044341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 131130216115251574787783765 1536682220100604392044341)
              ·
                refine ⟨144063958134431661754157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1536682220100604392044341 144063958134431661754157)
                ·
                  rfl

theorem cell21_1893804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 8, 5].length) (baseStart_1893804 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1893804 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1893804 prefixEnd_1893804 := by exact prefixLift 1893804
  have htrace : WordTrace (prefixWord ++ tailWord_1893804) baseStart_1893804 baseEnd_1893804 := by
    simpa [prefixWord, tailWord_1893804, baseEnd_1893804] using wordTrace_append hprefix tailTrace_1893804
  have hstable : (prefixWord ++ tailWord_1893804).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1893804).length < 2 ^ (prefixWord ++ tailWord_1893804).sum := by decide
  have hdescent : baseEnd_1893804 < baseStart_1893804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1893804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1893835 : List Nat := [1, 1, 1, 1, 3, 3, 2, 6, 3]
def baseStart_1893835 : Nat := 118140960795 + 1893835 * 2 ^ 59
def prefixEnd_1893835 : Nat := 4983230072969 + 3 ^ 40 * 1893835 * 2
def baseEnd_1893835 : Nat := 432198949025645820245741

theorem tailTrace_1893835 : CollatzResearch.WordTrace tailWord_1893835 prefixEnd_1893835 432198949025645820245741 := by
  unfold tailWord_1893835
  simp only [CollatzResearch.WordTrace]
  refine ⟨69073837093966711112634959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46049224729311140741756639 69073837093966711112634959)
  ·
    refine ⟨103610755640950066668952439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69073837093966711112634959 103610755640950066668952439)
    ·
      refine ⟨155416133461425100003428659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103610755640950066668952439 155416133461425100003428659)
      ·
        refine ⟨233124200192137650005142989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155416133461425100003428659 233124200192137650005142989)
        ·
          refine ⟨87421575072051618751928621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 233124200192137650005142989 87421575072051618751928621)
          ·
            refine ⟨32783090652019357031973233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87421575072051618751928621 32783090652019357031973233)
            ·
              refine ⟨24587317989014517773979925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32783090652019357031973233 24587317989014517773979925)
              ·
                refine ⟨1152530530735055520655309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 24587317989014517773979925 1152530530735055520655309)
                ·
                  refine ⟨432198949025645820245741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1152530530735055520655309 432198949025645820245741)
                  ·
                    rfl

theorem cell21_1893835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 6, 3].length) (baseStart_1893835 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1893835 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1893835 prefixEnd_1893835 := by exact prefixLift 1893835
  have htrace : WordTrace (prefixWord ++ tailWord_1893835) baseStart_1893835 baseEnd_1893835 := by
    simpa [prefixWord, tailWord_1893835, baseEnd_1893835] using wordTrace_append hprefix tailTrace_1893835
  have hstable : (prefixWord ++ tailWord_1893835).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1893835).length < 2 ^ (prefixWord ++ tailWord_1893835).sum := by decide
  have hdescent : baseEnd_1893835 < baseStart_1893835 := by decide
  rcases family_descends (prefixWord ++ tailWord_1893835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1893886 : List Nat := [4, 2, 2, 3, 1, 1, 1, 4, 3]
def baseStart_1893886 : Nat := 118140960795 + 1893886 * 2 ^ 59
def prefixEnd_1893886 : Nat := 4983230072969 + 3 ^ 40 * 1893886 * 2
def baseEnd_1893886 : Nat := 432210587920481064895637

theorem tailTrace_1893886 : CollatzResearch.WordTrace tailWord_1893886 prefixEnd_1893886 432210587920481064895637 := by
  unfold tailWord_1893886
  simp only [CollatzResearch.WordTrace]
  refine ⟨8634462152097743352842689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46050464811187964548494341 8634462152097743352842689)
  ·
    refine ⟨6475846614073307514632017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8634462152097743352842689 6475846614073307514632017)
    ·
      refine ⟨4856884960554980635974013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6475846614073307514632017 4856884960554980635974013)
      ·
        refine ⟨1821331860208117738490255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4856884960554980635974013 1821331860208117738490255)
        ·
          refine ⟨2731997790312176607735383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1821331860208117738490255 2731997790312176607735383)
          ·
            refine ⟨4097996685468264911603075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2731997790312176607735383 4097996685468264911603075)
            ·
              refine ⟨6146995028202397367404613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4097996685468264911603075 6146995028202397367404613)
              ·
                refine ⟨1152561567787949506388365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6146995028202397367404613 1152561567787949506388365)
                ·
                  refine ⟨432210587920481064895637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1152561567787949506388365 432210587920481064895637)
                  ·
                    rfl

theorem cell21_1893886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 4, 3].length) (baseStart_1893886 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1893886 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1893886 prefixEnd_1893886 := by exact prefixLift 1893886
  have htrace : WordTrace (prefixWord ++ tailWord_1893886) baseStart_1893886 baseEnd_1893886 := by
    simpa [prefixWord, tailWord_1893886, baseEnd_1893886] using wordTrace_append hprefix tailTrace_1893886
  have hstable : (prefixWord ++ tailWord_1893886).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1893886).length < 2 ^ (prefixWord ++ tailWord_1893886).sum := by decide
  have hdescent : baseEnd_1893886 < baseStart_1893886 := by decide
  rcases family_descends (prefixWord ++ tailWord_1893886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1893939 : List Nat := [1, 1, 1, 2, 4, 4, 8]
def baseStart_1893939 : Nat := 118140960795 + 1893939 * 2 ^ 59
def prefixEnd_1893939 : Nat := 4983230072969 + 3 ^ 40 * 1893939 * 2
def baseEnd_1893939 : Nat := 48024742582507194501355

theorem tailTrace_1893939 : CollatzResearch.WordTrace tailWord_1893939 prefixEnd_1893939 48024742582507194501355 := by
  unfold tailWord_1893939
  simp only [CollatzResearch.WordTrace]
  refine ⟨69077630285589936874420871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46051753523726624582947247 69077630285589936874420871)
  ·
    refine ⟨103616445428384905311631307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69077630285589936874420871 103616445428384905311631307)
    ·
      refine ⟨155424668142577357967446961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103616445428384905311631307 155424668142577357967446961)
      ·
        refine ⟨116568501106933018475585221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155424668142577357967446961 116568501106933018475585221)
        ·
          refine ⟨21856593957549940964172229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 116568501106933018475585221 21856593957549940964172229)
          ·
            refine ⟨4098111367040613930782293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21856593957549940964172229 4098111367040613930782293)
            ·
              refine ⟨48024742582507194501355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4098111367040613930782293 48024742582507194501355)
              ·
                rfl

theorem cell21_1893939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 8].length) (baseStart_1893939 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1893939 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1893939 prefixEnd_1893939 := by exact prefixLift 1893939
  have htrace : WordTrace (prefixWord ++ tailWord_1893939) baseStart_1893939 baseEnd_1893939 := by
    simpa [prefixWord, tailWord_1893939, baseEnd_1893939] using wordTrace_append hprefix tailTrace_1893939
  have hstable : (prefixWord ++ tailWord_1893939).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1893939).length < 2 ^ (prefixWord ++ tailWord_1893939).sum := by decide
  have hdescent : baseEnd_1893939 < baseStart_1893939 := by decide
  rcases family_descends (prefixWord ++ tailWord_1893939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1893959 : List Nat := [1, 1, 4, 1, 5, 1, 3, 1, 4]
def baseStart_1893959 : Nat := 118140960795 + 1893959 * 2 ^ 59
def prefixEnd_1893959 : Nat := 4983230072969 + 3 ^ 40 * 1893959 * 2
def baseEnd_1893959 : Nat := 432227247515049160178821

theorem tailTrace_1893959 : CollatzResearch.WordTrace tailWord_1893959 prefixEnd_1893959 432227247515049160178821 := by
  unfold tailWord_1893959
  simp only [CollatzResearch.WordTrace]
  refine ⟨69078359745517480290148931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46052239830344986860099287 69078359745517480290148931)
  ·
    refine ⟨103617539618276220435223397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69078359745517480290148931 103617539618276220435223397)
    ·
      refine ⟨19428288678426791331604387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103617539618276220435223397 19428288678426791331604387)
      ·
        refine ⟨29142433017640186997406581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19428288678426791331604387 29142433017640186997406581)
        ·
          refine ⟨2732103095403767531006867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29142433017640186997406581 2732103095403767531006867)
          ·
            refine ⟨4098154643105651296510301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2732103095403767531006867 4098154643105651296510301)
            ·
              refine ⟨1536807991164619236191363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4098154643105651296510301 1536807991164619236191363)
              ·
                refine ⟨2305211986746928854287045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1536807991164619236191363 2305211986746928854287045)
                ·
                  refine ⟨432227247515049160178821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2305211986746928854287045 432227247515049160178821)
                  ·
                    rfl

theorem cell21_1893959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 3, 1, 4].length) (baseStart_1893959 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1893959 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1893959 prefixEnd_1893959 := by exact prefixLift 1893959
  have htrace : WordTrace (prefixWord ++ tailWord_1893959) baseStart_1893959 baseEnd_1893959 := by
    simpa [prefixWord, tailWord_1893959, baseEnd_1893959] using wordTrace_append hprefix tailTrace_1893959
  have hstable : (prefixWord ++ tailWord_1893959).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1893959).length < 2 ^ (prefixWord ++ tailWord_1893959).sum := by decide
  have hdescent : baseEnd_1893959 < baseStart_1893959 := by decide
  rcases family_descends (prefixWord ++ tailWord_1893959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1894063 : List Nat := [1, 1, 2, 1, 2, 4, 3, 4, 3]
def baseStart_1894063 : Nat := 118140960795 + 1894063 * 2 ^ 59
def prefixEnd_1894063 : Nat := 4983230072969 + 3 ^ 40 * 1894063 * 2
def baseEnd_1894063 : Nat := 432250981731968090445275

theorem tailTrace_1894063 : CollatzResearch.WordTrace tailWord_1894063 prefixEnd_1894063 432250981731968090445275 := by
  unfold tailWord_1894063
  simp only [CollatzResearch.WordTrace]
  refine ⟨69082152937140706051934843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46054768624760470701289895 69082152937140706051934843)
  ·
    refine ⟨103623229405711059077902265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69082152937140706051934843 103623229405711059077902265)
    ·
      refine ⟨77717422054283294308426699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103623229405711059077902265 77717422054283294308426699)
      ·
        refine ⟨116576133081424941462640049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77717422054283294308426699 116576133081424941462640049)
        ·
          refine ⟨87432099811068706096980037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116576133081424941462640049 87432099811068706096980037)
          ·
            refine ⟨16393518714575382393183757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87432099811068706096980037 16393518714575382393183757)
            ·
              refine ⟨6147569517965768397443909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16393518714575382393183757 6147569517965768397443909)
              ·
                refine ⟨1152669284618581574520733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6147569517965768397443909 1152669284618581574520733)
                ·
                  refine ⟨432250981731968090445275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1152669284618581574520733 432250981731968090445275)
                  ·
                    rfl

theorem cell21_1894063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 4, 3].length) (baseStart_1894063 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1894063 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1894063 prefixEnd_1894063 := by exact prefixLift 1894063
  have htrace : WordTrace (prefixWord ++ tailWord_1894063) baseStart_1894063 baseEnd_1894063 := by
    simpa [prefixWord, tailWord_1894063, baseEnd_1894063] using wordTrace_append hprefix tailTrace_1894063
  have hstable : (prefixWord ++ tailWord_1894063).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1894063).length < 2 ^ (prefixWord ++ tailWord_1894063).sum := by decide
  have hdescent : baseEnd_1894063 < baseStart_1894063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1894063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1894077 : List Nat := [1, 4, 1, 2, 1, 2, 1, 5, 4]
def baseStart_1894077 : Nat := 118140960795 + 1894077 * 2 ^ 59
def prefixEnd_1894077 : Nat := 4983230072969 + 3 ^ 40 * 1894077 * 2
def baseEnd_1894077 : Nat := 432254176722707177211913

theorem tailTrace_1894077 : CollatzResearch.WordTrace tailWord_1894077 prefixEnd_1894077 432254176722707177211913 := by
  unfold tailWord_1894077
  simp only [CollatzResearch.WordTrace]
  refine ⟨69082663559089986442944485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46055109039393324295296323 69082663559089986442944485)
  ·
    refine ⟨12952999417329372458052091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69082663559089986442944485 12952999417329372458052091)
    ·
      refine ⟨19429499125994058687078137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12952999417329372458052091 19429499125994058687078137)
      ·
        refine ⟨14572124344495544015308603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19429499125994058687078137 14572124344495544015308603)
        ·
          refine ⟨21858186516743316022962905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14572124344495544015308603 21858186516743316022962905)
          ·
            refine ⟨16393639887557487017222179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21858186516743316022962905 16393639887557487017222179)
            ·
              refine ⟨24590459831336230525833269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16393639887557487017222179 24590459831336230525833269)
              ·
                refine ⟨2305355609187771611796869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24590459831336230525833269 2305355609187771611796869)
                ·
                  refine ⟨432254176722707177211913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2305355609187771611796869 432254176722707177211913)
                  ·
                    rfl

theorem cell21_1894077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 5, 4].length) (baseStart_1894077 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1894077 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1894077 prefixEnd_1894077 := by exact prefixLift 1894077
  have htrace : WordTrace (prefixWord ++ tailWord_1894077) baseStart_1894077 baseEnd_1894077 := by
    simpa [prefixWord, tailWord_1894077, baseEnd_1894077] using wordTrace_append hprefix tailTrace_1894077
  have hstable : (prefixWord ++ tailWord_1894077).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1894077).length < 2 ^ (prefixWord ++ tailWord_1894077).sum := by decide
  have hdescent : baseEnd_1894077 < baseStart_1894077 := by decide
  rcases family_descends (prefixWord ++ tailWord_1894077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1894122 : List Nat := [3, 1, 3, 1, 1, 1, 3, 3, 5]
def baseStart_1894122 : Nat := 118140960795 + 1894122 * 2 ^ 59
def prefixEnd_1894122 : Nat := 4983230072969 + 3 ^ 40 * 1894122 * 2
def baseEnd_1894122 : Nat := 432264446335797098961821

theorem tailTrace_1894122 : CollatzResearch.WordTrace tailWord_1894122 prefixEnd_1894122 432264446335797098961821 := by
  unfold tailWord_1894122
  simp only [CollatzResearch.WordTrace]
  refine ⟨17271076210981739782083155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46056203229284639418888413 17271076210981739782083155)
  ·
    refine ⟨25906614316472609673124733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17271076210981739782083155 25906614316472609673124733)
    ·
      refine ⟨9714980368677228627421775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25906614316472609673124733 9714980368677228627421775)
      ·
        refine ⟨14572470553015842941132663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9714980368677228627421775 14572470553015842941132663)
        ·
          refine ⟨21858705829523764411698995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14572470553015842941132663 21858705829523764411698995)
          ·
            refine ⟨32788058744285646617548493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21858705829523764411698995 32788058744285646617548493)
            ·
              refine ⟨12295522029107117481580685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32788058744285646617548493 12295522029107117481580685)
              ·
                refine ⟨4610820760915169055592757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12295522029107117481580685 4610820760915169055592757)
                ·
                  refine ⟨432264446335797098961821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4610820760915169055592757 432264446335797098961821)
                  ·
                    rfl

theorem cell21_1894122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 3, 5].length) (baseStart_1894122 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1894122 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1894122 prefixEnd_1894122 := by exact prefixLift 1894122
  have htrace : WordTrace (prefixWord ++ tailWord_1894122) baseStart_1894122 baseEnd_1894122 := by
    simpa [prefixWord, tailWord_1894122, baseEnd_1894122] using wordTrace_append hprefix tailTrace_1894122
  have hstable : (prefixWord ++ tailWord_1894122).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1894122).length < 2 ^ (prefixWord ++ tailWord_1894122).sum := by decide
  have hdescent : baseEnd_1894122 < baseStart_1894122 := by decide
  rcases family_descends (prefixWord ++ tailWord_1894122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1894142 : List Nat := [4, 2, 2, 1, 3, 2, 2, 5]
def baseStart_1894142 : Nat := 118140960795 + 1894142 * 2 ^ 59
def prefixEnd_1894142 : Nat := 4983230072969 + 3 ^ 40 * 1894142 * 2
def baseEnd_1894142 : Nat := 144089670202760502876149

theorem tailTrace_1894142 : CollatzResearch.WordTrace tailWord_1894142 prefixEnd_1894142 144089670202760502876149 := by
  unfold tailWord_1894142
  simp only [CollatzResearch.WordTrace]
  refine ⟨8635629287981812818007585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46056689535903001696040453 8635629287981812818007585)
  ·
    refine ⟨6476721965986359613505689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8635629287981812818007585 6476721965986359613505689)
    ·
      refine ⟨4857541474489769710129267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6476721965986359613505689 4857541474489769710129267)
      ·
        refine ⟨7286312211734654565193901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4857541474489769710129267 7286312211734654565193901)
        ·
          refine ⟨2732367079400495461947713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7286312211734654565193901 2732367079400495461947713)
          ·
            refine ⟨2049275309550371596460785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2732367079400495461947713 2049275309550371596460785)
            ·
              refine ⟨1536956482162778697345589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2049275309550371596460785 1536956482162778697345589)
              ·
                refine ⟨144089670202760502876149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1536956482162778697345589 144089670202760502876149)
                ·
                  rfl

theorem cell21_1894142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 2, 5].length) (baseStart_1894142 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1894142 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1894142 prefixEnd_1894142 := by exact prefixLift 1894142
  have htrace : WordTrace (prefixWord ++ tailWord_1894142) baseStart_1894142 baseEnd_1894142 := by
    simpa [prefixWord, tailWord_1894142, baseEnd_1894142] using wordTrace_append hprefix tailTrace_1894142
  have hstable : (prefixWord ++ tailWord_1894142).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1894142).length < 2 ^ (prefixWord ++ tailWord_1894142).sum := by decide
  have hdescent : baseEnd_1894142 < baseStart_1894142 := by decide
  rcases family_descends (prefixWord ++ tailWord_1894142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1894167 : List Nat := [1, 1, 3, 4, 2, 1, 9]
def baseStart_1894167 : Nat := 118140960795 + 1894167 * 2 ^ 59
def prefixEnd_1894167 : Nat := 4983230072969 + 3 ^ 40 * 1894167 * 2
def baseEnd_1894167 : Nat := 48030523994320780079081

theorem tailTrace_1894167 : CollatzResearch.WordTrace tailWord_1894167 prefixEnd_1894167 48030523994320780079081 := by
  unfold tailWord_1894167
  simp only [CollatzResearch.WordTrace]
  refine ⟨69085946128763931813720755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46057297419175954542480503 69085946128763931813720755)
  ·
    refine ⟨103628919193145897720581133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69085946128763931813720755 103628919193145897720581133)
    ·
      refine ⟨38860844697429711645217925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103628919193145897720581133 38860844697429711645217925)
      ·
        refine ⟨7286408380768070933478361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38860844697429711645217925 7286408380768070933478361)
        ·
          refine ⟨5464806285576053200108771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7286408380768070933478361 5464806285576053200108771)
          ·
            refine ⟨8197209428364079800163157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5464806285576053200108771 8197209428364079800163157)
            ·
              refine ⟨48030523994320780079081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8197209428364079800163157 48030523994320780079081)
              ·
                rfl

theorem cell21_1894167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 9].length) (baseStart_1894167 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1894167 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1894167 prefixEnd_1894167 := by exact prefixLift 1894167
  have htrace : WordTrace (prefixWord ++ tailWord_1894167) baseStart_1894167 baseEnd_1894167 := by
    simpa [prefixWord, tailWord_1894167, baseEnd_1894167] using wordTrace_append hprefix tailTrace_1894167
  have hstable : (prefixWord ++ tailWord_1894167).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1894167).length < 2 ^ (prefixWord ++ tailWord_1894167).sum := by decide
  have hdescent : baseEnd_1894167 < baseStart_1894167 := by decide
  rcases family_descends (prefixWord ++ tailWord_1894167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1894184 : List Nat := [2, 1, 5, 1, 1, 3, 2, 6]
def baseStart_1894184 : Nat := 118140960795 + 1894184 * 2 ^ 59
def prefixEnd_1894184 : Nat := 4983230072969 + 3 ^ 40 * 1894184 * 2
def baseEnd_1894184 : Nat := 144092865193499589642787

theorem tailTrace_1894184 : CollatzResearch.WordTrace tailWord_1894184 prefixEnd_1894184 144092865193499589642787 := by
  unfold tailWord_1894184
  simp only [CollatzResearch.WordTrace]
  refine ⟨34543283084851171858544803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46057710779801562478059737 34543283084851171858544803)
  ·
    refine ⟨51814924627276757787817205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34543283084851171858544803 51814924627276757787817205)
    ·
      refine ⟨4857649183807196042607863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 51814924627276757787817205 4857649183807196042607863)
      ·
        refine ⟨7286473775710794063911795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4857649183807196042607863 7286473775710794063911795)
        ·
          refine ⟨10929710663566191095867693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7286473775710794063911795 10929710663566191095867693)
          ·
            refine ⟨4098641498837321660950385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10929710663566191095867693 4098641498837321660950385)
            ·
              refine ⟨3073981124127991245712789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4098641498837321660950385 3073981124127991245712789)
              ·
                refine ⟨144092865193499589642787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3073981124127991245712789 144092865193499589642787)
                ·
                  rfl

theorem cell21_1894184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 2, 6].length) (baseStart_1894184 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1894184 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1894184 prefixEnd_1894184 := by exact prefixLift 1894184
  have htrace : WordTrace (prefixWord ++ tailWord_1894184) baseStart_1894184 baseEnd_1894184 := by
    simpa [prefixWord, tailWord_1894184, baseEnd_1894184] using wordTrace_append hprefix tailTrace_1894184
  have hstable : (prefixWord ++ tailWord_1894184).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1894184).length < 2 ^ (prefixWord ++ tailWord_1894184).sum := by decide
  have hdescent : baseEnd_1894184 < baseStart_1894184 := by decide
  rcases family_descends (prefixWord ++ tailWord_1894184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1894229 : List Nat := [1, 3, 2, 2, 2, 2, 1, 4, 4]
def baseStart_1894229 : Nat := 118140960795 + 1894229 * 2 ^ 59
def prefixEnd_1894229 : Nat := 4983230072969 + 3 ^ 40 * 1894229 * 2
def baseEnd_1894229 : Nat := 432288865193588690678269

theorem tailTrace_1894229 : CollatzResearch.WordTrace tailWord_1894229 prefixEnd_1894229 432288865193588690678269 := by
  unfold tailWord_1894229
  simp only [CollatzResearch.WordTrace]
  refine ⟨69088207454539316402477741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46058804969692877601651827 69088207454539316402477741)
  ·
    refine ⟨25908077795452243650929153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69088207454539316402477741 25908077795452243650929153)
    ·
      refine ⟨19431058346589182738196865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25908077795452243650929153 19431058346589182738196865)
      ·
        refine ⟨14573293759941887053647649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19431058346589182738196865 14573293759941887053647649)
        ·
          refine ⟨10929970319956415290235737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14573293759941887053647649 10929970319956415290235737)
          ·
            refine ⟨8197477739967311467676803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10929970319956415290235737 8197477739967311467676803)
            ·
              refine ⟨12296216609950967201515205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8197477739967311467676803 12296216609950967201515205)
              ·
                refine ⟨2305540614365806350284101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12296216609950967201515205 2305540614365806350284101)
                ·
                  refine ⟨432288865193588690678269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2305540614365806350284101 432288865193588690678269)
                  ·
                    rfl

theorem cell21_1894229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 4, 4].length) (baseStart_1894229 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1894229 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1894229 prefixEnd_1894229 := by exact prefixLift 1894229
  have htrace : WordTrace (prefixWord ++ tailWord_1894229) baseStart_1894229 baseEnd_1894229 := by
    simpa [prefixWord, tailWord_1894229, baseEnd_1894229] using wordTrace_append hprefix tailTrace_1894229
  have hstable : (prefixWord ++ tailWord_1894229).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1894229).length < 2 ^ (prefixWord ++ tailWord_1894229).sum := by decide
  have hdescent : baseEnd_1894229 < baseStart_1894229 := by decide
  rcases family_descends (prefixWord ++ tailWord_1894229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1894398 : List Nat := [4, 2, 2, 2, 1, 1, 1, 4, 4]
def baseStart_1894398 : Nat := 118140960795 + 1894398 * 2 ^ 59
def prefixEnd_1894398 : Nat := 4983230072969 + 3 ^ 40 * 1894398 * 2
def baseEnd_1894398 : Nat := 432327433296081952361257

theorem tailTrace_1894398 : CollatzResearch.WordTrace tailWord_1894398 prefixEnd_1894398 432327433296081952361257 := by
  unfold tailWord_1894398
  simp only [CollatzResearch.WordTrace]
  refine ⟨8636796423865882283172481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46062914260618038843586565 8636796423865882283172481)
  ·
    refine ⟨6477597317899411712379361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8636796423865882283172481 6477597317899411712379361)
    ·
      refine ⟨4858197988424558784284521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6477597317899411712379361 4858197988424558784284521)
      ·
        refine ⟨3643648491318419088213391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4858197988424558784284521 3643648491318419088213391)
        ·
          refine ⟨5465472736977628632320087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3643648491318419088213391 5465472736977628632320087)
          ·
            refine ⟨8198209105466442948480131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5465472736977628632320087 8198209105466442948480131)
            ·
              refine ⟨12297313658199664422720197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8198209105466442948480131 12297313658199664422720197)
              ·
                refine ⟨2305746310912437079260037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12297313658199664422720197 2305746310912437079260037)
                ·
                  refine ⟨432327433296081952361257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2305746310912437079260037 432327433296081952361257)
                  ·
                    rfl

theorem cell21_1894398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 4, 4].length) (baseStart_1894398 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1894398 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1894398 prefixEnd_1894398 := by exact prefixLift 1894398
  have htrace : WordTrace (prefixWord ++ tailWord_1894398) baseStart_1894398 baseEnd_1894398 := by
    simpa [prefixWord, tailWord_1894398, baseEnd_1894398] using wordTrace_append hprefix tailTrace_1894398
  have hstable : (prefixWord ++ tailWord_1894398).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1894398).length < 2 ^ (prefixWord ++ tailWord_1894398).sum := by decide
  have hdescent : baseEnd_1894398 < baseStart_1894398 := by decide
  rcases family_descends (prefixWord ++ tailWord_1894398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1894426 : List Nat := [3, 1, 1, 3, 1, 4, 1, 2, 5]
def baseStart_1894426 : Nat := 118140960795 + 1894426 * 2 ^ 59
def prefixEnd_1894426 : Nat := 4983230072969 + 3 ^ 40 * 1894426 * 2
def baseEnd_1894426 : Nat := 432333823277560125894533

theorem tailTrace_1894426 : CollatzResearch.WordTrace tailWord_1894426 prefixEnd_1894426 432333823277560125894533 := by
  unfold tailWord_1894426
  simp only [CollatzResearch.WordTrace]
  refine ⟨17273848158706404761849783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46063595089883746031599421 17273848158706404761849783)
  ·
    refine ⟨25910772238059607142774675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17273848158706404761849783 25910772238059607142774675)
    ·
      refine ⟨38866158357089410714162013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25910772238059607142774675 38866158357089410714162013)
      ·
        refine ⟨14574809383908529017810755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38866158357089410714162013 14574809383908529017810755)
        ·
          refine ⟨21862214075862793526716133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14574809383908529017810755 21862214075862793526716133)
          ·
            refine ⟨4099165139224273786259275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21862214075862793526716133 4099165139224273786259275)
            ·
              refine ⟨6148747708836410679388913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4099165139224273786259275 6148747708836410679388913)
              ·
                refine ⟨4611560781627308009541685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6148747708836410679388913 4611560781627308009541685)
                ·
                  refine ⟨432333823277560125894533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4611560781627308009541685 432333823277560125894533)
                  ·
                    rfl

theorem cell21_1894426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 2, 5].length) (baseStart_1894426 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1894426 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1894426 prefixEnd_1894426 := by exact prefixLift 1894426
  have htrace : WordTrace (prefixWord ++ tailWord_1894426) baseStart_1894426 baseEnd_1894426 := by
    simpa [prefixWord, tailWord_1894426, baseEnd_1894426] using wordTrace_append hprefix tailTrace_1894426
  have hstable : (prefixWord ++ tailWord_1894426).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1894426).length < 2 ^ (prefixWord ++ tailWord_1894426).sum := by decide
  have hdescent : baseEnd_1894426 < baseStart_1894426 := by decide
  rcases family_descends (prefixWord ++ tailWord_1894426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1894457 : List Nat := [1, 2, 1, 5, 3, 1, 1, 1, 6]
def baseStart_1894457 : Nat := 118140960795 + 1894457 * 2 ^ 59
def prefixEnd_1894457 : Nat := 4983230072969 + 3 ^ 40 * 1894457 * 2
def baseEnd_1894457 : Nat := 432340897899910960877803

theorem tailTrace_1894457 : CollatzResearch.WordTrace tailWord_1894457 prefixEnd_1894457 432340897899910960877803 := by
  unfold tailWord_1894457
  simp only [CollatzResearch.WordTrace]
  refine ⟨69096523297713311341777625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46064348865142207561185083 69096523297713311341777625)
  ·
    refine ⟨51822392473284983506333219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69096523297713311341777625 51822392473284983506333219)
    ·
      refine ⟨77733588709927475259499829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51822392473284983506333219 77733588709927475259499829)
      ·
        refine ⟨7287523941555700805578109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 77733588709927475259499829 7287523941555700805578109)
        ·
          refine ⟨2732821478083387802091791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7287523941555700805578109 2732821478083387802091791)
          ·
            refine ⟨4099232217125081703137687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2732821478083387802091791 4099232217125081703137687)
            ·
              refine ⟨6148848325687622554706531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4099232217125081703137687 6148848325687622554706531)
              ·
                refine ⟨9223272488531433832059797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6148848325687622554706531 9223272488531433832059797)
                ·
                  refine ⟨432340897899910960877803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9223272488531433832059797 432340897899910960877803)
                  ·
                    rfl

theorem cell21_1894457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 1, 6].length) (baseStart_1894457 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1894457 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1894457 prefixEnd_1894457 := by exact prefixLift 1894457
  have htrace : WordTrace (prefixWord ++ tailWord_1894457) baseStart_1894457 baseEnd_1894457 := by
    simpa [prefixWord, tailWord_1894457, baseEnd_1894457] using wordTrace_append hprefix tailTrace_1894457
  have hstable : (prefixWord ++ tailWord_1894457).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1894457).length < 2 ^ (prefixWord ++ tailWord_1894457).sum := by decide
  have hdescent : baseEnd_1894457 < baseStart_1894457 := by decide
  rcases family_descends (prefixWord ++ tailWord_1894457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1894488 : List Nat := [2, 1, 2, 2, 1, 6, 2, 5]
def baseStart_1894488 : Nat := 118140960795 + 1894488 * 2 ^ 59
def prefixEnd_1894488 : Nat := 4983230072969 + 3 ^ 40 * 1894488 * 2
def baseEnd_1894488 : Nat := 144115990840753931953691

theorem tailTrace_1894488 : CollatzResearch.WordTrace tailWord_1894488 prefixEnd_1894488 144115990840753931953691 := by
  unfold tailWord_1894488
  simp only [CollatzResearch.WordTrace]
  refine ⟨34548826980300501818078059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46065102640400669090770745 34548826980300501818078059)
  ·
    refine ⟨51823240470450752727117089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34548826980300501818078059 51823240470450752727117089)
    ·
      refine ⟨38867430352838064545337817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51823240470450752727117089 38867430352838064545337817)
      ·
        refine ⟨29150572764628548409003363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38867430352838064545337817 29150572764628548409003363)
        ·
          refine ⟨43725859146942822613505045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29150572764628548409003363 43725859146942822613505045)
          ·
            refine ⟨2049649647512944810008049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 43725859146942822613505045 2049649647512944810008049)
            ·
              refine ⟨1537237235634708607506037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2049649647512944810008049 1537237235634708607506037)
              ·
                refine ⟨144115990840753931953691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1537237235634708607506037 144115990840753931953691)
                ·
                  rfl

theorem cell21_1894488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 2, 5].length) (baseStart_1894488 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1894488 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1894488 prefixEnd_1894488 := by exact prefixLift 1894488
  have htrace : WordTrace (prefixWord ++ tailWord_1894488) baseStart_1894488 baseEnd_1894488 := by
    simpa [prefixWord, tailWord_1894488, baseEnd_1894488] using wordTrace_append hprefix tailTrace_1894488
  have hstable : (prefixWord ++ tailWord_1894488).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1894488).length < 2 ^ (prefixWord ++ tailWord_1894488).sum := by decide
  have hdescent : baseEnd_1894488 < baseStart_1894488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1894488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1894533 : List Nat := [1, 3, 1, 1, 5, 2, 1, 3, 4]
def baseStart_1894533 : Nat := 118140960795 + 1894533 * 2 ^ 59
def prefixEnd_1894533 : Nat := 4983230072969 + 3 ^ 40 * 1894533 * 2
def baseEnd_1894533 : Nat := 432358242135351717610981

theorem tailTrace_1894533 : CollatzResearch.WordTrace tailWord_1894533 prefixEnd_1894533 432358242135351717610981 := by
  unfold tailWord_1894533
  simp only [CollatzResearch.WordTrace]
  refine ⟨69099295245437976321544253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46066196830291984214362835 69099295245437976321544253)
  ·
    refine ⟨25912235717039241120579095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69099295245437976321544253 25912235717039241120579095)
    ·
      refine ⟨38868353575558861680868643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25912235717039241120579095 38868353575558861680868643)
      ·
        refine ⟨58302530363338292521302965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38868353575558861680868643 58302530363338292521302965)
        ·
          refine ⟨5465862221562964923872153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58302530363338292521302965 5465862221562964923872153)
          ·
            refine ⟨4099396666172223692904115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5465862221562964923872153 4099396666172223692904115)
            ·
              refine ⟨6149094999258335539356173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4099396666172223692904115 6149094999258335539356173)
              ·
                refine ⟨2305910624721875827258565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6149094999258335539356173 2305910624721875827258565)
                ·
                  refine ⟨432358242135351717610981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2305910624721875827258565 432358242135351717610981)
                  ·
                    rfl

theorem cell21_1894533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 3, 4].length) (baseStart_1894533 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1894533 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1894533 prefixEnd_1894533 := by exact prefixLift 1894533
  have htrace : WordTrace (prefixWord ++ tailWord_1894533) baseStart_1894533 baseEnd_1894533 := by
    simpa [prefixWord, tailWord_1894533, baseEnd_1894533] using wordTrace_append hprefix tailTrace_1894533
  have hstable : (prefixWord ++ tailWord_1894533).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1894533).length < 2 ^ (prefixWord ++ tailWord_1894533).sum := by decide
  have hdescent : baseEnd_1894533 < baseStart_1894533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1894533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1894570 : List Nat := [3, 1, 5, 1, 2, 2, 2, 2, 3]
def baseStart_1894570 : Nat := 118140960795 + 1894570 * 2 ^ 59
def prefixEnd_1894570 : Nat := 4983230072969 + 3 ^ 40 * 1894570 * 2
def baseEnd_1894570 : Nat := 432366686039447875494239

theorem tailTrace_1894570 : CollatzResearch.WordTrace tailWord_1894570 prefixEnd_1894570 432366686039447875494239 := by
  unfold tailWord_1894570
  simp only [CollatzResearch.WordTrace]
  refine ⟨17275161186575982910160291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46067096497535954427094109 17275161186575982910160291)
  ·
    refine ⟨25912741779863974365240437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17275161186575982910160291 25912741779863974365240437)
    ·
      refine ⟨2429319541862247596741291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25912741779863974365240437 2429319541862247596741291)
      ·
        refine ⟨3643979312793371395111937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2429319541862247596741291 3643979312793371395111937)
        ·
          refine ⟨2732984484595028546333953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3643979312793371395111937 2732984484595028546333953)
          ·
            refine ⟨2049738363446271409750465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2732984484595028546333953 2049738363446271409750465)
            ·
              refine ⟨1537303772584703557312849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2049738363446271409750465 1537303772584703557312849)
              ·
                refine ⟨1152977829438527667984637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1537303772584703557312849 1152977829438527667984637)
                ·
                  refine ⟨432366686039447875494239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1152977829438527667984637 432366686039447875494239)
                  ·
                    rfl

theorem cell21_1894570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 2, 2, 3].length) (baseStart_1894570 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1894570 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1894570 prefixEnd_1894570 := by exact prefixLift 1894570
  have htrace : WordTrace (prefixWord ++ tailWord_1894570) baseStart_1894570 baseEnd_1894570 := by
    simpa [prefixWord, tailWord_1894570, baseEnd_1894570] using wordTrace_append hprefix tailTrace_1894570
  have hstable : (prefixWord ++ tailWord_1894570).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1894570).length < 2 ^ (prefixWord ++ tailWord_1894570).sum := by decide
  have hdescent : baseEnd_1894570 < baseStart_1894570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1894570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1894581 : List Nat := [1, 3, 3, 4, 1, 2, 1, 6]
def baseStart_1894581 : Nat := 118140960795 + 1894581 * 2 ^ 59
def prefixEnd_1894581 : Nat := 4983230072969 + 3 ^ 40 * 1894581 * 2
def baseEnd_1894581 : Nat := 144123065463104766936961

theorem tailTrace_1894581 : CollatzResearch.WordTrace tailWord_1894581 prefixEnd_1894581 144123065463104766936961 := by
  unfold tailWord_1894581
  simp only [CollatzResearch.WordTrace]
  refine ⟨69101045949264080519291597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46067363966176053679527731 69101045949264080519291597)
  ·
    refine ⟨25912892230974030194734349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69101045949264080519291597 25912892230974030194734349)
    ·
      refine ⟨9717334586615261323025381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25912892230974030194734349 9717334586615261323025381)
      ·
        refine ⟨1822000234990361498067259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9717334586615261323025381 1822000234990361498067259)
        ·
          refine ⟨2733000352485542247100889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1822000234990361498067259 2733000352485542247100889)
          ·
            refine ⟨2049750264364156685325667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2733000352485542247100889 2049750264364156685325667)
            ·
              refine ⟨3074625396546235027988501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2049750264364156685325667 3074625396546235027988501)
              ·
                refine ⟨144123065463104766936961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3074625396546235027988501 144123065463104766936961)
                ·
                  rfl

theorem cell21_1894581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 1, 6].length) (baseStart_1894581 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1894581 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1894581 prefixEnd_1894581 := by exact prefixLift 1894581
  have htrace : WordTrace (prefixWord ++ tailWord_1894581) baseStart_1894581 baseEnd_1894581 := by
    simpa [prefixWord, tailWord_1894581, baseEnd_1894581] using wordTrace_append hprefix tailTrace_1894581
  have hstable : (prefixWord ++ tailWord_1894581).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1894581).length < 2 ^ (prefixWord ++ tailWord_1894581).sum := by decide
  have hdescent : baseEnd_1894581 < baseStart_1894581 := by decide
  rcases family_descends (prefixWord ++ tailWord_1894581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1894654 : List Nat := [4, 2, 2, 1, 1, 1, 1, 4, 5]
def baseStart_1894654 : Nat := 118140960795 + 1894654 * 2 ^ 59
def prefixEnd_1894654 : Nat := 4983230072969 + 3 ^ 40 * 1894654 * 2
def baseEnd_1894654 : Nat := 432385855983882396094067

theorem tailTrace_1894654 : CollatzResearch.WordTrace tailWord_1894654 prefixEnd_1894654 432385855983882396094067 := by
  unfold tailWord_1894654
  simp only [CollatzResearch.WordTrace]
  refine ⟨8637963559749951748337377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46069138985333075991132677 8637963559749951748337377)
  ·
    refine ⟨6478472669812463811253033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8637963559749951748337377 6478472669812463811253033)
    ·
      refine ⟨4858854502359347858439775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6478472669812463811253033 4858854502359347858439775)
      ·
        refine ⟨7288281753539021787659663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4858854502359347858439775 7288281753539021787659663)
        ·
          refine ⟨10932422630308532681489495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7288281753539021787659663 10932422630308532681489495)
          ·
            refine ⟨16398633945462799022234243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10932422630308532681489495 16398633945462799022234243)
            ·
              refine ⟨24597950918194198533351365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16398633945462799022234243 24597950918194198533351365)
              ·
                refine ⟨4612115797161412225003381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24597950918194198533351365 4612115797161412225003381)
                ·
                  refine ⟨432385855983882396094067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4612115797161412225003381 432385855983882396094067)
                  ·
                    rfl

theorem cell21_1894654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 4, 5].length) (baseStart_1894654 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1894654 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1894654 prefixEnd_1894654 := by exact prefixLift 1894654
  have htrace : WordTrace (prefixWord ++ tailWord_1894654) baseStart_1894654 baseEnd_1894654 := by
    simpa [prefixWord, tailWord_1894654, baseEnd_1894654] using wordTrace_append hprefix tailTrace_1894654
  have hstable : (prefixWord ++ tailWord_1894654).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1894654).length < 2 ^ (prefixWord ++ tailWord_1894654).sum := by decide
  have hdescent : baseEnd_1894654 < baseStart_1894654 := by decide
  rcases family_descends (prefixWord ++ tailWord_1894654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1894688 : List Nat := [2, 1, 1, 5, 2, 2, 3, 2, 3]
def baseStart_1894688 : Nat := 118140960795 + 1894688 * 2 ^ 59
def prefixEnd_1894688 : Nat := 4983230072969 + 3 ^ 40 * 1894688 * 2
def baseEnd_1894688 : Nat := 432393615247105892527331

theorem tailTrace_1894688 : CollatzResearch.WordTrace tailWord_1894688 prefixEnd_1894688 432393615247105892527331 := by
  unfold tailWord_1894688
  simp only [CollatzResearch.WordTrace]
  refine ⟨34552474279938218896718359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46069965706584291862291145 34552474279938218896718359)
  ·
    refine ⟨51828711419907328345077539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34552474279938218896718359 51828711419907328345077539)
    ·
      refine ⟨77743067129860992517616309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51828711419907328345077539 77743067129860992517616309)
      ·
        refine ⟨7288412543424468048526529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 77743067129860992517616309 7288412543424468048526529)
        ·
          refine ⟨5466309407568351036394897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7288412543424468048526529 5466309407568351036394897)
          ·
            refine ⟨4099732055676263277296173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5466309407568351036394897 4099732055676263277296173)
            ·
              refine ⟨1537399520878598728986065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4099732055676263277296173 1537399520878598728986065)
              ·
                refine ⟨1153049640658949046739549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1537399520878598728986065 1153049640658949046739549)
                ·
                  refine ⟨432393615247105892527331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1153049640658949046739549 432393615247105892527331)
                  ·
                    rfl

theorem cell21_1894688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 3, 2, 3].length) (baseStart_1894688 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1894688 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1894688 prefixEnd_1894688 := by exact prefixLift 1894688
  have htrace : WordTrace (prefixWord ++ tailWord_1894688) baseStart_1894688 baseEnd_1894688 := by
    simpa [prefixWord, tailWord_1894688, baseEnd_1894688] using wordTrace_append hprefix tailTrace_1894688
  have hstable : (prefixWord ++ tailWord_1894688).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1894688).length < 2 ^ (prefixWord ++ tailWord_1894688).sum := by decide
  have hdescent : baseEnd_1894688 < baseStart_1894688 := by decide
  rcases family_descends (prefixWord ++ tailWord_1894688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1894820 : List Nat := [2, 3, 1, 2, 1, 1, 2, 5, 4]
def baseStart_1894820 : Nat := 118140960795 + 1894820 * 2 ^ 59
def prefixEnd_1894820 : Nat := 4983230072969 + 3 ^ 40 * 1894820 * 2
def baseEnd_1894820 : Nat := 432423739445502996327061

theorem tailTrace_1894820 : CollatzResearch.WordTrace tailWord_1894820 prefixEnd_1894820 432423739445502996327061 := by
  unfold tailWord_1894820
  simp only [CollatzResearch.WordTrace]
  refine ⟨34554881497699112168620957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46073175330265482891494609 34554881497699112168620957)
  ·
    refine ⟨12958080561637167063232859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34554881497699112168620957 12958080561637167063232859)
    ·
      refine ⟨19437120842455750594849289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12958080561637167063232859 19437120842455750594849289)
      ·
        refine ⟨14577840631841812946136967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19437120842455750594849289 14577840631841812946136967)
        ·
          refine ⟨21866760947762719419205451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14577840631841812946136967 21866760947762719419205451)
          ·
            refine ⟨32800141421644079128808177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21866760947762719419205451 32800141421644079128808177)
            ·
              refine ⟨24600106066233059346606133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32800141421644079128808177 24600106066233059346606133)
              ·
                refine ⟨2306259943709349313744325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24600106066233059346606133 2306259943709349313744325)
                ·
                  refine ⟨432423739445502996327061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2306259943709349313744325 432423739445502996327061)
                  ·
                    rfl

theorem cell21_1894820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 5, 4].length) (baseStart_1894820 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1894820 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1894820 prefixEnd_1894820 := by exact prefixLift 1894820
  have htrace : WordTrace (prefixWord ++ tailWord_1894820) baseStart_1894820 baseEnd_1894820 := by
    simpa [prefixWord, tailWord_1894820, baseEnd_1894820] using wordTrace_append hprefix tailTrace_1894820
  have hstable : (prefixWord ++ tailWord_1894820).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1894820).length < 2 ^ (prefixWord ++ tailWord_1894820).sum := by decide
  have hdescent : baseEnd_1894820 < baseStart_1894820 := by decide
  rcases family_descends (prefixWord ++ tailWord_1894820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1894834 : List Nat := [3, 2, 1, 1, 1, 1, 5, 7]
def baseStart_1894834 : Nat := 118140960795 + 1894834 * 2 ^ 59
def prefixEnd_1894834 : Nat := 4983230072969 + 3 ^ 40 * 1894834 * 2
def baseEnd_1894834 : Nat := 144142311478747361031233

theorem tailTrace_1894834 : CollatzResearch.WordTrace tailWord_1894834 prefixEnd_1894834 144142311478747361031233 := by
  unfold tailWord_1894834
  simp only [CollatzResearch.WordTrace]
  refine ⟨17277568404336876182062889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46073515744898336485501037 17277568404336876182062889)
  ·
    refine ⟨12958176303252657136547167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17277568404336876182062889 12958176303252657136547167)
    ·
      refine ⟨19437264454878985704820751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12958176303252657136547167 19437264454878985704820751)
      ·
        refine ⟨29155896682318478557231127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19437264454878985704820751 29155896682318478557231127)
        ·
          refine ⟨43733845023477717835846691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29155896682318478557231127 43733845023477717835846691)
          ·
            refine ⟨65600767535216576753770037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43733845023477717835846691 65600767535216576753770037)
            ·
              refine ⟨6150071956426554070665941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65600767535216576753770037 6150071956426554070665941)
              ·
                refine ⟨144142311478747361031233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6150071956426554070665941 144142311478747361031233)
                ·
                  rfl

theorem cell21_1894834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 7].length) (baseStart_1894834 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1894834 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1894834 prefixEnd_1894834 := by exact prefixLift 1894834
  have htrace : WordTrace (prefixWord ++ tailWord_1894834) baseStart_1894834 baseEnd_1894834 := by
    simpa [prefixWord, tailWord_1894834, baseEnd_1894834] using wordTrace_append hprefix tailTrace_1894834
  have hstable : (prefixWord ++ tailWord_1894834).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1894834).length < 2 ^ (prefixWord ++ tailWord_1894834).sum := by decide
  have hdescent : baseEnd_1894834 < baseStart_1894834 := by decide
  rcases family_descends (prefixWord ++ tailWord_1894834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1894910 : List Nat := [4, 2, 2, 13]
def baseStart_1894910 : Nat := 118140960795 + 1894910 * 2 ^ 59
def prefixEnd_1894910 : Nat := 4983230072969 + 3 ^ 40 * 1894910 * 2
def baseEnd_1894910 : Nat := 1779606085068653661839

theorem tailTrace_1894910 : CollatzResearch.WordTrace tailWord_1894910 prefixEnd_1894910 1779606085068653661839 := by
  unfold tailWord_1894910
  simp only [CollatzResearch.WordTrace]
  refine ⟨8639130695634021213502273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46075363710048113138678789 8639130695634021213502273)
  ·
    refine ⟨6479348021725515910126705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8639130695634021213502273 6479348021725515910126705)
    ·
      refine ⟨4859511016294136932595029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6479348021725515910126705 4859511016294136932595029)
      ·
        refine ⟨1779606085068653661839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 13 4859511016294136932595029 1779606085068653661839)
        ·
          rfl

theorem cell21_1894910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 13].length) (baseStart_1894910 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1894910 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1894910 prefixEnd_1894910 := by exact prefixLift 1894910
  have htrace : WordTrace (prefixWord ++ tailWord_1894910) baseStart_1894910 baseEnd_1894910 := by
    simpa [prefixWord, tailWord_1894910, baseEnd_1894910] using wordTrace_append hprefix tailTrace_1894910
  have hstable : (prefixWord ++ tailWord_1894910).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1894910).length < 2 ^ (prefixWord ++ tailWord_1894910).sum := by decide
  have hdescent : baseEnd_1894910 < baseStart_1894910 := by decide
  rcases family_descends (prefixWord ++ tailWord_1894910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1894913 : List Nat := [1, 2, 4, 1, 3, 2, 2, 2, 4]
def baseStart_1894913 : Nat := 118140960795 + 1894913 * 2 ^ 59
def prefixEnd_1894913 : Nat := 4983230072969 + 3 ^ 40 * 1894913 * 2
def baseEnd_1894913 : Nat := 432444963312555501276871

theorem tailTrace_1894913 : CollatzResearch.WordTrace tailWord_1894913 prefixEnd_1894913 432444963312555501276871 := by
  unfold tailWord_1894913
  simp only [CollatzResearch.WordTrace]
  refine ⟨69113154984061301220377393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46075436656040867480251595 69113154984061301220377393)
  ·
    refine ⟨51834866238045975915283045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69113154984061301220377393 51834866238045975915283045)
    ·
      refine ⟨9719037419633620484115571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51834866238045975915283045 9719037419633620484115571)
      ·
        refine ⟨14578556129450430726173357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9719037419633620484115571 14578556129450430726173357)
        ·
          refine ⟨5466958548543911522315009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14578556129450430726173357 5466958548543911522315009)
          ·
            refine ⟨4100218911407933641736257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5466958548543911522315009 4100218911407933641736257)
            ·
              refine ⟨3075164183555950231302193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4100218911407933641736257 3075164183555950231302193)
              ·
                refine ⟨2306373137666962673476645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3075164183555950231302193 2306373137666962673476645)
                ·
                  refine ⟨432444963312555501276871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2306373137666962673476645 432444963312555501276871)
                  ·
                    rfl

theorem cell21_1894913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 2, 2, 4].length) (baseStart_1894913 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1894913 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1894913 prefixEnd_1894913 := by exact prefixLift 1894913
  have htrace : WordTrace (prefixWord ++ tailWord_1894913) baseStart_1894913 baseEnd_1894913 := by
    simpa [prefixWord, tailWord_1894913, baseEnd_1894913] using wordTrace_append hprefix tailTrace_1894913
  have hstable : (prefixWord ++ tailWord_1894913).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1894913).length < 2 ^ (prefixWord ++ tailWord_1894913).sum := by decide
  have hdescent : baseEnd_1894913 < baseStart_1894913 := by decide
  rcases family_descends (prefixWord ++ tailWord_1894913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1894916 : List Nat := [2, 3, 2, 3, 1, 1, 4, 2, 3]
def baseStart_1894916 : Nat := 118140960795 + 1894916 * 2 ^ 59
def prefixEnd_1894916 : Nat := 4983230072969 + 3 ^ 40 * 1894916 * 2
def baseEnd_1894916 : Nat := 432445647953428162726865

theorem tailTrace_1894916 : CollatzResearch.WordTrace tailWord_1894916 prefixEnd_1894916 432445647953428162726865 := by
  unfold tailWord_1894916
  simp only [CollatzResearch.WordTrace]
  refine ⟨34556632201525216366368301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46075509602033621821824401 34556632201525216366368301)
  ·
    refine ⟨12958737075571956137388113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34556632201525216366368301 12958737075571956137388113)
    ·
      refine ⟨9719052806678967103041085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12958737075571956137388113 9719052806678967103041085)
      ·
        refine ⟨3644644802504612663640407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9719052806678967103041085 3644644802504612663640407)
        ·
          refine ⟨5466967203756918995460611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3644644802504612663640407 5466967203756918995460611)
          ·
            refine ⟨8200450805635378493190917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5466967203756918995460611 8200450805635378493190917)
            ·
              refine ⟨1537584526056633467473297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8200450805635378493190917 1537584526056633467473297)
              ·
                refine ⟨1153188394542475100604973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1537584526056633467473297 1153188394542475100604973)
                ·
                  refine ⟨432445647953428162726865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1153188394542475100604973 432445647953428162726865)
                  ·
                    rfl

theorem cell21_1894916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 4, 2, 3].length) (baseStart_1894916 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1894916 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1894916 prefixEnd_1894916 := by exact prefixLift 1894916
  have htrace : WordTrace (prefixWord ++ tailWord_1894916) baseStart_1894916 baseEnd_1894916 := by
    simpa [prefixWord, tailWord_1894916, baseEnd_1894916] using wordTrace_append hprefix tailTrace_1894916
  have hstable : (prefixWord ++ tailWord_1894916).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1894916).length < 2 ^ (prefixWord ++ tailWord_1894916).sum := by decide
  have hdescent : baseEnd_1894916 < baseStart_1894916 := by decide
  rcases family_descends (prefixWord ++ tailWord_1894916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1894941 : List Nat := [1, 4, 2, 2, 1, 2, 1, 1, 7]
def baseStart_1894941 : Nat := 118140960795 + 1894941 * 2 ^ 59
def prefixEnd_1894941 : Nat := 4983230072969 + 3 ^ 40 * 1894941 * 2
def baseEnd_1894941 : Nat := 432451353294033674810147

theorem tailTrace_1894941 : CollatzResearch.WordTrace tailWord_1894941 prefixEnd_1894941 432451353294033674810147 := by
  unfold tailWord_1894941
  simp only [CollatzResearch.WordTrace]
  refine ⟨69114176227959862002396677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46076117485306574668264451 69114176227959862002396677)
  ·
    refine ⟨12958908042742474125449377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69114176227959862002396677 12958908042742474125449377)
    ·
      refine ⟨9719181032056855594087033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12958908042742474125449377 9719181032056855594087033)
      ·
        refine ⟨7289385774042641695565275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9719181032056855594087033 7289385774042641695565275)
        ·
          refine ⟨10934078661063962543347913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7289385774042641695565275 10934078661063962543347913)
          ·
            refine ⟨8200558995797971907510935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10934078661063962543347913 8200558995797971907510935)
            ·
              refine ⟨12300838493696957861266403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8200558995797971907510935 12300838493696957861266403)
              ·
                refine ⟨18451257740545436791899605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12300838493696957861266403 18451257740545436791899605)
                ·
                  refine ⟨432451353294033674810147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18451257740545436791899605 432451353294033674810147)
                  ·
                    rfl

theorem cell21_1894941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 1, 7].length) (baseStart_1894941 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1894941 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1894941 prefixEnd_1894941 := by exact prefixLift 1894941
  have htrace : WordTrace (prefixWord ++ tailWord_1894941) baseStart_1894941 baseEnd_1894941 := by
    simpa [prefixWord, tailWord_1894941, baseEnd_1894941] using wordTrace_append hprefix tailTrace_1894941
  have hstable : (prefixWord ++ tailWord_1894941).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1894941).length < 2 ^ (prefixWord ++ tailWord_1894941).sum := by decide
  have hdescent : baseEnd_1894941 < baseStart_1894941 := by decide
  rcases family_descends (prefixWord ++ tailWord_1894941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1894944 : List Nat := [2, 1, 1, 6, 2, 1, 3, 5]
def baseStart_1894944 : Nat := 118140960795 + 1894944 * 2 ^ 59
def prefixEnd_1894944 : Nat := 4983230072969 + 3 ^ 40 * 1894944 * 2
def baseEnd_1894944 : Nat := 144150679311635445420047

theorem tailTrace_1894944 : CollatzResearch.WordTrace tailWord_1894944 prefixEnd_1894944 144150679311635445420047 := by
  unfold tailWord_1894944
  simp only [CollatzResearch.WordTrace]
  refine ⟨34557142823474496757377943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46076190431299329009837257 34557142823474496757377943)
  ·
    refine ⟨51835714235211745136066915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34557142823474496757377943 51835714235211745136066915)
    ·
      refine ⟨77753571352817617704100373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51835714235211745136066915 77753571352817617704100373)
      ·
        refine ⟨3644698657163325829879705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 77753571352817617704100373 3644698657163325829879705)
        ·
          refine ⟨2733523992872494372409779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3644698657163325829879705 2733523992872494372409779)
          ·
            refine ⟨4100285989308741558614669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2733523992872494372409779 4100285989308741558614669)
            ·
              refine ⟨1537607245990778084480501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4100285989308741558614669 1537607245990778084480501)
              ·
                refine ⟨144150679311635445420047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1537607245990778084480501 144150679311635445420047)
                ·
                  rfl

theorem cell21_1894944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 3, 5].length) (baseStart_1894944 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1894944 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1894944 prefixEnd_1894944 := by exact prefixLift 1894944
  have htrace : WordTrace (prefixWord ++ tailWord_1894944) baseStart_1894944 baseEnd_1894944 := by
    simpa [prefixWord, tailWord_1894944, baseEnd_1894944] using wordTrace_append hprefix tailTrace_1894944
  have hstable : (prefixWord ++ tailWord_1894944).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1894944).length < 2 ^ (prefixWord ++ tailWord_1894944).sum := by decide
  have hdescent : baseEnd_1894944 < baseStart_1894944 := by decide
  rcases family_descends (prefixWord ++ tailWord_1894944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1894964 : List Nat := [2, 5, 1, 3, 2, 1, 1, 2, 4]
def baseStart_1894964 : Nat := 118140960795 + 1894964 * 2 ^ 59
def prefixEnd_1894964 : Nat := 4983230072969 + 3 ^ 40 * 1894964 * 2
def baseEnd_1894964 : Nat := 432456602207390745926767

theorem tailTrace_1894964 : CollatzResearch.WordTrace tailWord_1894964 prefixEnd_1894964 432456602207390745926767 := by
  unfold tailWord_1894964
  simp only [CollatzResearch.WordTrace]
  refine ⟨34557507553438268465241973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46076676737917691286989297 34557507553438268465241973)
  ·
    refine ⟨3239766333134837668616435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34557507553438268465241973 3239766333134837668616435)
    ·
      refine ⟨4859649499702256502924653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3239766333134837668616435 4859649499702256502924653)
      ·
        refine ⟨1822368562388346188596745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4859649499702256502924653 1822368562388346188596745)
        ·
          refine ⟨1366776421791259641447559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1822368562388346188596745 1366776421791259641447559)
          ·
            refine ⟨2050164632686889462171339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1366776421791259641447559 2050164632686889462171339)
            ·
              refine ⟨3075246949030334193257009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2050164632686889462171339 3075246949030334193257009)
              ·
                refine ⟨2306435211772750644942757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3075246949030334193257009 2306435211772750644942757)
                ·
                  refine ⟨432456602207390745926767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2306435211772750644942757 432456602207390745926767)
                  ·
                    rfl

theorem cell21_1894964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 1, 2, 4].length) (baseStart_1894964 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1894964 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1894964 prefixEnd_1894964 := by exact prefixLift 1894964
  have htrace : WordTrace (prefixWord ++ tailWord_1894964) baseStart_1894964 baseEnd_1894964 := by
    simpa [prefixWord, tailWord_1894964, baseEnd_1894964] using wordTrace_append hprefix tailTrace_1894964
  have hstable : (prefixWord ++ tailWord_1894964).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1894964).length < 2 ^ (prefixWord ++ tailWord_1894964).sum := by decide
  have hdescent : baseEnd_1894964 < baseStart_1894964 := by decide
  rcases family_descends (prefixWord ++ tailWord_1894964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1894972 : List Nat := [2, 2, 2, 2, 3, 2, 1, 1, 6]
def baseStart_1894972 : Nat := 118140960795 + 1894972 * 2 ^ 59
def prefixEnd_1894972 : Nat := 4983230072969 + 3 ^ 40 * 1894972 * 2
def baseEnd_1894972 : Nat := 432458427916384509793417

theorem tailTrace_1894972 : CollatzResearch.WordTrace tailWord_1894972 prefixEnd_1894972 432458427916384509793417 := by
  unfold tailWord_1894972
  simp only [CollatzResearch.WordTrace]
  refine ⟨34557653445423777148387585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46076871260565036197850113 34557653445423777148387585)
  ·
    refine ⟨25918240084067832861290689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34557653445423777148387585 25918240084067832861290689)
    ·
      refine ⟨19438680063050874645968017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25918240084067832861290689 19438680063050874645968017)
      ·
        refine ⟨14579010047288155984476013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19438680063050874645968017 14579010047288155984476013)
        ·
          refine ⟨5467128767733058494178505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14579010047288155984476013 5467128767733058494178505)
          ·
            refine ⟨4100346575799793870633879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5467128767733058494178505 4100346575799793870633879)
            ·
              refine ⟨6150519863699690805950819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4100346575799793870633879 6150519863699690805950819)
              ·
                refine ⟨9225779795549536208926229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6150519863699690805950819 9225779795549536208926229)
                ·
                  refine ⟨432458427916384509793417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9225779795549536208926229 432458427916384509793417)
                  ·
                    rfl

theorem cell21_1894972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 1, 6].length) (baseStart_1894972 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1894972 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1894972 prefixEnd_1894972 := by exact prefixLift 1894972
  have htrace : WordTrace (prefixWord ++ tailWord_1894972) baseStart_1894972 baseEnd_1894972 := by
    simpa [prefixWord, tailWord_1894972, baseEnd_1894972] using wordTrace_append hprefix tailTrace_1894972
  have hstable : (prefixWord ++ tailWord_1894972).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1894972).length < 2 ^ (prefixWord ++ tailWord_1894972).sum := by decide
  have hdescent : baseEnd_1894972 < baseStart_1894972 := by decide
  rcases family_descends (prefixWord ++ tailWord_1894972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1895031 : List Nat := [1, 1, 3, 1, 1, 3, 4, 1, 6]
def baseStart_1895031 : Nat := 118140960795 + 1895031 * 2 ^ 59
def prefixEnd_1895031 : Nat := 4983230072969 + 3 ^ 40 * 1895031 * 2
def baseEnd_1895031 : Nat := 432471892520213518309963

theorem tailTrace_1895031 : CollatzResearch.WordTrace tailWord_1895031 prefixEnd_1895031 432471892520213518309963 := by
  unfold tailWord_1895031
  simp only [CollatzResearch.WordTrace]
  refine ⟨69117458797633807373172947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46078305865089204915448631 69117458797633807373172947)
  ·
    refine ⟨103676188196450711059759421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69117458797633807373172947 103676188196450711059759421)
    ·
      refine ⟨38878570573669016647409783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103676188196450711059759421 38878570573669016647409783)
      ·
        refine ⟨58317855860503524971114675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38878570573669016647409783 58317855860503524971114675)
        ·
          refine ⟨87476783790755287456672013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58317855860503524971114675 87476783790755287456672013)
          ·
            refine ⟨32803793921533232796252005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87476783790755287456672013 32803793921533232796252005)
            ·
              refine ⟨6150711360287481149297251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32803793921533232796252005 6150711360287481149297251)
              ·
                refine ⟨9226067040431221723945877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6150711360287481149297251 9226067040431221723945877)
                ·
                  refine ⟨432471892520213518309963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9226067040431221723945877 432471892520213518309963)
                  ·
                    rfl

theorem cell21_1895031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 1, 6].length) (baseStart_1895031 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1895031 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1895031 prefixEnd_1895031 := by exact prefixLift 1895031
  have htrace : WordTrace (prefixWord ++ tailWord_1895031) baseStart_1895031 baseEnd_1895031 := by
    simpa [prefixWord, tailWord_1895031, baseEnd_1895031] using wordTrace_append hprefix tailTrace_1895031
  have hstable : (prefixWord ++ tailWord_1895031).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1895031).length < 2 ^ (prefixWord ++ tailWord_1895031).sum := by decide
  have hdescent : baseEnd_1895031 < baseStart_1895031 := by decide
  rcases family_descends (prefixWord ++ tailWord_1895031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1895079 : List Nat := [1, 1, 6, 3, 1, 9]
def baseStart_1895079 : Nat := 118140960795 + 1895079 * 2 ^ 59
def prefixEnd_1895079 : Nat := 4983230072969 + 3 ^ 40 * 1895079 * 2
def baseEnd_1895079 : Nat := 16017883213858374129995

theorem tailTrace_1895079 : CollatzResearch.WordTrace tailWord_1895079 prefixEnd_1895079 16017883213858374129995 := by
  unfold tailWord_1895079
  simp only [CollatzResearch.WordTrace]
  refine ⟨69119209501459911570920291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46079473000973274380613527 69119209501459911570920291)
  ·
    refine ⟨103678814252189867356380437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69119209501459911570920291 103678814252189867356380437)
    ·
      refine ⟨4859944418071400032330333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 103678814252189867356380437 4859944418071400032330333)
      ·
        refine ⟨1822479156776775012123875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4859944418071400032330333 1822479156776775012123875)
        ·
          refine ⟨2733718735165162518185813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1822479156776775012123875 2733718735165162518185813)
          ·
            refine ⟨16017883213858374129995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2733718735165162518185813 16017883213858374129995)
            ·
              rfl

theorem cell21_1895079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 9].length) (baseStart_1895079 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1895079 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1895079 prefixEnd_1895079 := by exact prefixLift 1895079
  have htrace : WordTrace (prefixWord ++ tailWord_1895079) baseStart_1895079 baseEnd_1895079 := by
    simpa [prefixWord, tailWord_1895079, baseEnd_1895079] using wordTrace_append hprefix tailTrace_1895079
  have hstable : (prefixWord ++ tailWord_1895079).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1895079).length < 2 ^ (prefixWord ++ tailWord_1895079).sum := by decide
  have hdescent : baseEnd_1895079 < baseStart_1895079 := by decide
  rcases family_descends (prefixWord ++ tailWord_1895079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1895141 : List Nat := [1, 3, 1, 4, 1, 4, 1, 2, 4]
def baseStart_1895141 : Nat := 118140960795 + 1895141 * 2 ^ 59
def prefixEnd_1895141 : Nat := 4983230072969 + 3 ^ 40 * 1895141 * 2
def baseEnd_1895141 : Nat := 432496996018877771476405

theorem tailTrace_1895141 : CollatzResearch.WordTrace tailWord_1895141 prefixEnd_1895141 432496996018877771476405 := by
  unfold tailWord_1895141
  simp only [CollatzResearch.WordTrace]
  refine ⟨69121470827235296159677277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46080980551490197439784851 69121470827235296159677277)
  ·
    refine ⟨25920551560213236059878979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69121470827235296159677277 25920551560213236059878979)
    ·
      refine ⟨38880827340319854089818469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25920551560213236059878979 38880827340319854089818469)
      ·
        refine ⟨7290155126309972641840963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38880827340319854089818469 7290155126309972641840963)
        ·
          refine ⟨10935232689464958962761445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7290155126309972641840963 10935232689464958962761445)
          ·
            refine ⟨2050356129274679805517771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10935232689464958962761445 2050356129274679805517771)
            ·
              refine ⟨3075534193912019708276657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2050356129274679805517771 3075534193912019708276657)
              ·
                refine ⟨2306650645434014781207493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3075534193912019708276657 2306650645434014781207493)
                ·
                  refine ⟨432496996018877771476405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2306650645434014781207493 432496996018877771476405)
                  ·
                    rfl

theorem cell21_1895141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 1, 2, 4].length) (baseStart_1895141 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1895141 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1895141 prefixEnd_1895141 := by exact prefixLift 1895141
  have htrace : WordTrace (prefixWord ++ tailWord_1895141) baseStart_1895141 baseEnd_1895141 := by
    simpa [prefixWord, tailWord_1895141, baseEnd_1895141] using wordTrace_append hprefix tailTrace_1895141
  have hstable : (prefixWord ++ tailWord_1895141).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1895141).length < 2 ^ (prefixWord ++ tailWord_1895141).sum := by decide
  have hdescent : baseEnd_1895141 < baseStart_1895141 := by decide
  rcases family_descends (prefixWord ++ tailWord_1895141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1895228 : List Nat := [2, 2, 2, 2, 1, 1, 1, 3, 7]
def baseStart_1895228 : Nat := 118140960795 + 1895228 * 2 ^ 59
def prefixEnd_1895228 : Nat := 4983230072969 + 3 ^ 40 * 1895228 * 2
def baseEnd_1895228 : Nat := 432516850604184953526227

theorem tailTrace_1895228 : CollatzResearch.WordTrace tailWord_1895228 prefixEnd_1895228 432516850604184953526227 := by
  unfold tailWord_1895228
  simp only [CollatzResearch.WordTrace]
  refine ⟨34562321988960055009047169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46083095985280073345396225 34562321988960055009047169)
  ·
    refine ⟨25921741491720041256785377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34562321988960055009047169 25921741491720041256785377)
    ·
      refine ⟨19441306118790030942589033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25921741491720041256785377 19441306118790030942589033)
      ·
        refine ⟨14580979589092523206941775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19441306118790030942589033 14580979589092523206941775)
        ·
          refine ⟨21871469383638784810412663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14580979589092523206941775 21871469383638784810412663)
          ·
            refine ⟨32807204075458177215618995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21871469383638784810412663 32807204075458177215618995)
            ·
              refine ⟨49210806113187265823428493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32807204075458177215618995 49210806113187265823428493)
              ·
                refine ⟨18454052292445224683785685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49210806113187265823428493 18454052292445224683785685)
                ·
                  refine ⟨432516850604184953526227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18454052292445224683785685 432516850604184953526227)
                  ·
                    rfl

theorem cell21_1895228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 3, 7].length) (baseStart_1895228 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1895228 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1895228 prefixEnd_1895228 := by exact prefixLift 1895228
  have htrace : WordTrace (prefixWord ++ tailWord_1895228) baseStart_1895228 baseEnd_1895228 := by
    simpa [prefixWord, tailWord_1895228, baseEnd_1895228] using wordTrace_append hprefix tailTrace_1895228
  have hstable : (prefixWord ++ tailWord_1895228).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1895228).length < 2 ^ (prefixWord ++ tailWord_1895228).sum := by decide
  have hdescent : baseEnd_1895228 < baseStart_1895228 := by decide
  rcases family_descends (prefixWord ++ tailWord_1895228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1895341 : List Nat := [1, 5, 2, 3, 1, 2, 2, 5]
def baseStart_1895341 : Nat := 118140960795 + 1895341 * 2 ^ 59
def prefixEnd_1895341 : Nat := 4983230072969 + 3 ^ 40 * 1895341 * 2
def baseEnd_1895341 : Nat := 144180879581240622714221

theorem tailTrace_1895341 : CollatzResearch.WordTrace tailWord_1895341 prefixEnd_1895341 144180879581240622714221 := by
  unfold tailWord_1895341
  simp only [CollatzResearch.WordTrace]
  refine ⟨69128765426510730316957877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46085843617673820211305251 69128765426510730316957877)
  ·
    refine ⟨6480821758735380967214801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 69128765426510730316957877 6480821758735380967214801)
    ·
      refine ⟨4860616319051535725411101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6480821758735380967214801 4860616319051535725411101)
      ·
        refine ⟨1822731119644325897029163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4860616319051535725411101 1822731119644325897029163)
        ·
          refine ⟨2734096679466488845543745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1822731119644325897029163 2734096679466488845543745)
          ·
            refine ⟨2050572509599866634157809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2734096679466488845543745 2050572509599866634157809)
            ·
              refine ⟨1537929382199899975618357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2050572509599866634157809 1537929382199899975618357)
              ·
                refine ⟨144180879581240622714221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1537929382199899975618357 144180879581240622714221)
                ·
                  rfl

theorem cell21_1895341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 2, 5].length) (baseStart_1895341 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1895341 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1895341 prefixEnd_1895341 := by exact prefixLift 1895341
  have htrace : WordTrace (prefixWord ++ tailWord_1895341) baseStart_1895341 baseEnd_1895341 := by
    simpa [prefixWord, tailWord_1895341, baseEnd_1895341] using wordTrace_append hprefix tailTrace_1895341
  have hstable : (prefixWord ++ tailWord_1895341).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1895341).length < 2 ^ (prefixWord ++ tailWord_1895341).sum := by decide
  have hdescent : baseEnd_1895341 < baseStart_1895341 := by decide
  rcases family_descends (prefixWord ++ tailWord_1895341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1895425 : List Nat := [1, 2, 4, 1, 2, 11]
def baseStart_1895425 : Nat := 118140960795 + 1895425 * 2 ^ 59
def prefixEnd_1895425 : Nat := 4983230072969 + 3 ^ 40 * 1895425 * 2
def baseEnd_1895425 : Nat := 16020807729190977360833

theorem tailTrace_1895425 : CollatzResearch.WordTrace tailWord_1895425 prefixEnd_1895425 16020807729190977360833 := by
  unfold tailWord_1895425
  simp only [CollatzResearch.WordTrace]
  refine ⟨69131829158206412663015729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46087886105470941775343819 69131829158206412663015729)
  ·
    refine ⟨51848871868654809497261797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69131829158206412663015729 51848871868654809497261797)
    ·
      refine ⟨9721663475372776780736587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51848871868654809497261797 9721663475372776780736587)
      ·
        refine ⟨14582495213059165171104881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9721663475372776780736587 14582495213059165171104881)
        ·
          refine ⟨10936871409794373878328661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14582495213059165171104881 10936871409794373878328661)
          ·
            refine ⟨16020807729190977360833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 10936871409794373878328661 16020807729190977360833)
            ·
              rfl

theorem cell21_1895425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 11].length) (baseStart_1895425 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1895425 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1895425 prefixEnd_1895425 := by exact prefixLift 1895425
  have htrace : WordTrace (prefixWord ++ tailWord_1895425) baseStart_1895425 baseEnd_1895425 := by
    simpa [prefixWord, tailWord_1895425, baseEnd_1895425] using wordTrace_append hprefix tailTrace_1895425
  have hstable : (prefixWord ++ tailWord_1895425).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1895425).length < 2 ^ (prefixWord ++ tailWord_1895425).sum := by decide
  have hdescent : baseEnd_1895425 < baseStart_1895425 := by decide
  rcases family_descends (prefixWord ++ tailWord_1895425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1895510 : List Nat := [5, 2, 2, 1, 3, 1, 2, 5]
def baseStart_1895510 : Nat := 118140960795 + 1895510 * 2 ^ 59
def prefixEnd_1895510 : Nat := 4983230072969 + 3 ^ 40 * 1895510 * 2
def baseEnd_1895510 : Nat := 144193735615405043275217

theorem tailTrace_1895510 : CollatzResearch.WordTrace tailWord_1895510 prefixEnd_1895510 144193735615405043275217 := by
  unfold tailWord_1895510
  simp only [CollatzResearch.WordTrace]
  refine ⟨4320933085181154511241249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46089952908598981453239989 4320933085181154511241249)
  ·
    refine ⟨3240699813885865883430937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4320933085181154511241249 3240699813885865883430937)
    ·
      refine ⟨2430524860414399412573203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3240699813885865883430937 2430524860414399412573203)
      ·
        refine ⟨3645787290621599118859805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2430524860414399412573203 3645787290621599118859805)
        ·
          refine ⟨1367170233983099669572427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3645787290621599118859805 1367170233983099669572427)
          ·
            refine ⟨2050755350974649504358641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1367170233983099669572427 2050755350974649504358641)
            ·
              refine ⟨1538066513230987128268981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2050755350974649504358641 1538066513230987128268981)
              ·
                refine ⟨144193735615405043275217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1538066513230987128268981 144193735615405043275217)
                ·
                  rfl

theorem cell21_1895510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 2, 5].length) (baseStart_1895510 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1895510 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1895510 prefixEnd_1895510 := by exact prefixLift 1895510
  have htrace : WordTrace (prefixWord ++ tailWord_1895510) baseStart_1895510 baseEnd_1895510 := by
    simpa [prefixWord, tailWord_1895510, baseEnd_1895510] using wordTrace_append hprefix tailTrace_1895510
  have hstable : (prefixWord ++ tailWord_1895510).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1895510).length < 2 ^ (prefixWord ++ tailWord_1895510).sum := by decide
  have hdescent : baseEnd_1895510 < baseStart_1895510 := by decide
  rcases family_descends (prefixWord ++ tailWord_1895510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1895594 : List Nat := [3, 1, 5, 1, 1, 10]
def baseStart_1895594 : Nat := 118140960795 + 1895594 * 2 ^ 59
def prefixEnd_1895594 : Nat := 4983230072969 + 3 ^ 40 * 1895594 * 2
def baseEnd_1895594 : Nat := 16022236177431468534277

theorem tailTrace_1895594 : CollatzResearch.WordTrace tailWord_1895594 prefixEnd_1895594 16022236177431468534277 := by
  unfold tailWord_1895594
  simp only [CollatzResearch.WordTrace]
  refine ⟨17284498273648538631479459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46091995396396103017278557 17284498273648538631479459)
  ·
    refine ⟨25926747410472807947219189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17284498273648538631479459 25926747410472807947219189)
    ·
      refine ⟨2430632569731825745051799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25926747410472807947219189 2430632569731825745051799)
      ·
        refine ⟨3645948854597738617577699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2430632569731825745051799 3645948854597738617577699)
        ·
          refine ⟨5468923281896607926366549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3645948854597738617577699 5468923281896607926366549)
          ·
            refine ⟨16022236177431468534277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5468923281896607926366549 16022236177431468534277)
            ·
              rfl

theorem cell21_1895594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 10].length) (baseStart_1895594 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1895594 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1895594 prefixEnd_1895594 := by exact prefixLift 1895594
  have htrace : WordTrace (prefixWord ++ tailWord_1895594) baseStart_1895594 baseEnd_1895594 := by
    simpa [prefixWord, tailWord_1895594, baseEnd_1895594] using wordTrace_append hprefix tailTrace_1895594
  have hstable : (prefixWord ++ tailWord_1895594).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1895594).length < 2 ^ (prefixWord ++ tailWord_1895594).sum := by decide
  have hdescent : baseEnd_1895594 < baseStart_1895594 := by decide
  rcases family_descends (prefixWord ++ tailWord_1895594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1895597 : List Nat := [1, 5, 2, 1, 3, 1, 2, 2, 4]
def baseStart_1895597 : Nat := 118140960795 + 1895597 * 2 ^ 59
def prefixEnd_1895597 : Nat := 4983230072969 + 3 ^ 40 * 1895597 * 2
def baseEnd_1895597 : Nat := 432601061431522311875473

theorem tailTrace_1895597 : CollatzResearch.WordTrace tailWord_1895597 prefixEnd_1895597 432601061431522311875473 := by
  unfold tailWord_1895597
  simp only [CollatzResearch.WordTrace]
  refine ⟨69138102513583286038277045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46092068342388857358851363 69138102513583286038277045)
  ·
    refine ⟨6481697110648433066088473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 69138102513583286038277045 6481697110648433066088473)
    ·
      refine ⟨4861272832986324799566355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6481697110648433066088473 4861272832986324799566355)
      ·
        refine ⟨7291909249479487199349533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4861272832986324799566355 7291909249479487199349533)
        ·
          refine ⟨2734465968554807699756075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7291909249479487199349533 2734465968554807699756075)
          ·
            refine ⟨4101698952832211549634113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2734465968554807699756075 4101698952832211549634113)
            ·
              refine ⟨3076274214624158662225585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4101698952832211549634113 3076274214624158662225585)
              ·
                refine ⟨2307205660968118996669189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3076274214624158662225585 2307205660968118996669189)
                ·
                  refine ⟨432601061431522311875473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2307205660968118996669189 432601061431522311875473)
                  ·
                    rfl

theorem cell21_1895597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 2, 2, 4].length) (baseStart_1895597 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1895597 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1895597 prefixEnd_1895597 := by exact prefixLift 1895597
  have htrace : WordTrace (prefixWord ++ tailWord_1895597) baseStart_1895597 baseEnd_1895597 := by
    simpa [prefixWord, tailWord_1895597, baseEnd_1895597] using wordTrace_append hprefix tailTrace_1895597
  have hstable : (prefixWord ++ tailWord_1895597).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1895597).length < 2 ^ (prefixWord ++ tailWord_1895597).sum := by decide
  have hdescent : baseEnd_1895597 < baseStart_1895597 := by decide
  rcases family_descends (prefixWord ++ tailWord_1895597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1895729 : List Nat := [1, 2, 2, 3, 3, 1, 1, 8]
def baseStart_1895729 : Nat := 118140960795 + 1895729 * 2 ^ 59
def prefixEnd_1895729 : Nat := 4983230072969 + 3 ^ 40 * 1895729 * 2
def baseEnd_1895729 : Nat := 144210395209973138558401

theorem tailTrace_1895729 : CollatzResearch.WordTrace tailWord_1895729 prefixEnd_1895729 144210395209973138558401 := by
  unfold tailWord_1895729
  simp only [CollatzResearch.WordTrace]
  refine ⟨69142916949105072582082241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46095277966070048388054827 69142916949105072582082241)
  ·
    refine ⟨51857187711828804436561681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69142916949105072582082241 51857187711828804436561681)
    ·
      refine ⟨38892890783871603327421261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51857187711828804436561681 38892890783871603327421261)
      ·
        refine ⟨14584834043951851247782973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38892890783871603327421261 14584834043951851247782973)
        ·
          refine ⟨5469312766481944217918615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14584834043951851247782973 5469312766481944217918615)
          ·
            refine ⟨8203969149722916326877923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5469312766481944217918615 8203969149722916326877923)
            ·
              refine ⟨12305953724584374490316885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8203969149722916326877923 12305953724584374490316885)
              ·
                refine ⟨144210395209973138558401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12305953724584374490316885 144210395209973138558401)
                ·
                  rfl

theorem cell21_1895729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 8].length) (baseStart_1895729 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1895729 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1895729 prefixEnd_1895729 := by exact prefixLift 1895729
  have htrace : WordTrace (prefixWord ++ tailWord_1895729) baseStart_1895729 baseEnd_1895729 := by
    simpa [prefixWord, tailWord_1895729, baseEnd_1895729] using wordTrace_append hprefix tailTrace_1895729
  have hstable : (prefixWord ++ tailWord_1895729).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1895729).length < 2 ^ (prefixWord ++ tailWord_1895729).sum := by decide
  have hdescent : baseEnd_1895729 < baseStart_1895729 := by decide
  rcases family_descends (prefixWord ++ tailWord_1895729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1895732 : List Nat := [2, 5, 1, 1, 1, 1, 3, 3, 4]
def baseStart_1895732 : Nat := 118140960795 + 1895732 * 2 ^ 59
def prefixEnd_1895732 : Nat := 4983230072969 + 3 ^ 40 * 1895732 * 2
def baseEnd_1895732 : Nat := 432631870270792077125197

theorem tailTrace_1895732 : CollatzResearch.WordTrace tailWord_1895732 prefixEnd_1895732 432631870270792077125197 := by
  unfold tailWord_1895732
  simp only [CollatzResearch.WordTrace]
  refine ⟨34571513184047102047220725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46095350912062802729627633 34571513184047102047220725)
  ·
    refine ⟨3241079361004415816926943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34571513184047102047220725 3241079361004415816926943)
    ·
      refine ⟨4861619041506623725390415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3241079361004415816926943 4861619041506623725390415)
      ·
        refine ⟨7292428562259935588085623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4861619041506623725390415 7292428562259935588085623)
        ·
          refine ⟨10938642843389903382128435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7292428562259935588085623 10938642843389903382128435)
          ·
            refine ⟨16407964265084855073192653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10938642843389903382128435 16407964265084855073192653)
            ·
              refine ⟨6152986599406820652447245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16407964265084855073192653 6152986599406820652447245)
              ·
                refine ⟨2307369974777557744667717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6152986599406820652447245 2307369974777557744667717)
                ·
                  refine ⟨432631870270792077125197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2307369974777557744667717 432631870270792077125197)
                  ·
                    rfl

theorem cell21_1895732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_1895732 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1895732 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1895732 prefixEnd_1895732 := by exact prefixLift 1895732
  have htrace : WordTrace (prefixWord ++ tailWord_1895732) baseStart_1895732 baseEnd_1895732 := by
    simpa [prefixWord, tailWord_1895732, baseEnd_1895732] using wordTrace_append hprefix tailTrace_1895732
  have hstable : (prefixWord ++ tailWord_1895732).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1895732).length < 2 ^ (prefixWord ++ tailWord_1895732).sum := by decide
  have hdescent : baseEnd_1895732 < baseStart_1895732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1895732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1895819 : List Nat := [1, 1, 1, 1, 4, 3, 1, 2, 7]
def baseStart_1895819 : Nat := 118140960795 + 1895819 * 2 ^ 59
def prefixEnd_1895819 : Nat := 4983230072969 + 3 ^ 40 * 1895819 * 2
def baseEnd_1895819 : Nat := 432651724856099259175019

theorem tailTrace_1895819 : CollatzResearch.WordTrace tailWord_1895819 prefixEnd_1895819 432651724856099259175019 := by
  unfold tailWord_1895819
  simp only [CollatzResearch.WordTrace]
  refine ⟨69146199518779017952858511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46097466345852678635239007 69146199518779017952858511)
  ·
    refine ⟨103719299278168526929287767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69146199518779017952858511 103719299278168526929287767)
    ·
      refine ⟨155578948917252790393931651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103719299278168526929287767 155578948917252790393931651)
      ·
        refine ⟨233368423375879185590897477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155578948917252790393931651 233368423375879185590897477)
        ·
          refine ⟨43756579382977347298293277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 233368423375879185590897477 43756579382977347298293277)
          ·
            refine ⟨16408717268616505236859979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43756579382977347298293277 16408717268616505236859979)
            ·
              refine ⟨24613075902924757855289969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16408717268616505236859979 24613075902924757855289969)
              ·
                refine ⟨18459806927193568391467477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24613075902924757855289969 18459806927193568391467477)
                ·
                  refine ⟨432651724856099259175019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18459806927193568391467477 432651724856099259175019)
                  ·
                    rfl

theorem cell21_1895819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 2, 7].length) (baseStart_1895819 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1895819 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1895819 prefixEnd_1895819 := by exact prefixLift 1895819
  have htrace : WordTrace (prefixWord ++ tailWord_1895819) baseStart_1895819 baseEnd_1895819 := by
    simpa [prefixWord, tailWord_1895819, baseEnd_1895819] using wordTrace_append hprefix tailTrace_1895819
  have hstable : (prefixWord ++ tailWord_1895819).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1895819).length < 2 ^ (prefixWord ++ tailWord_1895819).sum := by decide
  have hdescent : baseEnd_1895819 < baseStart_1895819 := by decide
  rcases family_descends (prefixWord ++ tailWord_1895819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1895822 : List Nat := [4, 1, 1, 4, 2, 1, 8]
def baseStart_1895822 : Nat := 118140960795 + 1895822 * 2 ^ 59
def prefixEnd_1895822 : Nat := 4983230072969 + 3 ^ 40 * 1895822 * 2
def baseEnd_1895822 : Nat := 48072489944107991180557

theorem tailTrace_1895822 : CollatzResearch.WordTrace tailWord_1895822 prefixEnd_1895822 48072489944107991180557 := by
  unfold tailWord_1895822
  simp only [CollatzResearch.WordTrace]
  refine ⟨8643288617221018683152215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46097539291845432976811813 8643288617221018683152215)
  ·
    refine ⟨12964932925831528024728323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8643288617221018683152215 12964932925831528024728323)
    ·
      refine ⟨19447399388747292037092485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12964932925831528024728323 19447399388747292037092485)
      ·
        refine ⟨3646387385390117256954841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19447399388747292037092485 3646387385390117256954841)
        ·
          refine ⟨2734790539042587942716131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3646387385390117256954841 2734790539042587942716131)
          ·
            refine ⟨4102185808563881914074197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2734790539042587942716131 4102185808563881914074197)
            ·
              refine ⟨48072489944107991180557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4102185808563881914074197 48072489944107991180557)
              ·
                rfl

theorem cell21_1895822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 8].length) (baseStart_1895822 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1895822 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1895822 prefixEnd_1895822 := by exact prefixLift 1895822
  have htrace : WordTrace (prefixWord ++ tailWord_1895822) baseStart_1895822 baseEnd_1895822 := by
    simpa [prefixWord, tailWord_1895822, baseEnd_1895822] using wordTrace_append hprefix tailTrace_1895822
  have hstable : (prefixWord ++ tailWord_1895822).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1895822).length < 2 ^ (prefixWord ++ tailWord_1895822).sum := by decide
  have hdescent : baseEnd_1895822 < baseStart_1895822 := by decide
  rcases family_descends (prefixWord ++ tailWord_1895822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1895853 : List Nat := [1, 5, 2, 2, 1, 1, 2, 2, 5]
def baseStart_1895853 : Nat := 118140960795 + 1895853 * 2 ^ 59
def prefixEnd_1895853 : Nat := 4983230072969 + 3 ^ 40 * 1895853 * 2
def baseEnd_1895853 : Nat := 432659484119322755608283

theorem tailTrace_1895853 : CollatzResearch.WordTrace tailWord_1895853 prefixEnd_1895853 432659484119322755608283 := by
  unfold tailWord_1895853
  simp only [CollatzResearch.WordTrace]
  refine ⟨69147439600655841759596213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46098293067103894506397475 69147439600655841759596213)
  ·
    refine ⟨6482572462561485164962145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 69147439600655841759596213 6482572462561485164962145)
    ·
      refine ⟨4861929346921113873721609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6482572462561485164962145 4861929346921113873721609)
      ·
        refine ⟨3646447010190835405291207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4861929346921113873721609 3646447010190835405291207)
        ·
          refine ⟨5469670515286253107936811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3646447010190835405291207 5469670515286253107936811)
          ·
            refine ⟨8204505772929379661905217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5469670515286253107936811 8204505772929379661905217)
            ·
              refine ⟨6153379329697034746428913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8204505772929379661905217 6153379329697034746428913)
              ·
                refine ⟨4615034497272776059821685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6153379329697034746428913 4615034497272776059821685)
                ·
                  refine ⟨432659484119322755608283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4615034497272776059821685 432659484119322755608283)
                  ·
                    rfl

theorem cell21_1895853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 2, 5].length) (baseStart_1895853 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1895853 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1895853 prefixEnd_1895853 := by exact prefixLift 1895853
  have htrace : WordTrace (prefixWord ++ tailWord_1895853) baseStart_1895853 baseEnd_1895853 := by
    simpa [prefixWord, tailWord_1895853, baseEnd_1895853] using wordTrace_append hprefix tailTrace_1895853
  have hstable : (prefixWord ++ tailWord_1895853).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1895853).length < 2 ^ (prefixWord ++ tailWord_1895853).sum := by decide
  have hdescent : baseEnd_1895853 < baseStart_1895853 := by decide
  rcases family_descends (prefixWord ++ tailWord_1895853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1895901 : List Nat := [1, 4, 3, 1, 1, 4, 2, 1, 4]
def baseStart_1895901 : Nat := 118140960795 + 1895901 * 2 ^ 59
def prefixEnd_1895901 : Nat := 4983230072969 + 3 ^ 40 * 1895901 * 2
def baseEnd_1895901 : Nat := 432670438373285338808185

theorem tailTrace_1895901 : CollatzResearch.WordTrace tailWord_1895901 prefixEnd_1895901 432670438373285338808185 := by
  unfold tailWord_1895901
  simp only [CollatzResearch.WordTrace]
  refine ⟨69149190304481945957343557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46099460202987963971562371 69149190304481945957343557)
  ·
    refine ⟨12965473182090364867001917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69149190304481945957343557 12965473182090364867001917)
    ·
      refine ⟨4862052443283886825125719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12965473182090364867001917 4862052443283886825125719)
      ·
        refine ⟨7293078664925830237688579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4862052443283886825125719 7293078664925830237688579)
        ·
          refine ⟨10939617997388745356532869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7293078664925830237688579 10939617997388745356532869)
          ·
            refine ⟨2051178374510389754349913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10939617997388745356532869 2051178374510389754349913)
            ·
              refine ⟨1538383780882792315762435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2051178374510389754349913 1538383780882792315762435)
              ·
                refine ⟨2307575671324188473643653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1538383780882792315762435 2307575671324188473643653)
                ·
                  refine ⟨432670438373285338808185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2307575671324188473643653 432670438373285338808185)
                  ·
                    rfl

theorem cell21_1895901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 2, 1, 4].length) (baseStart_1895901 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1895901 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1895901 prefixEnd_1895901 := by exact prefixLift 1895901
  have htrace : WordTrace (prefixWord ++ tailWord_1895901) baseStart_1895901 baseEnd_1895901 := by
    simpa [prefixWord, tailWord_1895901, baseEnd_1895901] using wordTrace_append hprefix tailTrace_1895901
  have hstable : (prefixWord ++ tailWord_1895901).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1895901).length < 2 ^ (prefixWord ++ tailWord_1895901).sum := by decide
  have hdescent : baseEnd_1895901 < baseStart_1895901 := by decide
  rcases family_descends (prefixWord ++ tailWord_1895901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1895943 : List Nat := [1, 1, 4, 3, 2, 1, 1, 4, 4]
def baseStart_1895943 : Nat := 118140960795 + 1895943 * 2 ^ 59
def prefixEnd_1895943 : Nat := 4983230072969 + 3 ^ 40 * 1895943 * 2
def baseEnd_1895943 : Nat := 432680023345502599108099

theorem tailTrace_1895943 : CollatzResearch.WordTrace tailWord_1895943 prefixEnd_1895943 432680023345502599108099 := by
  unfold tailWord_1895943
  simp only [CollatzResearch.WordTrace]
  refine ⟨69150722170329787130372483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46100481446886524753581655 69150722170329787130372483)
  ·
    refine ⟨103726083255494680695558725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69150722170329787130372483 103726083255494680695558725)
    ·
      refine ⟨19448640610405252630417261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103726083255494680695558725 19448640610405252630417261)
      ·
        refine ⟨7293240228901969736406473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19448640610405252630417261 7293240228901969736406473)
        ·
          refine ⟨5469930171676477302304855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7293240228901969736406473 5469930171676477302304855)
          ·
            refine ⟨8204895257514715953457283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5469930171676477302304855 8204895257514715953457283)
            ·
              refine ⟨12307342886272073930185925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8204895257514715953457283 12307342886272073930185925)
              ·
                refine ⟨2307626791176013861909861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12307342886272073930185925 2307626791176013861909861)
                ·
                  refine ⟨432680023345502599108099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2307626791176013861909861 432680023345502599108099)
                  ·
                    rfl

theorem cell21_1895943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 4, 4].length) (baseStart_1895943 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1895943 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1895943 prefixEnd_1895943 := by exact prefixLift 1895943
  have htrace : WordTrace (prefixWord ++ tailWord_1895943) baseStart_1895943 baseEnd_1895943 := by
    simpa [prefixWord, tailWord_1895943, baseEnd_1895943] using wordTrace_append hprefix tailTrace_1895943
  have hstable : (prefixWord ++ tailWord_1895943).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1895943).length < 2 ^ (prefixWord ++ tailWord_1895943).sum := by decide
  have hdescent : baseEnd_1895943 < baseStart_1895943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1895943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1895946 : List Nat := [3, 1, 2, 2, 2, 2, 4, 2, 3]
def baseStart_1895946 : Nat := 118140960795 + 1895946 * 2 ^ 59
def prefixEnd_1895946 : Nat := 4983230072969 + 3 ^ 40 * 1895946 * 2
def baseEnd_1895946 : Nat := 432680707986375260558093

theorem tailTrace_1895946 : CollatzResearch.WordTrace tailWord_1895946 prefixEnd_1895946 432680707986375260558093 := by
  unfold tailWord_1895946
  simp only [CollatzResearch.WordTrace]
  refine ⟨17287707897329729660682923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46100554392879279095154461 17287707897329729660682923)
  ·
    refine ⟨25931561845994594491024385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17287707897329729660682923 25931561845994594491024385)
    ·
      refine ⟨19448671384495945868268289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25931561845994594491024385 19448671384495945868268289)
      ·
        refine ⟨14586503538371959401201217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19448671384495945868268289 14586503538371959401201217)
        ·
          refine ⟨10939877653778969550900913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14586503538371959401201217 10939877653778969550900913)
          ·
            refine ⟨8204908240334227163175685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10939877653778969550900913 8204908240334227163175685)
            ·
              refine ⟨1538420295062667593095441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8204908240334227163175685 1538420295062667593095441)
              ·
                refine ⟨1153815221297000694821581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1538420295062667593095441 1153815221297000694821581)
                ·
                  refine ⟨432680707986375260558093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1153815221297000694821581 432680707986375260558093)
                  ·
                    rfl

theorem cell21_1895946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 4, 2, 3].length) (baseStart_1895946 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1895946 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1895946 prefixEnd_1895946 := by exact prefixLift 1895946
  have htrace : WordTrace (prefixWord ++ tailWord_1895946) baseStart_1895946 baseEnd_1895946 := by
    simpa [prefixWord, tailWord_1895946, baseEnd_1895946] using wordTrace_append hprefix tailTrace_1895946
  have hstable : (prefixWord ++ tailWord_1895946).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1895946).length < 2 ^ (prefixWord ++ tailWord_1895946).sum := by decide
  have hdescent : baseEnd_1895946 < baseStart_1895946 := by decide
  rcases family_descends (prefixWord ++ tailWord_1895946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1895949 : List Nat := [1, 7, 1, 1, 3, 1, 1, 6]
def baseStart_1895949 : Nat := 118140960795 + 1895949 * 2 ^ 59
def prefixEnd_1895949 : Nat := 4983230072969 + 3 ^ 40 * 1895949 * 2
def baseEnd_1895949 : Nat := 144227130875749307336029

theorem tailTrace_1895949 : CollatzResearch.WordTrace tailWord_1895949 prefixEnd_1895949 144227130875749307336029 := by
  unfold tailWord_1895949
  simp only [CollatzResearch.WordTrace]
  refine ⟨69150941008308050155090901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46100627338872033436727267 69150941008308050155090901)
  ·
    refine ⟨1620725179882219925509943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 69150941008308050155090901 1620725179882219925509943)
    ·
      refine ⟨2431087769823329888264915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1620725179882219925509943 2431087769823329888264915)
      ·
        refine ⟨3646631654734994832397373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2431087769823329888264915 3646631654734994832397373)
        ·
          refine ⟨1367486870525623062149015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3646631654734994832397373 1367486870525623062149015)
          ·
            refine ⟨2051230305788434593223523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1367486870525623062149015 2051230305788434593223523)
            ·
              refine ⟨3076845458682651889835285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2051230305788434593223523 3076845458682651889835285)
              ·
                refine ⟨144227130875749307336029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3076845458682651889835285 144227130875749307336029)
                ·
                  rfl

theorem cell21_1895949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 1, 6].length) (baseStart_1895949 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1895949 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1895949 prefixEnd_1895949 := by exact prefixLift 1895949
  have htrace : WordTrace (prefixWord ++ tailWord_1895949) baseStart_1895949 baseEnd_1895949 := by
    simpa [prefixWord, tailWord_1895949, baseEnd_1895949] using wordTrace_append hprefix tailTrace_1895949
  have hstable : (prefixWord ++ tailWord_1895949).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1895949).length < 2 ^ (prefixWord ++ tailWord_1895949).sum := by decide
  have hdescent : baseEnd_1895949 < baseStart_1895949 := by decide
  rcases family_descends (prefixWord ++ tailWord_1895949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1895957 : List Nat := [1, 3, 2, 1, 3, 2, 3, 6]
def baseStart_1895957 : Nat := 118140960795 + 1895957 * 2 ^ 59
def prefixEnd_1895957 : Nat := 4983230072969 + 3 ^ 40 * 1895957 * 2
def baseEnd_1895957 : Nat := 144227739445413895291579

theorem tailTrace_1895957 : CollatzResearch.WordTrace tailWord_1895957 prefixEnd_1895957 144227739445413895291579 := by
  unfold tailWord_1895957
  simp only [CollatzResearch.WordTrace]
  refine ⟨69151232792279067521382125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46100821861519378347588083 69151232792279067521382125)
  ·
    refine ⟨25931712297104650320518297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69151232792279067521382125 25931712297104650320518297)
    ·
      refine ⟨19448784222828487740388723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25931712297104650320518297 19448784222828487740388723)
      ·
        refine ⟨29173176334242731610583085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19448784222828487740388723 29173176334242731610583085)
        ·
          refine ⟨10939941125341024353968657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29173176334242731610583085 10939941125341024353968657)
          ·
            refine ⟨8204955844005768265476493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10939941125341024353968657 8204955844005768265476493)
            ·
              refine ⟨3076858441502163099553685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8204955844005768265476493 3076858441502163099553685)
              ·
                refine ⟨144227739445413895291579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3076858441502163099553685 144227739445413895291579)
                ·
                  rfl

theorem cell21_1895957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 3, 6].length) (baseStart_1895957 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1895957 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1895957 prefixEnd_1895957 := by exact prefixLift 1895957
  have htrace : WordTrace (prefixWord ++ tailWord_1895957) baseStart_1895957 baseEnd_1895957 := by
    simpa [prefixWord, tailWord_1895957, baseEnd_1895957] using wordTrace_append hprefix tailTrace_1895957
  have hstable : (prefixWord ++ tailWord_1895957).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1895957).length < 2 ^ (prefixWord ++ tailWord_1895957).sum := by decide
  have hdescent : baseEnd_1895957 < baseStart_1895957 := by decide
  rcases family_descends (prefixWord ++ tailWord_1895957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1896016 : List Nat := [2, 1, 1, 1, 1, 3, 4, 8]
def baseStart_1896016 : Nat := 118140960795 + 1896016 * 2 ^ 59
def prefixEnd_1896016 : Nat := 4983230072969 + 3 ^ 40 * 1896016 * 2
def baseEnd_1896016 : Nat := 144232227646690231463761

theorem tailTrace_1896016 : CollatzResearch.WordTrace tailWord_1896016 prefixEnd_1896016 144232227646690231463761 := by
  unfold tailWord_1896016
  simp only [CollatzResearch.WordTrace]
  refine ⟨34576692349532660298889951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46102256466043547065186601 34576692349532660298889951)
  ·
    refine ⟨51865038524298990448334927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34576692349532660298889951 51865038524298990448334927)
    ·
      refine ⟨77797557786448485672502391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51865038524298990448334927 77797557786448485672502391)
      ·
        refine ⟨116696336679672728508753587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77797557786448485672502391 116696336679672728508753587)
        ·
          refine ⟨175044505019509092763130381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116696336679672728508753587 175044505019509092763130381)
          ·
            refine ⟨65641689382315909786173893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 175044505019509092763130381 65641689382315909786173893)
            ·
              refine ⟨12307816759184233084907605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65641689382315909786173893 12307816759184233084907605)
              ·
                refine ⟨144232227646690231463761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12307816759184233084907605 144232227646690231463761)
                ·
                  rfl

theorem cell21_1896016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 8].length) (baseStart_1896016 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1896016 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1896016 prefixEnd_1896016 := by exact prefixLift 1896016
  have htrace : WordTrace (prefixWord ++ tailWord_1896016) baseStart_1896016 baseEnd_1896016 := by
    simpa [prefixWord, tailWord_1896016, baseEnd_1896016] using wordTrace_append hprefix tailTrace_1896016
  have hstable : (prefixWord ++ tailWord_1896016).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1896016).length < 2 ^ (prefixWord ++ tailWord_1896016).sum := by decide
  have hdescent : baseEnd_1896016 < baseStart_1896016 := by decide
  rcases family_descends (prefixWord ++ tailWord_1896016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1896126 : List Nat := [4, 2, 1, 1, 2, 4, 1, 6]
def baseStart_1896126 : Nat := 118140960795 + 1896126 * 2 ^ 59
def prefixEnd_1896126 : Nat := 4983230072969 + 3 ^ 40 * 1896126 * 2
def baseEnd_1896126 : Nat := 144240595479578315852575

theorem tailTrace_1896126 : CollatzResearch.WordTrace tailWord_1896126 prefixEnd_1896126 144240595479578315852575 := by
  unfold tailWord_1896126
  simp only [CollatzResearch.WordTrace]
  refine ⟨8644674591083351173035529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46104931152444539589522821 8644674591083351173035529)
  ·
    refine ⟨6483505943312513379776647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8644674591083351173035529 6483505943312513379776647)
    ·
      refine ⟨9725258914968770069664971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6483505943312513379776647 9725258914968770069664971)
      ·
        refine ⟨14587888372453155104497457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9725258914968770069664971 14587888372453155104497457)
        ·
          refine ⟨10940916279339866328373093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14587888372453155104497457 10940916279339866328373093)
          ·
            refine ⟨2051421802376224936569955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10940916279339866328373093 2051421802376224936569955)
            ·
              refine ⟨3077132703564337404854933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2051421802376224936569955 3077132703564337404854933)
              ·
                refine ⟨144240595479578315852575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3077132703564337404854933 144240595479578315852575)
                ·
                  rfl

theorem cell21_1896126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 1, 6].length) (baseStart_1896126 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1896126 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1896126 prefixEnd_1896126 := by exact prefixLift 1896126
  have htrace : WordTrace (prefixWord ++ tailWord_1896126) baseStart_1896126 baseEnd_1896126 := by
    simpa [prefixWord, tailWord_1896126, baseEnd_1896126] using wordTrace_append hprefix tailTrace_1896126
  have hstable : (prefixWord ++ tailWord_1896126).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1896126).length < 2 ^ (prefixWord ++ tailWord_1896126).sum := by decide
  have hdescent : baseEnd_1896126 < baseStart_1896126 := by decide
  rcases family_descends (prefixWord ++ tailWord_1896126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1896202 : List Nat := [3, 1, 2, 2, 1, 5, 2, 5]
def baseStart_1896202 : Nat := 118140960795 + 1896202 * 2 ^ 59
def prefixEnd_1896202 : Nat := 4983230072969 + 3 ^ 40 * 1896202 * 2
def baseEnd_1896202 : Nat := 144246376891391901430301

theorem tailTrace_1896202 : CollatzResearch.WordTrace tailWord_1896202 prefixEnd_1896202 144246376891391901430301 := by
  unfold tailWord_1896202
  simp only [CollatzResearch.WordTrace]
  refine ⟨17290042169097868591012715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46106779117594316242700573 17290042169097868591012715)
  ·
    refine ⟨25935063253646802886519073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17290042169097868591012715 25935063253646802886519073)
    ·
      refine ⟨19451297440235102164889305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25935063253646802886519073 19451297440235102164889305)
      ·
        refine ⟨14588473080176326623666979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19451297440235102164889305 14588473080176326623666979)
        ·
          refine ⟨21882709620264489935500469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14588473080176326623666979 21882709620264489935500469)
          ·
            refine ⟨2051504026899795931453169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21882709620264489935500469 2051504026899795931453169)
            ·
              refine ⟨1538628020174846948589877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2051504026899795931453169 1538628020174846948589877)
              ·
                refine ⟨144246376891391901430301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1538628020174846948589877 144246376891391901430301)
                ·
                  rfl

theorem cell21_1896202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 2, 5].length) (baseStart_1896202 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1896202 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1896202 prefixEnd_1896202 := by exact prefixLift 1896202
  have htrace : WordTrace (prefixWord ++ tailWord_1896202) baseStart_1896202 baseEnd_1896202 := by
    simpa [prefixWord, tailWord_1896202, baseEnd_1896202] using wordTrace_append hprefix tailTrace_1896202
  have hstable : (prefixWord ++ tailWord_1896202).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1896202).length < 2 ^ (prefixWord ++ tailWord_1896202).sum := by decide
  have hdescent : baseEnd_1896202 < baseStart_1896202 := by decide
  rcases family_descends (prefixWord ++ tailWord_1896202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1896284 : List Nat := [2, 2, 4, 2, 3, 1, 2, 2, 3]
def baseStart_1896284 : Nat := 118140960795 + 1896284 * 2 ^ 59
def prefixEnd_1896284 : Nat := 4983230072969 + 3 ^ 40 * 1896284 * 2
def baseEnd_1896284 : Nat := 432757844191361783924069

theorem tailTrace_1896284 : CollatzResearch.WordTrace tailWord_1896284 prefixEnd_1896284 432757844191361783924069 := by
  unfold tailWord_1896284
  simp only [CollatzResearch.WordTrace]
  refine ⟨34581579731047201184267953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46108772974729601579023937 34581579731047201184267953)
  ·
    refine ⟨25936184798285400888200965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34581579731047201184267953 25936184798285400888200965)
    ·
      refine ⟨4863034649678512666537681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25936184798285400888200965 4863034649678512666537681)
      ·
        refine ⟨3647275987258884499903261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4863034649678512666537681 3647275987258884499903261)
        ·
          refine ⟨1367728495222081687463723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3647275987258884499903261 1367728495222081687463723)
          ·
            refine ⟨2051592742833122531195585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1367728495222081687463723 2051592742833122531195585)
            ·
              refine ⟨1538694557124841898396689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2051592742833122531195585 1538694557124841898396689)
              ·
                refine ⟨1154020917843631423797517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1538694557124841898396689 1154020917843631423797517)
                ·
                  refine ⟨432757844191361783924069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1154020917843631423797517 432757844191361783924069)
                  ·
                    rfl

theorem cell21_1896284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 2, 2, 3].length) (baseStart_1896284 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1896284 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1896284 prefixEnd_1896284 := by exact prefixLift 1896284
  have htrace : WordTrace (prefixWord ++ tailWord_1896284) baseStart_1896284 baseEnd_1896284 := by
    simpa [prefixWord, tailWord_1896284, baseEnd_1896284] using wordTrace_append hprefix tailTrace_1896284
  have hstable : (prefixWord ++ tailWord_1896284).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1896284).length < 2 ^ (prefixWord ++ tailWord_1896284).sum := by decide
  have hdescent : baseEnd_1896284 < baseStart_1896284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1896284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1896340 : List Nat := [2, 4, 2, 1, 1, 4, 1, 2, 4]
def baseStart_1896340 : Nat := 118140960795 + 1896340 * 2 ^ 59
def prefixEnd_1896340 : Nat := 4983230072969 + 3 ^ 40 * 1896340 * 2
def baseEnd_1896340 : Nat := 432770624154318130990621

theorem tailTrace_1896340 : CollatzResearch.WordTrace tailWord_1896340 prefixEnd_1896340 432770624154318130990621 := by
  unfold tailWord_1896340
  simp only [CollatzResearch.WordTrace]
  refine ⟨34582600974945761966287237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46110134633261015955049649 34582600974945761966287237)
  ·
    refine ⟨6484237682802330368678857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34582600974945761966287237 6484237682802330368678857)
    ·
      refine ⟨4863178262101747776509143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6484237682802330368678857 4863178262101747776509143)
      ·
        refine ⟨7294767393152621664763715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4863178262101747776509143 7294767393152621664763715)
        ·
          refine ⟨10942151089728932497145573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7294767393152621664763715 10942151089728932497145573)
          ·
            refine ⟨2051653329324174843214795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10942151089728932497145573 2051653329324174843214795)
            ·
              refine ⟨3077479993986262264822193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2051653329324174843214795 3077479993986262264822193)
              ·
                refine ⟨2308109995489696698616645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3077479993986262264822193 2308109995489696698616645)
                ·
                  refine ⟨432770624154318130990621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2308109995489696698616645 432770624154318130990621)
                  ·
                    rfl

theorem cell21_1896340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 1, 2, 4].length) (baseStart_1896340 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1896340 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1896340 prefixEnd_1896340 := by exact prefixLift 1896340
  have htrace : WordTrace (prefixWord ++ tailWord_1896340) baseStart_1896340 baseEnd_1896340 := by
    simpa [prefixWord, tailWord_1896340, baseEnd_1896340] using wordTrace_append hprefix tailTrace_1896340
  have hstable : (prefixWord ++ tailWord_1896340).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1896340).length < 2 ^ (prefixWord ++ tailWord_1896340).sum := by decide
  have hdescent : baseEnd_1896340 < baseStart_1896340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1896340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1896382 : List Nat := [4, 2, 1, 1, 1, 3, 1, 2, 6]
def baseStart_1896382 : Nat := 118140960795 + 1896382 * 2 ^ 59
def prefixEnd_1896382 : Nat := 4983230072969 + 3 ^ 40 * 1896382 * 2
def baseEnd_1896382 : Nat := 432780209126535391290535

theorem tailTrace_1896382 : CollatzResearch.WordTrace tailWord_1896382 prefixEnd_1896382 432780209126535391290535 := by
  unfold tailWord_1896382
  simp only [CollatzResearch.WordTrace]
  refine ⟨8645841726967420638200425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46111155877159576737068933 8645841726967420638200425)
  ·
    refine ⟨6484381295225565478650319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8645841726967420638200425 6484381295225565478650319)
    ·
      refine ⟨9726571942838348217975479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6484381295225565478650319 9726571942838348217975479)
      ·
        refine ⟨14589857914257522326963219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9726571942838348217975479 14589857914257522326963219)
        ·
          refine ⟨21884786871386283490444829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14589857914257522326963219 21884786871386283490444829)
          ·
            refine ⟨8206795076769856308916811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21884786871386283490444829 8206795076769856308916811)
            ·
              refine ⟨12310192615154784463375217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8206795076769856308916811 12310192615154784463375217)
              ·
                refine ⟨9232644461366088347531413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12310192615154784463375217 9232644461366088347531413)
                ·
                  refine ⟨432780209126535391290535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9232644461366088347531413 432780209126535391290535)
                  ·
                    rfl

theorem cell21_1896382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 2, 6].length) (baseStart_1896382 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1896382 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1896382 prefixEnd_1896382 := by exact prefixLift 1896382
  have htrace : WordTrace (prefixWord ++ tailWord_1896382) baseStart_1896382 baseEnd_1896382 := by
    simpa [prefixWord, tailWord_1896382, baseEnd_1896382] using wordTrace_append hprefix tailTrace_1896382
  have hstable : (prefixWord ++ tailWord_1896382).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1896382).length < 2 ^ (prefixWord ++ tailWord_1896382).sum := by decide
  have hdescent : baseEnd_1896382 < baseStart_1896382 := by decide
  rcases family_descends (prefixWord ++ tailWord_1896382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1896396 : List Nat := [2, 2, 1, 4, 1, 2, 9]
def baseStart_1896396 : Nat := 118140960795 + 1896396 * 2 ^ 59
def prefixEnd_1896396 : Nat := 4983230072969 + 3 ^ 40 * 1896396 * 2
def baseEnd_1896396 : Nat := 48087044901919386450797

theorem tailTrace_1896396 : CollatzResearch.WordTrace tailWord_1896396 prefixEnd_1896396 48087044901919386450797 := by
  unfold tailWord_1896396
  simp only [CollatzResearch.WordTrace]
  refine ⟨34583622218844322748306521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46111496291792430331075361 34583622218844322748306521)
  ·
    refine ⟨25937716664133242061229891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34583622218844322748306521 25937716664133242061229891)
    ·
      refine ⟨38906574996199863091844837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25937716664133242061229891 38906574996199863091844837)
      ·
        refine ⟨7294982811787474329720907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38906574996199863091844837 7294982811787474329720907)
        ·
          refine ⟨10942474217681211494581361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7294982811787474329720907 10942474217681211494581361)
          ·
            refine ⟨8206855663260908620936021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10942474217681211494581361 8206855663260908620936021)
            ·
              refine ⟨48087044901919386450797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8206855663260908620936021 48087044901919386450797)
              ·
                rfl

theorem cell21_1896396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 9].length) (baseStart_1896396 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1896396 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1896396 prefixEnd_1896396 := by exact prefixLift 1896396
  have htrace : WordTrace (prefixWord ++ tailWord_1896396) baseStart_1896396 baseEnd_1896396 := by
    simpa [prefixWord, tailWord_1896396, baseEnd_1896396] using wordTrace_append hprefix tailTrace_1896396
  have hstable : (prefixWord ++ tailWord_1896396).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1896396).length < 2 ^ (prefixWord ++ tailWord_1896396).sum := by decide
  have hdescent : baseEnd_1896396 < baseStart_1896396 := by decide
  rcases family_descends (prefixWord ++ tailWord_1896396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1896402 : List Nat := [3, 2, 2, 3, 3, 1, 1, 1, 5]
def baseStart_1896402 : Nat := 118140960795 + 1896402 * 2 ^ 59
def prefixEnd_1896402 : Nat := 4983230072969 + 3 ^ 40 * 1896402 * 2
def baseEnd_1896402 : Nat := 432784773399019800957161

theorem tailTrace_1896402 : CollatzResearch.WordTrace tailWord_1896402 prefixEnd_1896402 432784773399019800957161 := by
  unfold tailWord_1896402
  simp only [CollatzResearch.WordTrace]
  refine ⟨17291865818916727130332865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46111642183777939014220973 17291865818916727130332865)
  ·
    refine ⟨12968899364187545347749649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17291865818916727130332865 12968899364187545347749649)
    ·
      refine ⟨9726674523140659010812237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12968899364187545347749649 9726674523140659010812237)
      ·
        refine ⟨3647502946177747129054589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9726674523140659010812237 3647502946177747129054589)
        ·
          refine ⟨1367813604816655173395471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3647502946177747129054589 1367813604816655173395471)
          ·
            refine ⟨2051720407224982760093207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1367813604816655173395471 2051720407224982760093207)
            ·
              refine ⟨3077580610837474140139811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2051720407224982760093207 3077580610837474140139811)
              ·
                refine ⟨4616370916256211210209717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3077580610837474140139811 4616370916256211210209717)
                ·
                  refine ⟨432784773399019800957161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4616370916256211210209717 432784773399019800957161)
                  ·
                    rfl

theorem cell21_1896402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 1, 1, 5].length) (baseStart_1896402 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1896402 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1896402 prefixEnd_1896402 := by exact prefixLift 1896402
  have htrace : WordTrace (prefixWord ++ tailWord_1896402) baseStart_1896402 baseEnd_1896402 := by
    simpa [prefixWord, tailWord_1896402, baseEnd_1896402] using wordTrace_append hprefix tailTrace_1896402
  have hstable : (prefixWord ++ tailWord_1896402).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1896402).length < 2 ^ (prefixWord ++ tailWord_1896402).sum := by decide
  have hdescent : baseEnd_1896402 < baseStart_1896402 := by decide
  rcases family_descends (prefixWord ++ tailWord_1896402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1896444 : List Nat := [2, 2, 2, 1, 2, 2, 2, 5, 3]
def baseStart_1896444 : Nat := 118140960795 + 1896444 * 2 ^ 59
def prefixEnd_1896444 : Nat := 4983230072969 + 3 ^ 40 * 1896444 * 2
def baseEnd_1896444 : Nat := 432794358371237061257075

theorem tailTrace_1896444 : CollatzResearch.WordTrace tailWord_1896444 prefixEnd_1896444 432794358371237061257075 := by
  unfold tailWord_1896444
  simp only [CollatzResearch.WordTrace]
  refine ⟨34584497570757374847180193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46112663427676499796240257 34584497570757374847180193)
  ·
    refine ⟨25938373178068031135385145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34584497570757374847180193 25938373178068031135385145)
    ·
      refine ⟨19453779883551023351538859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25938373178068031135385145 19453779883551023351538859)
      ·
        refine ⟨29180669825326535027308289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19453779883551023351538859 29180669825326535027308289)
        ·
          refine ⟨21885502368994901270481217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29180669825326535027308289 21885502368994901270481217)
          ·
            refine ⟨16414126776746175952860913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21885502368994901270481217 16414126776746175952860913)
            ·
              refine ⟨12310595082559631964645685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16414126776746175952860913 12310595082559631964645685)
              ·
                refine ⟨1154118288989965496685533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12310595082559631964645685 1154118288989965496685533)
                ·
                  refine ⟨432794358371237061257075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1154118288989965496685533 432794358371237061257075)
                  ·
                    rfl

theorem cell21_1896444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 5, 3].length) (baseStart_1896444 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1896444 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1896444 prefixEnd_1896444 := by exact prefixLift 1896444
  have htrace : WordTrace (prefixWord ++ tailWord_1896444) baseStart_1896444 baseEnd_1896444 := by
    simpa [prefixWord, tailWord_1896444, baseEnd_1896444] using wordTrace_append hprefix tailTrace_1896444
  have hstable : (prefixWord ++ tailWord_1896444).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1896444).length < 2 ^ (prefixWord ++ tailWord_1896444).sum := by decide
  have hdescent : baseEnd_1896444 < baseStart_1896444 := by decide
  rcases family_descends (prefixWord ++ tailWord_1896444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1896554 : List Nat := [3, 1, 3, 2, 3, 2, 1, 3, 3]
def baseStart_1896554 : Nat := 118140960795 + 1896554 * 2 ^ 59
def prefixEnd_1896554 : Nat := 4983230072969 + 3 ^ 40 * 1896554 * 2
def baseEnd_1896554 : Nat := 432819461869901314423517

theorem tailTrace_1896554 : CollatzResearch.WordTrace tailWord_1896554 prefixEnd_1896554 432819461869901314423517 := by
  unfold tailWord_1896554
  simp only [CollatzResearch.WordTrace]
  refine ⟨17293251792779059620216179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46115338114077492320576477 17293251792779059620216179)
  ·
    refine ⟨25939877689168589430324269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17293251792779059620216179 25939877689168589430324269)
    ·
      refine ⟨9727454133438221036371601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25939877689168589430324269 9727454133438221036371601)
      ·
        refine ⟨7295590600078665777278701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9727454133438221036371601 7295590600078665777278701)
        ·
          refine ⟨2735846475029499666479513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7295590600078665777278701 2735846475029499666479513)
          ·
            refine ⟨2051884856272124749859635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2735846475029499666479513 2051884856272124749859635)
            ·
              refine ⟨3077827284408187124789453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2051884856272124749859635 3077827284408187124789453)
              ·
                refine ⟨1154185231653070171796045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3077827284408187124789453 1154185231653070171796045)
                ·
                  refine ⟨432819461869901314423517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1154185231653070171796045 432819461869901314423517)
                  ·
                    rfl

theorem cell21_1896554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 1, 3, 3].length) (baseStart_1896554 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1896554 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1896554 prefixEnd_1896554 := by exact prefixLift 1896554
  have htrace : WordTrace (prefixWord ++ tailWord_1896554) baseStart_1896554 baseEnd_1896554 := by
    simpa [prefixWord, tailWord_1896554, baseEnd_1896554] using wordTrace_append hprefix tailTrace_1896554
  have hstable : (prefixWord ++ tailWord_1896554).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1896554).length < 2 ^ (prefixWord ++ tailWord_1896554).sum := by decide
  have hdescent : baseEnd_1896554 < baseStart_1896554 := by decide
  rcases family_descends (prefixWord ++ tailWord_1896554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1896579 : List Nat := [1, 1, 1, 3, 3, 3, 3, 1, 5]
def baseStart_1896579 : Nat := 118140960795 + 1896579 * 2 ^ 59
def prefixEnd_1896579 : Nat := 4983230072969 + 3 ^ 40 * 1896579 * 2
def baseEnd_1896579 : Nat := 432825167210506826506799

theorem tailTrace_1896579 : CollatzResearch.WordTrace tailWord_1896579 prefixEnd_1896579 432825167210506826506799 := by
  unfold tailWord_1896579
  simp only [CollatzResearch.WordTrace]
  refine ⟨69173918996025667750524791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46115945997350445167016527 69173918996025667750524791)
  ·
    refine ⟨103760878494038501625787187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69173918996025667750524791 103760878494038501625787187)
    ·
      refine ⟨155641317741057752438680781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103760878494038501625787187 155641317741057752438680781)
      ·
        refine ⟨58365494152896657164505293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155641317741057752438680781 58365494152896657164505293)
        ·
          refine ⟨21887060307336246436689485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58365494152896657164505293 21887060307336246436689485)
          ·
            refine ⟨8207647615251092413758557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21887060307336246436689485 8207647615251092413758557)
            ·
              refine ⟨3077867855719159655159459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8207647615251092413758557 3077867855719159655159459)
              ·
                refine ⟨4616801783578739482739189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3077867855719159655159459 4616801783578739482739189)
                ·
                  refine ⟨432825167210506826506799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4616801783578739482739189 432825167210506826506799)
                  ·
                    rfl

theorem cell21_1896579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 3, 1, 5].length) (baseStart_1896579 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1896579 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1896579 prefixEnd_1896579 := by exact prefixLift 1896579
  have htrace : WordTrace (prefixWord ++ tailWord_1896579) baseStart_1896579 baseEnd_1896579 := by
    simpa [prefixWord, tailWord_1896579, baseEnd_1896579] using wordTrace_append hprefix tailTrace_1896579
  have hstable : (prefixWord ++ tailWord_1896579).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1896579).length < 2 ^ (prefixWord ++ tailWord_1896579).sum := by decide
  have hdescent : baseEnd_1896579 < baseStart_1896579 := by decide
  rcases family_descends (prefixWord ++ tailWord_1896579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1896672 : List Nat := [2, 1, 1, 3, 1, 3, 4, 3, 3]
def baseStart_1896672 : Nat := 118140960795 + 1896672 * 2 ^ 59
def prefixEnd_1896672 : Nat := 4983230072969 + 3 ^ 40 * 1896672 * 2
def baseEnd_1896672 : Nat := 432846391077559331456609

theorem tailTrace_1896672 : CollatzResearch.WordTrace tailWord_1896672 prefixEnd_1896672 432846391077559331456609 := by
  unfold tailWord_1896672
  simp only [CollatzResearch.WordTrace]
  refine ⟨34588655492344372316830135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46118207323125829755773513 34588655492344372316830135)
  ·
    refine ⟨51882983238516558475245203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34588655492344372316830135 51882983238516558475245203)
    ·
      refine ⟨77824474857774837712867805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51882983238516558475245203 77824474857774837712867805)
      ·
        refine ⟨29184178071665564142325427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77824474857774837712867805 29184178071665564142325427)
        ·
          refine ⟨43776267107498346213488141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29184178071665564142325427 43776267107498346213488141)
          ·
            refine ⟨16416100165311879830058053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43776267107498346213488141 16416100165311879830058053)
            ·
              refine ⟨3078018780995977468135885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16416100165311879830058053 3078018780995977468135885)
              ·
                refine ⟨1154257042873491550550957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3078018780995977468135885 1154257042873491550550957)
                ·
                  refine ⟨432846391077559331456609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1154257042873491550550957 432846391077559331456609)
                  ·
                    rfl

theorem cell21_1896672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 4, 3, 3].length) (baseStart_1896672 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1896672 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1896672 prefixEnd_1896672 := by exact prefixLift 1896672
  have htrace : WordTrace (prefixWord ++ tailWord_1896672) baseStart_1896672 baseEnd_1896672 := by
    simpa [prefixWord, tailWord_1896672, baseEnd_1896672] using wordTrace_append hprefix tailTrace_1896672
  have hstable : (prefixWord ++ tailWord_1896672).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1896672).length < 2 ^ (prefixWord ++ tailWord_1896672).sum := by decide
  have hdescent : baseEnd_1896672 < baseStart_1896672 := by decide
  rcases family_descends (prefixWord ++ tailWord_1896672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1896683 : List Nat := [1, 1, 1, 1, 2, 5, 10]
def baseStart_1896683 : Nat := 118140960795 + 1896683 * 2 ^ 59
def prefixEnd_1896683 : Nat := 4983230072969 + 3 ^ 40 * 1896683 * 2
def baseEnd_1896683 : Nat := 48094322380825084085917

theorem tailTrace_1896683 : CollatzResearch.WordTrace tailWord_1896683 prefixEnd_1896683 48094322380825084085917 := by
  unfold tailWord_1896683
  simp only [CollatzResearch.WordTrace]
  refine ⟨69177712187648893512310703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46118474791765929008207135 69177712187648893512310703)
  ·
    refine ⟨103766568281473340268466055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69177712187648893512310703 103766568281473340268466055)
    ·
      refine ⟨155649852422210010402699083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103766568281473340268466055 155649852422210010402699083)
      ·
        refine ⟨233474778633315015604048625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155649852422210010402699083 233474778633315015604048625)
        ·
          refine ⟨175106083974986261703036469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 233474778633315015604048625 175106083974986261703036469)
          ·
            refine ⟨16416195372654962034659669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 175106083974986261703036469 16416195372654962034659669)
            ·
              refine ⟨48094322380825084085917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 16416195372654962034659669 48094322380825084085917)
              ·
                rfl

theorem cell21_1896683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 10].length) (baseStart_1896683 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1896683 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1896683 prefixEnd_1896683 := by exact prefixLift 1896683
  have htrace : WordTrace (prefixWord ++ tailWord_1896683) baseStart_1896683 baseEnd_1896683 := by
    simpa [prefixWord, tailWord_1896683, baseEnd_1896683] using wordTrace_append hprefix tailTrace_1896683
  have hstable : (prefixWord ++ tailWord_1896683).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1896683).length < 2 ^ (prefixWord ++ tailWord_1896683).sum := by decide
  have hdescent : baseEnd_1896683 < baseStart_1896683 := by decide
  rcases family_descends (prefixWord ++ tailWord_1896683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1896734 : List Nat := [4, 3, 2, 1, 1, 3, 7]
def baseStart_1896734 : Nat := 118140960795 + 1896734 * 2 ^ 59
def prefixEnd_1896734 : Nat := 4983230072969 + 3 ^ 40 * 1896734 * 2
def baseEnd_1896734 : Nat := 48095615591362333491461

theorem tailTrace_1896734 : CollatzResearch.WordTrace tailWord_1896734 prefixEnd_1896734 48095615591362333491461 := by
  unfold tailWord_1896734
  simp only [CollatzResearch.WordTrace]
  refine ⟨8647446538808016152802157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46119714873642752814944837 8647446538808016152802157)
  ·
    refine ⟨3242792452053006057300809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8647446538808016152802157 3242792452053006057300809)
    ·
      refine ⟨2432094339039754542975607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3242792452053006057300809 2432094339039754542975607)
      ·
        refine ⟨3648141508559631814463411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2432094339039754542975607 3648141508559631814463411)
        ·
          refine ⟨5472212262839447721695117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3648141508559631814463411 5472212262839447721695117)
          ·
            refine ⟨2052079598564792895635669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5472212262839447721695117 2052079598564792895635669)
            ·
              refine ⟨48095615591362333491461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2052079598564792895635669 48095615591362333491461)
              ·
                rfl

theorem cell21_1896734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 7].length) (baseStart_1896734 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1896734 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1896734 prefixEnd_1896734 := by exact prefixLift 1896734
  have htrace : WordTrace (prefixWord ++ tailWord_1896734) baseStart_1896734 baseEnd_1896734 := by
    simpa [prefixWord, tailWord_1896734, baseEnd_1896734] using wordTrace_append hprefix tailTrace_1896734
  have hstable : (prefixWord ++ tailWord_1896734).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1896734).length < 2 ^ (prefixWord ++ tailWord_1896734).sum := by decide
  have hdescent : baseEnd_1896734 < baseStart_1896734 := by decide
  rcases family_descends (prefixWord ++ tailWord_1896734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1896762 : List Nat := [3, 1, 1, 1, 4, 3, 1, 3, 4]
def baseStart_1896762 : Nat := 118140960795 + 1896762 * 2 ^ 59
def prefixEnd_1896762 : Nat := 4983230072969 + 3 ^ 40 * 1896762 * 2
def baseEnd_1896762 : Nat := 432866930303739174956425

theorem tailTrace_1896762 : CollatzResearch.WordTrace tailWord_1896762 prefixEnd_1896762 432866930303739174956425 := by
  unfold tailWord_1896762
  simp only [CollatzResearch.WordTrace]
  refine ⟨17295148388590672501109135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46120395702908460002957693 17295148388590672501109135)
  ·
    refine ⟨25942722582886008751663703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17295148388590672501109135 25942722582886008751663703)
    ·
      refine ⟨38914083874329013127495555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25942722582886008751663703 38914083874329013127495555)
      ·
        refine ⟨58371125811493519691243333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38914083874329013127495555 58371125811493519691243333)
        ·
          refine ⟨10944586089655034942108125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58371125811493519691243333 10944586089655034942108125)
          ·
            refine ⟨4104219783620638103290547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10944586089655034942108125 4104219783620638103290547)
            ·
              refine ⟨6156329675430957154935821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4104219783620638103290547 6156329675430957154935821)
              ·
                refine ⟨2308623628286608933100933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6156329675430957154935821 2308623628286608933100933)
                ·
                  refine ⟨432866930303739174956425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2308623628286608933100933 432866930303739174956425)
                  ·
                    rfl

theorem cell21_1896762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 3, 4].length) (baseStart_1896762 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1896762 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1896762 prefixEnd_1896762 := by exact prefixLift 1896762
  have htrace : WordTrace (prefixWord ++ tailWord_1896762) baseStart_1896762 baseEnd_1896762 := by
    simpa [prefixWord, tailWord_1896762, baseEnd_1896762] using wordTrace_append hprefix tailTrace_1896762
  have hstable : (prefixWord ++ tailWord_1896762).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1896762).length < 2 ^ (prefixWord ++ tailWord_1896762).sum := by decide
  have hdescent : baseEnd_1896762 < baseStart_1896762 := by decide
  rcases family_descends (prefixWord ++ tailWord_1896762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1896796 : List Nat := [2, 2, 4, 3, 1, 1, 2, 2, 4]
def baseStart_1896796 : Nat := 118140960795 + 1896796 * 2 ^ 59
def prefixEnd_1896796 : Nat := 4983230072969 + 3 ^ 40 * 1896796 * 2
def baseEnd_1896796 : Nat := 432874689566962671389689

theorem tailTrace_1896796 : CollatzResearch.WordTrace tailWord_1896796 prefixEnd_1896796 432874689566962671389689 := by
  unfold tailWord_1896796
  simp only [CollatzResearch.WordTrace]
  refine ⟨34590916818119756905587121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46121222424159675874116161 34590916818119756905587121)
  ·
    refine ⟨25943187613589817679190341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34590916818119756905587121 25943187613589817679190341)
    ·
      refine ⟨4864347677548090814848189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25943187613589817679190341 4864347677548090814848189)
      ·
        refine ⟨1824130379080534055568071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4864347677548090814848189 1824130379080534055568071)
        ·
          refine ⟨2736195568620801083352107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1824130379080534055568071 2736195568620801083352107)
          ·
            refine ⟨4104293352931201625028161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2736195568620801083352107 4104293352931201625028161)
            ·
              refine ⟨3078220014698401218771121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4104293352931201625028161 3078220014698401218771121)
              ·
                refine ⟨2308665011023800914078341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3078220014698401218771121 2308665011023800914078341)
                ·
                  refine ⟨432874689566962671389689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2308665011023800914078341 432874689566962671389689)
                  ·
                    rfl

theorem cell21_1896796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 2, 2, 4].length) (baseStart_1896796 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1896796 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1896796 prefixEnd_1896796 := by exact prefixLift 1896796
  have htrace : WordTrace (prefixWord ++ tailWord_1896796) baseStart_1896796 baseEnd_1896796 := by
    simpa [prefixWord, tailWord_1896796, baseEnd_1896796] using wordTrace_append hprefix tailTrace_1896796
  have hstable : (prefixWord ++ tailWord_1896796).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1896796).length < 2 ^ (prefixWord ++ tailWord_1896796).sum := by decide
  have hdescent : baseEnd_1896796 < baseStart_1896796 := by decide
  rcases family_descends (prefixWord ++ tailWord_1896796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1896872 : List Nat := [2, 1, 6, 1, 1, 2, 3, 1, 4]
def baseStart_1896872 : Nat := 118140960795 + 1896872 * 2 ^ 59
def prefixEnd_1896872 : Nat := 4983230072969 + 3 ^ 40 * 1896872 * 2
def baseEnd_1896872 : Nat := 432892033802403428122867

theorem tailTrace_1896872 : CollatzResearch.WordTrace tailWord_1896872 prefixEnd_1896872 432892033802403428122867 := by
  unfold tailWord_1896872
  simp only [CollatzResearch.WordTrace]
  refine ⟨34592302791982089395470435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46123070389309452527293913 34592302791982089395470435)
  ·
    refine ⟨51888454187973134093205653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34592302791982089395470435 51888454187973134093205653)
    ·
      refine ⟨2432271290061240660619015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 51888454187973134093205653 2432271290061240660619015)
      ·
        refine ⟨3648406935091860990928523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2432271290061240660619015 3648406935091860990928523)
        ·
          refine ⟨5472610402637791486392785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3648406935091860990928523 5472610402637791486392785)
          ·
            refine ⟨4104457801978343614794589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5472610402637791486392785 4104457801978343614794589)
            ·
              refine ⟨1539171675741878855547971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4104457801978343614794589 1539171675741878855547971)
              ·
                refine ⟨2308757513612818283321957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1539171675741878855547971 2308757513612818283321957)
                ·
                  refine ⟨432892033802403428122867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2308757513612818283321957 432892033802403428122867)
                  ·
                    rfl

theorem cell21_1896872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 3, 1, 4].length) (baseStart_1896872 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1896872 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1896872 prefixEnd_1896872 := by exact prefixLift 1896872
  have htrace : WordTrace (prefixWord ++ tailWord_1896872) baseStart_1896872 baseEnd_1896872 := by
    simpa [prefixWord, tailWord_1896872, baseEnd_1896872] using wordTrace_append hprefix tailTrace_1896872
  have hstable : (prefixWord ++ tailWord_1896872).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1896872).length < 2 ^ (prefixWord ++ tailWord_1896872).sum := by decide
  have hdescent : baseEnd_1896872 < baseStart_1896872 := by decide
  rcases family_descends (prefixWord ++ tailWord_1896872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1896917 : List Nat := [1, 3, 2, 3, 1, 3, 3, 2, 3]
def baseStart_1896917 : Nat := 118140960795 + 1896917 * 2 ^ 59
def prefixEnd_1896917 : Nat := 4983230072969 + 3 ^ 40 * 1896917 * 2
def baseEnd_1896917 : Nat := 432902303415493349872775

theorem tailTrace_1896917 : CollatzResearch.WordTrace tailWord_1896917 prefixEnd_1896917 432902303415493349872775 := by
  unfold tailWord_1896917
  simp only [CollatzResearch.WordTrace]
  refine ⟨69186246868801151476329005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46124164579200767650886003 69186246868801151476329005)
  ·
    refine ⟨25944842575800431803623377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69186246868801151476329005 25944842575800431803623377)
    ·
      refine ⟨19458631931850323852717533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25944842575800431803623377 19458631931850323852717533)
      ·
        refine ⟨7296986974443871444769075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19458631931850323852717533 7296986974443871444769075)
        ·
          refine ⟨10945480461665807167153613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7296986974443871444769075 10945480461665807167153613)
          ·
            refine ⟨4104555173124677687682605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10945480461665807167153613 4104555173124677687682605)
            ·
              refine ⟨1539208189921754132880977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4104555173124677687682605 1539208189921754132880977)
              ·
                refine ⟨1154406142441315599660733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1539208189921754132880977 1154406142441315599660733)
                ·
                  refine ⟨432902303415493349872775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1154406142441315599660733 432902303415493349872775)
                  ·
                    rfl

theorem cell21_1896917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 3, 2, 3].length) (baseStart_1896917 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1896917 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1896917 prefixEnd_1896917 := by exact prefixLift 1896917
  have htrace : WordTrace (prefixWord ++ tailWord_1896917) baseStart_1896917 baseEnd_1896917 := by
    simpa [prefixWord, tailWord_1896917, baseEnd_1896917] using wordTrace_append hprefix tailTrace_1896917
  have hstable : (prefixWord ++ tailWord_1896917).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1896917).length < 2 ^ (prefixWord ++ tailWord_1896917).sum := by decide
  have hdescent : baseEnd_1896917 < baseStart_1896917 := by decide
  rcases family_descends (prefixWord ++ tailWord_1896917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1896959 : List Nat := [1, 1, 2, 2, 1, 2, 4, 5, 3]
def baseStart_1896959 : Nat := 118140960795 + 1896959 * 2 ^ 59
def prefixEnd_1896959 : Nat := 4983230072969 + 3 ^ 40 * 1896959 * 2
def baseEnd_1896959 : Nat := 432911888387710610172689

theorem tailTrace_1896959 : CollatzResearch.WordTrace tailWord_1896959 prefixEnd_1896959 432911888387710610172689 := by
  unfold tailWord_1896959
  simp only [CollatzResearch.WordTrace]
  refine ⟨69187778734648992649357931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46125185823099328432905287 69187778734648992649357931)
  ·
    refine ⟨103781668101973488974036897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69187778734648992649357931 103781668101973488974036897)
    ·
      refine ⟨77836251076480116730527673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103781668101973488974036897 77836251076480116730527673)
      ·
        refine ⟨58377188307360087547895755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77836251076480116730527673 58377188307360087547895755)
        ·
          refine ⟨87565782461040131321843633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58377188307360087547895755 87565782461040131321843633)
          ·
            refine ⟨65674336845780098491382725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87565782461040131321843633 65674336845780098491382725)
            ·
              refine ⟨12313938158583768467134261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65674336845780098491382725 12313938158583768467134261)
              ·
                refine ⟨1154431702367228293793837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12313938158583768467134261 1154431702367228293793837)
                ·
                  refine ⟨432911888387710610172689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1154431702367228293793837 432911888387710610172689)
                  ·
                    rfl

theorem cell21_1896959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 5, 3].length) (baseStart_1896959 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1896959 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1896959 prefixEnd_1896959 := by exact prefixLift 1896959
  have htrace : WordTrace (prefixWord ++ tailWord_1896959) baseStart_1896959 baseEnd_1896959 := by
    simpa [prefixWord, tailWord_1896959, baseEnd_1896959] using wordTrace_append hprefix tailTrace_1896959
  have hstable : (prefixWord ++ tailWord_1896959).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1896959).length < 2 ^ (prefixWord ++ tailWord_1896959).sum := by decide
  have hdescent : baseEnd_1896959 < baseStart_1896959 := by decide
  rcases family_descends (prefixWord ++ tailWord_1896959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1897035 : List Nat := [1, 1, 1, 1, 3, 1, 6, 4, 3]
def baseStart_1897035 : Nat := 118140960795 + 1897035 * 2 ^ 59
def prefixEnd_1897035 : Nat := 4983230072969 + 3 ^ 40 * 1897035 * 2
def baseEnd_1897035 : Nat := 432929232623151366905867

theorem tailTrace_1897035 : CollatzResearch.WordTrace tailWord_1897035 prefixEnd_1897035 432929232623151366905867 := by
  unfold tailWord_1897035
  simp only [CollatzResearch.WordTrace]
  refine ⟨69190550682373657629124559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46127033788249105086083039 69190550682373657629124559)
  ·
    refine ⟨103785826023560486443686839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69190550682373657629124559 103785826023560486443686839)
    ·
      refine ⟨155678739035340729665530259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103785826023560486443686839 155678739035340729665530259)
      ·
        refine ⟨233518108553011094498295389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155678739035340729665530259 233518108553011094498295389)
        ·
          refine ⟨87569290707379160436860771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 233518108553011094498295389 87569290707379160436860771)
          ·
            refine ⟨131353936061068740655291157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87569290707379160436860771 131353936061068740655291157)
            ·
              refine ⟨6157215752862597218216773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 131353936061068740655291157 6157215752862597218216773)
              ·
                refine ⟨1154477953661736978415645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6157215752862597218216773 1154477953661736978415645)
                ·
                  refine ⟨432929232623151366905867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1154477953661736978415645 432929232623151366905867)
                  ·
                    rfl

theorem cell21_1897035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 4, 3].length) (baseStart_1897035 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1897035 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1897035 prefixEnd_1897035 := by exact prefixLift 1897035
  have htrace : WordTrace (prefixWord ++ tailWord_1897035) baseStart_1897035 baseEnd_1897035 := by
    simpa [prefixWord, tailWord_1897035, baseEnd_1897035] using wordTrace_append hprefix tailTrace_1897035
  have hstable : (prefixWord ++ tailWord_1897035).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1897035).length < 2 ^ (prefixWord ++ tailWord_1897035).sum := by decide
  have hdescent : baseEnd_1897035 < baseStart_1897035 := by decide
  rcases family_descends (prefixWord ++ tailWord_1897035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1897069 : List Nat := [1, 5, 1, 1, 3, 3, 1, 3, 3]
def baseStart_1897069 : Nat := 118140960795 + 1897069 * 2 ^ 59
def prefixEnd_1897069 : Nat := 4983230072969 + 3 ^ 40 * 1897069 * 2
def baseEnd_1897069 : Nat := 432936991886374863339131

theorem tailTrace_1897069 : CollatzResearch.WordTrace tailWord_1897069 prefixEnd_1897069 432936991886374863339131 := by
  unfold tailWord_1897069
  simp only [CollatzResearch.WordTrace]
  refine ⟨69191790764250481435862261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46127860509500320957241507 69191790764250481435862261)
  ·
    refine ⟨6486730384148482634612087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 69191790764250481435862261 6486730384148482634612087)
    ·
      refine ⟨9730095576222723951918131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6486730384148482634612087 9730095576222723951918131)
      ·
        refine ⟨14595143364334085927877197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9730095576222723951918131 14595143364334085927877197)
        ·
          refine ⟨5473178761625282222953949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14595143364334085927877197 5473178761625282222953949)
          ·
            refine ⟨2052442035609480833607731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5473178761625282222953949 2052442035609480833607731)
            ·
              refine ⟨3078663053414221250411597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2052442035609480833607731 3078663053414221250411597)
              ·
                refine ⟨1154498645030332968904349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3078663053414221250411597 1154498645030332968904349)
                ·
                  refine ⟨432936991886374863339131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1154498645030332968904349 432936991886374863339131)
                  ·
                    rfl

theorem cell21_1897069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 1, 3, 3].length) (baseStart_1897069 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1897069 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1897069 prefixEnd_1897069 := by exact prefixLift 1897069
  have htrace : WordTrace (prefixWord ++ tailWord_1897069) baseStart_1897069 baseEnd_1897069 := by
    simpa [prefixWord, tailWord_1897069, baseEnd_1897069] using wordTrace_append hprefix tailTrace_1897069
  have hstable : (prefixWord ++ tailWord_1897069).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1897069).length < 2 ^ (prefixWord ++ tailWord_1897069).sum := by decide
  have hdescent : baseEnd_1897069 < baseStart_1897069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1897069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1897156 : List Nat := [2, 3, 3, 1, 1, 2, 3, 6]
def baseStart_1897156 : Nat := 118140960795 + 1897156 * 2 ^ 59
def prefixEnd_1897156 : Nat := 4983230072969 + 3 ^ 40 * 1897156 * 2
def baseEnd_1897156 : Nat := 144318948823894015129651

theorem tailTrace_1897156 : CollatzResearch.WordTrace tailWord_1897156 prefixEnd_1897156 144318948823894015129651 := by
  unfold tailWord_1897156
  simp only [CollatzResearch.WordTrace]
  refine ⟨34597481957467647647139661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46129975943290196862852881 34597481957467647647139661)
  ·
    refine ⟨12974055734050367867677373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34597481957467647647139661 12974055734050367867677373)
    ·
      refine ⟨4865270900268887950379015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12974055734050367867677373 4865270900268887950379015)
      ·
        refine ⟨7297906350403331925568523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4865270900268887950379015 7297906350403331925568523)
        ·
          refine ⟨10946859525604997888352785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7297906350403331925568523 10946859525604997888352785)
          ·
            refine ⟨8210144644203748416264589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10946859525604997888352785 8210144644203748416264589)
            ·
              refine ⟨3078804241576405656099221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8210144644203748416264589 3078804241576405656099221)
              ·
                refine ⟨144318948823894015129651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3078804241576405656099221 144318948823894015129651)
                ·
                  rfl

theorem cell21_1897156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 3, 6].length) (baseStart_1897156 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1897156 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1897156 prefixEnd_1897156 := by exact prefixLift 1897156
  have htrace : WordTrace (prefixWord ++ tailWord_1897156) baseStart_1897156 baseEnd_1897156 := by
    simpa [prefixWord, tailWord_1897156, baseEnd_1897156] using wordTrace_append hprefix tailTrace_1897156
  have hstable : (prefixWord ++ tailWord_1897156).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1897156).length < 2 ^ (prefixWord ++ tailWord_1897156).sum := by decide
  have hdescent : baseEnd_1897156 < baseStart_1897156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1897156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1897184 : List Nat := [2, 1, 1, 3, 1, 2, 1, 4, 6]
def baseStart_1897184 : Nat := 118140960795 + 1897184 * 2 ^ 59
def prefixEnd_1897184 : Nat := 4983230072969 + 3 ^ 40 * 1897184 * 2
def baseEnd_1897184 : Nat := 432963236453160218922229

theorem tailTrace_1897184 : CollatzResearch.WordTrace tailWord_1897184 prefixEnd_1897184 432963236453160218922229 := by
  unfold tailWord_1897184
  simp only [CollatzResearch.WordTrace]
  refine ⟨34597992579416928038149303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46130656772555904050865737 34597992579416928038149303)
  ·
    refine ⟨51896988869125392057223955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34597992579416928038149303 51896988869125392057223955)
    ·
      refine ⟨77845483303688088085835933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51896988869125392057223955 77845483303688088085835933)
      ·
        refine ⟨29192056238883033032188475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77845483303688088085835933 29192056238883033032188475)
        ·
          refine ⟨43788084358324549548282713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29192056238883033032188475 43788084358324549548282713)
          ·
            refine ⟨32841063268743412161212035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43788084358324549548282713 32841063268743412161212035)
            ·
              refine ⟨49261594903115118241818053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32841063268743412161212035 49261594903115118241818053)
              ·
                refine ⟨9236549044334084670340885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49261594903115118241818053 9236549044334084670340885)
                ·
                  refine ⟨432963236453160218922229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9236549044334084670340885 432963236453160218922229)
                  ·
                    rfl

theorem cell21_1897184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 4, 6].length) (baseStart_1897184 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1897184 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1897184 prefixEnd_1897184 := by exact prefixLift 1897184
  have htrace : WordTrace (prefixWord ++ tailWord_1897184) baseStart_1897184 baseEnd_1897184 := by
    simpa [prefixWord, tailWord_1897184, baseEnd_1897184] using wordTrace_append hprefix tailTrace_1897184
  have hstable : (prefixWord ++ tailWord_1897184).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1897184).length < 2 ^ (prefixWord ++ tailWord_1897184).sum := by decide
  have hdescent : baseEnd_1897184 < baseStart_1897184 := by decide
  rcases family_descends (prefixWord ++ tailWord_1897184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1897260 : List Nat := [2, 2, 1, 1, 1, 4, 1, 3, 6]
def baseStart_1897260 : Nat := 118140960795 + 1897260 * 2 ^ 59
def prefixEnd_1897260 : Nat := 4983230072969 + 3 ^ 40 * 1897260 * 2
def baseEnd_1897260 : Nat := 432980580688600975655407

theorem tailTrace_1897260 : CollatzResearch.WordTrace tailWord_1897260 prefixEnd_1897260 432980580688600975655407 := by
  unfold tailWord_1897260
  simp only [CollatzResearch.WordTrace]
  refine ⟨34599378553279260528032617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46132504737705680704043489 34599378553279260528032617)
  ·
    refine ⟨25949533914959445396024463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34599378553279260528032617 25949533914959445396024463)
    ·
      refine ⟨38924300872439168094036695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25949533914959445396024463 38924300872439168094036695)
      ·
        refine ⟨58386451308658752141055043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38924300872439168094036695 58386451308658752141055043)
        ·
          refine ⟨87579676962988128211582565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58386451308658752141055043 87579676962988128211582565)
          ·
            refine ⟨16421189430560274039671731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87579676962988128211582565 16421189430560274039671731)
            ·
              refine ⟨24631784145840411059507597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16421189430560274039671731 24631784145840411059507597)
              ·
                refine ⟨9236919054690154147315349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24631784145840411059507597 9236919054690154147315349)
                ·
                  refine ⟨432980580688600975655407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9236919054690154147315349 432980580688600975655407)
                  ·
                    rfl

theorem cell21_1897260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 6].length) (baseStart_1897260 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1897260 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1897260 prefixEnd_1897260 := by exact prefixLift 1897260
  have htrace : WordTrace (prefixWord ++ tailWord_1897260) baseStart_1897260 baseEnd_1897260 := by
    simpa [prefixWord, tailWord_1897260, baseEnd_1897260] using wordTrace_append hprefix tailTrace_1897260
  have hstable : (prefixWord ++ tailWord_1897260).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1897260).length < 2 ^ (prefixWord ++ tailWord_1897260).sum := by decide
  have hdescent : baseEnd_1897260 < baseStart_1897260 := by decide
  rcases family_descends (prefixWord ++ tailWord_1897260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1897314 : List Nat := [3, 3, 2, 1, 3, 2, 2, 2, 3]
def baseStart_1897314 : Nat := 118140960795 + 1897314 * 2 ^ 59
def prefixEnd_1897314 : Nat := 4983230072969 + 3 ^ 40 * 1897314 * 2
def baseEnd_1897314 : Nat := 432992904224308881755297

theorem tailTrace_1897314 : CollatzResearch.WordTrace tailWord_1897314 prefixEnd_1897314 432992904224308881755297 := by
  unfold tailWord_1897314
  simp only [CollatzResearch.WordTrace]
  refine ⟨17300181662090722069632749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46133817765575258852353997 17300181662090722069632749)
  ·
    refine ⟨6487568123284020776112281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17300181662090722069632749 6487568123284020776112281)
    ·
      refine ⟨4865676092463015582084211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6487568123284020776112281 4865676092463015582084211)
      ·
        refine ⟨7298514138694523373126317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4865676092463015582084211 7298514138694523373126317)
        ·
          refine ⟨2736942802010446264922369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7298514138694523373126317 2736942802010446264922369)
          ·
            refine ⟨2052707101507834698691777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2736942802010446264922369 2052707101507834698691777)
            ·
              refine ⟨1539530326130876024018833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2052707101507834698691777 1539530326130876024018833)
              ·
                refine ⟨1154647744598157018014125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1539530326130876024018833 1154647744598157018014125)
                ·
                  refine ⟨432992904224308881755297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1154647744598157018014125 432992904224308881755297)
                  ·
                    rfl

theorem cell21_1897314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 2, 2, 3].length) (baseStart_1897314 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1897314 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1897314 prefixEnd_1897314 := by exact prefixLift 1897314
  have htrace : WordTrace (prefixWord ++ tailWord_1897314) baseStart_1897314 baseEnd_1897314 := by
    simpa [prefixWord, tailWord_1897314, baseEnd_1897314] using wordTrace_append hprefix tailTrace_1897314
  have hstable : (prefixWord ++ tailWord_1897314).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1897314).length < 2 ^ (prefixWord ++ tailWord_1897314).sum := by decide
  have hdescent : baseEnd_1897314 < baseStart_1897314 := by decide
  rcases family_descends (prefixWord ++ tailWord_1897314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1897342 : List Nat := [4, 2, 3, 1, 2, 1, 3, 5]
def baseStart_1897342 : Nat := 118140960795 + 1897342 * 2 ^ 59
def prefixEnd_1897342 : Nat := 4983230072969 + 3 ^ 40 * 1897342 * 2
def baseEnd_1897342 : Nat := 144333098068595685096191

theorem tailTrace_1897342 : CollatzResearch.WordTrace tailWord_1897342 prefixEnd_1897342 144333098068595685096191 := by
  unfold tailWord_1897342
  simp only [CollatzResearch.WordTrace]
  refine ⟨8650218486532681132568785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46134498594840966040366853 8650218486532681132568785)
  ·
    refine ⟨6487663864899510849426589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8650218486532681132568785 6487663864899510849426589)
    ·
      refine ⟨2432873949337316568534971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6487663864899510849426589 2432873949337316568534971)
      ·
        refine ⟨3649310924005974852802457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2432873949337316568534971 3649310924005974852802457)
        ·
          refine ⟨2736983193004481139601843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3649310924005974852802457 2736983193004481139601843)
          ·
            refine ⟨4105474789506721709402765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2736983193004481139601843 4105474789506721709402765)
            ·
              refine ⟨1539553046065020641026037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4105474789506721709402765 1539553046065020641026037)
              ·
                refine ⟨144333098068595685096191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1539553046065020641026037 144333098068595685096191)
                ·
                  rfl

theorem cell21_1897342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 3, 5].length) (baseStart_1897342 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1897342 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1897342 prefixEnd_1897342 := by exact prefixLift 1897342
  have htrace : WordTrace (prefixWord ++ tailWord_1897342) baseStart_1897342 baseEnd_1897342 := by
    simpa [prefixWord, tailWord_1897342, baseEnd_1897342] using wordTrace_append hprefix tailTrace_1897342
  have hstable : (prefixWord ++ tailWord_1897342).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1897342).length < 2 ^ (prefixWord ++ tailWord_1897342).sum := by decide
  have hdescent : baseEnd_1897342 < baseStart_1897342 := by decide
  rcases family_descends (prefixWord ++ tailWord_1897342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1897415 : List Nat := [1, 1, 4, 1, 1, 2, 5, 3, 3]
def baseStart_1897415 : Nat := 118140960795 + 1897415 * 2 ^ 59
def prefixEnd_1897415 : Nat := 4983230072969 + 3 ^ 40 * 1897415 * 2
def baseEnd_1897415 : Nat := 433015953800355150571757

theorem tailTrace_1897415 : CollatzResearch.WordTrace tailWord_1897415 prefixEnd_1897415 433015953800355150571757 := by
  unfold tailWord_1897415
  simp only [CollatzResearch.WordTrace]
  refine ⟨69204410420996982527957699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46136273613997988351971799 69204410420996982527957699)
  ·
    refine ⟨103806615631495473791936549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69204410420996982527957699 103806615631495473791936549)
    ·
      refine ⟨19463740430905401335988103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103806615631495473791936549 19463740430905401335988103)
      ·
        refine ⟨29195610646358102003982155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19463740430905401335988103 29195610646358102003982155)
        ·
          refine ⟨43793415969537153005973233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29195610646358102003982155 43793415969537153005973233)
          ·
            refine ⟨32845061977152864754479925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43793415969537153005973233 32845061977152864754479925)
            ·
              refine ⟨3079224560358081070732493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32845061977152864754479925 3079224560358081070732493)
              ·
                refine ⟨1154709210134280401524685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3079224560358081070732493 1154709210134280401524685)
                ·
                  refine ⟨433015953800355150571757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1154709210134280401524685 433015953800355150571757)
                  ·
                    rfl

theorem cell21_1897415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 5, 3, 3].length) (baseStart_1897415 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1897415 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1897415 prefixEnd_1897415 := by exact prefixLift 1897415
  have htrace : WordTrace (prefixWord ++ tailWord_1897415) baseStart_1897415 baseEnd_1897415 := by
    simpa [prefixWord, tailWord_1897415, baseEnd_1897415] using wordTrace_append hprefix tailTrace_1897415
  have hstable : (prefixWord ++ tailWord_1897415).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1897415).length < 2 ^ (prefixWord ++ tailWord_1897415).sum := by decide
  have hdescent : baseEnd_1897415 < baseStart_1897415 := by decide
  rcases family_descends (prefixWord ++ tailWord_1897415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1897432 : List Nat := [2, 1, 2, 2, 2, 4, 3, 2, 3]
def baseStart_1897432 : Nat := 118140960795 + 1897432 * 2 ^ 59
def prefixEnd_1897432 : Nat := 4983230072969 + 3 ^ 40 * 1897432 * 2
def baseEnd_1897432 : Nat := 433019833431966898788389

theorem tailTrace_1897432 : CollatzResearch.WordTrace tailWord_1897432 prefixEnd_1897432 433019833431966898788389 := by
  unfold tailWord_1897432
  simp only [CollatzResearch.WordTrace]
  refine ⟨34602515230967697215663275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46136686974623596287551033 34602515230967697215663275)
  ·
    refine ⟨51903772846451545823494913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34602515230967697215663275 51903772846451545823494913)
    ·
      refine ⟨38927829634838659367621185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51903772846451545823494913 38927829634838659367621185)
      ·
        refine ⟨29195872226128994525715889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38927829634838659367621185 29195872226128994525715889)
        ·
          refine ⟨21896904169596745894286917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29195872226128994525715889 21896904169596745894286917)
          ·
            refine ⟨4105669531799389855178797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21896904169596745894286917 4105669531799389855178797)
            ·
              refine ⟨1539626074424771195692049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4105669531799389855178797 1539626074424771195692049)
              ·
                refine ⟨1154719555818578396769037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1539626074424771195692049 1154719555818578396769037)
                ·
                  refine ⟨433019833431966898788389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1154719555818578396769037 433019833431966898788389)
                  ·
                    rfl

theorem cell21_1897432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 3, 2, 3].length) (baseStart_1897432 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1897432 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1897432 prefixEnd_1897432 := by exact prefixLift 1897432
  have htrace : WordTrace (prefixWord ++ tailWord_1897432) baseStart_1897432 baseEnd_1897432 := by
    simpa [prefixWord, tailWord_1897432, baseEnd_1897432] using wordTrace_append hprefix tailTrace_1897432
  have hstable : (prefixWord ++ tailWord_1897432).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1897432).length < 2 ^ (prefixWord ++ tailWord_1897432).sum := by decide
  have hdescent : baseEnd_1897432 < baseStart_1897432 := by decide
  rcases family_descends (prefixWord ++ tailWord_1897432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1897443 : List Nat := [1, 1, 1, 6, 1, 1, 4, 6]
def baseStart_1897443 : Nat := 118140960795 + 1897443 * 2 ^ 59
def prefixEnd_1897443 : Nat := 4983230072969 + 3 ^ 40 * 1897443 * 2
def baseEnd_1897443 : Nat := 144340781260611108035011

theorem tailTrace_1897443 : CollatzResearch.WordTrace tailWord_1897443 prefixEnd_1897443 144340781260611108035011 := by
  unfold tailWord_1897443
  simp only [CollatzResearch.WordTrace]
  refine ⟨69205431664895543309976983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46136954443263695539984655 69205431664895543309976983)
  ·
    refine ⟨103808147497343314964965475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69205431664895543309976983 103808147497343314964965475)
    ·
      refine ⟨155712221246014972447448213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103808147497343314964965475 155712221246014972447448213)
      ·
        refine ⟨7299010370906951833474135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 155712221246014972447448213 7299010370906951833474135)
        ·
          refine ⟨10948515556360427750211203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7299010370906951833474135 10948515556360427750211203)
          ·
            refine ⟨16422773334540641625316805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10948515556360427750211203 16422773334540641625316805)
            ·
              refine ⟨3079270000226370304746901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16422773334540641625316805 3079270000226370304746901)
              ·
                refine ⟨144340781260611108035011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3079270000226370304746901 144340781260611108035011)
                ·
                  rfl

theorem cell21_1897443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 4, 6].length) (baseStart_1897443 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1897443 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1897443 prefixEnd_1897443 := by exact prefixLift 1897443
  have htrace : WordTrace (prefixWord ++ tailWord_1897443) baseStart_1897443 baseEnd_1897443 := by
    simpa [prefixWord, tailWord_1897443, baseEnd_1897443] using wordTrace_append hprefix tailTrace_1897443
  have hstable : (prefixWord ++ tailWord_1897443).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1897443).length < 2 ^ (prefixWord ++ tailWord_1897443).sum := by decide
  have hdescent : baseEnd_1897443 < baseStart_1897443 := by decide
  rcases family_descends (prefixWord ++ tailWord_1897443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1897505 : List Nat := [1, 2, 3, 2, 3, 1, 2, 3, 4]
def baseStart_1897505 : Nat := 118140960795 + 1897505 * 2 ^ 59
def prefixEnd_1897505 : Nat := 4983230072969 + 3 ^ 40 * 1897505 * 2
def baseEnd_1897505 : Nat := 433036493026534994071573

theorem tailTrace_1897505 : CollatzResearch.WordTrace tailWord_1897505 prefixEnd_1897505 433036493026534994071573 := by
  unfold tailWord_1897505
  simp only [CollatzResearch.WordTrace]
  refine ⟨69207692990670927898733969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46138461993780618599155979 69207692990670927898733969)
  ·
    refine ⟨51905769743003195924050477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69207692990670927898733969 51905769743003195924050477)
    ·
      refine ⟨19464663653626198471518929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51905769743003195924050477 19464663653626198471518929)
      ·
        refine ⟨14598497740219648853639197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19464663653626198471518929 14598497740219648853639197)
        ·
          refine ⟨5474436652582368320114699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14598497740219648853639197 5474436652582368320114699)
          ·
            refine ⟨8211654978873552480172049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5474436652582368320114699 8211654978873552480172049)
            ·
              refine ⟨6158741234155164360129037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8211654978873552480172049 6158741234155164360129037)
              ·
                refine ⟨2309527962808186635048389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6158741234155164360129037 2309527962808186635048389)
                ·
                  refine ⟨433036493026534994071573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2309527962808186635048389 433036493026534994071573)
                  ·
                    rfl

theorem cell21_1897505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 3, 4].length) (baseStart_1897505 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1897505 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1897505 prefixEnd_1897505 := by exact prefixLift 1897505
  have htrace : WordTrace (prefixWord ++ tailWord_1897505) baseStart_1897505 baseEnd_1897505 := by
    simpa [prefixWord, tailWord_1897505, baseEnd_1897505] using wordTrace_append hprefix tailTrace_1897505
  have hstable : (prefixWord ++ tailWord_1897505).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1897505).length < 2 ^ (prefixWord ++ tailWord_1897505).sum := by decide
  have hdescent : baseEnd_1897505 < baseStart_1897505 := by decide
  rcases family_descends (prefixWord ++ tailWord_1897505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1897550 : List Nat := [4, 1, 1, 1, 1, 3, 4, 1, 5]
def baseStart_1897550 : Nat := 118140960795 + 1897550 * 2 ^ 59
def prefixEnd_1897550 : Nat := 4983230072969 + 3 ^ 40 * 1897550 * 2
def baseEnd_1897550 : Nat := 433046762639624915821481

theorem tailTrace_1897550 : CollatzResearch.WordTrace tailWord_1897550 prefixEnd_1897550 433046762639624915821481 := by
  unfold tailWord_1897550
  simp only [CollatzResearch.WordTrace]
  refine ⟨8651166784438487573015263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46139556183671933722748069 8651166784438487573015263)
  ·
    refine ⟨12976750176657731359522895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8651166784438487573015263 12976750176657731359522895)
    ·
      refine ⟨19465125264986597039284343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12976750176657731359522895 19465125264986597039284343)
      ·
        refine ⟨29197687897479895558926515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19465125264986597039284343 29197687897479895558926515)
        ·
          refine ⟨43796531846219843338389773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29197687897479895558926515 43796531846219843338389773)
          ·
            refine ⟨16423699442332441251896165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43796531846219843338389773 16423699442332441251896165)
            ·
              refine ⟨3079443645437332734730531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16423699442332441251896165 3079443645437332734730531)
              ·
                refine ⟨4619165468155999102095797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3079443645437332734730531 4619165468155999102095797)
                ·
                  refine ⟨433046762639624915821481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4619165468155999102095797 433046762639624915821481)
                  ·
                    rfl

theorem cell21_1897550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 4, 1, 5].length) (baseStart_1897550 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1897550 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1897550 prefixEnd_1897550 := by exact prefixLift 1897550
  have htrace : WordTrace (prefixWord ++ tailWord_1897550) baseStart_1897550 baseEnd_1897550 := by
    simpa [prefixWord, tailWord_1897550, baseEnd_1897550] using wordTrace_append hprefix tailTrace_1897550
  have hstable : (prefixWord ++ tailWord_1897550).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1897550).length < 2 ^ (prefixWord ++ tailWord_1897550).sum := by decide
  have hdescent : baseEnd_1897550 < baseStart_1897550 := by decide
  rcases family_descends (prefixWord ++ tailWord_1897550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1897657 : List Nat := [1, 2, 1, 4, 1, 4, 2, 2, 4]
def baseStart_1897657 : Nat := 118140960795 + 1897657 * 2 ^ 59
def prefixEnd_1897657 : Nat := 4983230072969 + 3 ^ 40 * 1897657 * 2
def baseEnd_1897657 : Nat := 433071181497416507537929

theorem tailTrace_1897657 : CollatzResearch.WordTrace tailWord_1897657 prefixEnd_1897657 433071181497416507537929 := by
  unfold tailWord_1897657
  simp only [CollatzResearch.WordTrace]
  refine ⟨69213236886120257858267225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46142157924080171905511483 69213236886120257858267225)
  ·
    refine ⟨51909927664590193393700419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69213236886120257858267225 51909927664590193393700419)
    ·
      refine ⟨77864891496885290090550629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51909927664590193393700419 77864891496885290090550629)
      ·
        refine ⟨14599667155665991891978243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77864891496885290090550629 14599667155665991891978243)
        ·
          refine ⟨21899500733498987837967365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14599667155665991891978243 21899500733498987837967365)
          ·
            refine ⟨4106156387531060219618881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21899500733498987837967365 4106156387531060219618881)
            ·
              refine ⟨3079617290648295164714161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4106156387531060219618881 3079617290648295164714161)
              ·
                refine ⟨2309712967986221373535621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3079617290648295164714161 2309712967986221373535621)
                ·
                  refine ⟨433071181497416507537929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2309712967986221373535621 433071181497416507537929)
                  ·
                    rfl

theorem cell21_1897657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 2, 2, 4].length) (baseStart_1897657 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1897657 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1897657 prefixEnd_1897657 := by exact prefixLift 1897657
  have htrace : WordTrace (prefixWord ++ tailWord_1897657) baseStart_1897657 baseEnd_1897657 := by
    simpa [prefixWord, tailWord_1897657, baseEnd_1897657] using wordTrace_append hprefix tailTrace_1897657
  have hstable : (prefixWord ++ tailWord_1897657).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1897657).length < 2 ^ (prefixWord ++ tailWord_1897657).sum := by decide
  have hdescent : baseEnd_1897657 < baseStart_1897657 := by decide
  rcases family_descends (prefixWord ++ tailWord_1897657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1897660 : List Nat := [2, 2, 2, 3, 2, 1, 4, 2, 3]
def baseStart_1897660 : Nat := 118140960795 + 1897660 * 2 ^ 59
def prefixEnd_1897660 : Nat := 4983230072969 + 3 ^ 40 * 1897660 * 2
def baseEnd_1897660 : Nat := 433071866138289168987923

theorem tailTrace_1897660 : CollatzResearch.WordTrace tailWord_1897660 prefixEnd_1897660 433071866138289168987923 := by
  unfold tailWord_1897660
  simp only [CollatzResearch.WordTrace]
  refine ⟨34606673152554694685313217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46142230870072926247084289 34606673152554694685313217)
  ·
    refine ⟨25955004864416021013984913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34606673152554694685313217 25955004864416021013984913)
    ·
      refine ⟨19466253648312015760488685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25955004864416021013984913 19466253648312015760488685)
      ·
        refine ⟨7299845118117005910183257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19466253648312015760488685 7299845118117005910183257)
        ·
          refine ⟨5474883838587754432637443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7299845118117005910183257 5474883838587754432637443)
          ·
            refine ⟨8212325757881631648956165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5474883838587754432637443 8212325757881631648956165)
            ·
              refine ⟨1539811079602805934179281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8212325757881631648956165 1539811079602805934179281)
              ·
                refine ⟨1154858309702104450634461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1539811079602805934179281 1154858309702104450634461)
                ·
                  refine ⟨433071866138289168987923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1154858309702104450634461 433071866138289168987923)
                  ·
                    rfl

theorem cell21_1897660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 4, 2, 3].length) (baseStart_1897660 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1897660 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1897660 prefixEnd_1897660 := by exact prefixLift 1897660
  have htrace : WordTrace (prefixWord ++ tailWord_1897660) baseStart_1897660 baseEnd_1897660 := by
    simpa [prefixWord, tailWord_1897660, baseEnd_1897660] using wordTrace_append hprefix tailTrace_1897660
  have hstable : (prefixWord ++ tailWord_1897660).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1897660).length < 2 ^ (prefixWord ++ tailWord_1897660).sum := by decide
  have hdescent : baseEnd_1897660 < baseStart_1897660 := by decide
  rcases family_descends (prefixWord ++ tailWord_1897660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1897688 : List Nat := [2, 1, 2, 2, 5, 1, 3, 5]
def baseStart_1897688 : Nat := 118140960795 + 1897688 * 2 ^ 59
def prefixEnd_1897688 : Nat := 4983230072969 + 3 ^ 40 * 1897688 * 2
def baseEnd_1897688 : Nat := 144359418706589114173733

theorem tailTrace_1897688 : CollatzResearch.WordTrace tailWord_1897688 prefixEnd_1897688 144359418706589114173733 := by
  unfold tailWord_1897688
  simp only [CollatzResearch.WordTrace]
  refine ⟨34607183774503975076322859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46142911699338633435097145 34607183774503975076322859)
  ·
    refine ⟨51910775661755962614484289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34607183774503975076322859 51910775661755962614484289)
    ·
      refine ⟨38933081746316971960863217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51910775661755962614484289 38933081746316971960863217)
      ·
        refine ⟨29199811309737728970647413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38933081746316971960863217 29199811309737728970647413)
        ·
          refine ⟨2737482310287912090998195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29199811309737728970647413 2737482310287912090998195)
          ·
            refine ⟨4106223465431868136497293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2737482310287912090998195 4106223465431868136497293)
            ·
              refine ⟨1539833799536950551186485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4106223465431868136497293 1539833799536950551186485)
              ·
                refine ⟨144359418706589114173733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1539833799536950551186485 144359418706589114173733)
                ·
                  rfl

theorem cell21_1897688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 3, 5].length) (baseStart_1897688 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1897688 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1897688 prefixEnd_1897688 := by exact prefixLift 1897688
  have htrace : WordTrace (prefixWord ++ tailWord_1897688) baseStart_1897688 baseEnd_1897688 := by
    simpa [prefixWord, tailWord_1897688, baseEnd_1897688] using wordTrace_append hprefix tailTrace_1897688
  have hstable : (prefixWord ++ tailWord_1897688).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1897688).length < 2 ^ (prefixWord ++ tailWord_1897688).sum := by decide
  have hdescent : baseEnd_1897688 < baseStart_1897688 := by decide
  rcases family_descends (prefixWord ++ tailWord_1897688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1897733 : List Nat := [1, 3, 1, 1, 2, 1, 7, 1, 4]
def baseStart_1897733 : Nat := 118140960795 + 1897733 * 2 ^ 59
def prefixEnd_1897733 : Nat := 4983230072969 + 3 ^ 40 * 1897733 * 2
def baseEnd_1897733 : Nat := 433088525732857264271107

theorem tailTrace_1897733 : CollatzResearch.WordTrace tailWord_1897733 prefixEnd_1897733 433088525732857264271107 := by
  unfold tailWord_1897733
  simp only [CollatzResearch.WordTrace]
  refine ⟨69216008833844922838033853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46144005889229948558689235 69216008833844922838033853)
  ·
    refine ⟨25956003312691846064262695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69216008833844922838033853 25956003312691846064262695)
    ·
      refine ⟨38934004969037769096394043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25956003312691846064262695 38934004969037769096394043)
      ·
        refine ⟨58401007453556653644591065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38934004969037769096394043 58401007453556653644591065)
        ·
          refine ⟨43800755590167490233443299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58401007453556653644591065 43800755590167490233443299)
          ·
            refine ⟨65701133385251235350164949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43800755590167490233443299 65701133385251235350164949)
            ·
              refine ⟨1539870313716825828519491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 65701133385251235350164949 1539870313716825828519491)
              ·
                refine ⟨2309805470575238742779237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1539870313716825828519491 2309805470575238742779237)
                ·
                  refine ⟨433088525732857264271107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2309805470575238742779237 433088525732857264271107)
                  ·
                    rfl

theorem cell21_1897733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 7, 1, 4].length) (baseStart_1897733 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1897733 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1897733 prefixEnd_1897733 := by exact prefixLift 1897733
  have htrace : WordTrace (prefixWord ++ tailWord_1897733) baseStart_1897733 baseEnd_1897733 := by
    simpa [prefixWord, tailWord_1897733, baseEnd_1897733] using wordTrace_append hprefix tailTrace_1897733
  have hstable : (prefixWord ++ tailWord_1897733).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1897733).length < 2 ^ (prefixWord ++ tailWord_1897733).sum := by decide
  have hdescent : baseEnd_1897733 < baseStart_1897733 := by decide
  rcases family_descends (prefixWord ++ tailWord_1897733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1897778 : List Nat := [3, 2, 1, 1, 4, 1, 3, 1, 5]
def baseStart_1897778 : Nat := 118140960795 + 1897778 * 2 ^ 59
def prefixEnd_1897778 : Nat := 4983230072969 + 3 ^ 40 * 1897778 * 2
def baseEnd_1897778 : Nat := 433098795345947186021015

theorem tailTrace_1897778 : CollatzResearch.WordTrace tailWord_1897778 prefixEnd_1897778 433098795345947186021015 := by
  unfold tailWord_1897778
  simp only [CollatzResearch.WordTrace]
  refine ⟨17304412529670473880855497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46145100079121263682281325 17304412529670473880855497)
  ·
    refine ⟨12978309397252855410641623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17304412529670473880855497 12978309397252855410641623)
    ·
      refine ⟨19467464095879283115962435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12978309397252855410641623 19467464095879283115962435)
      ·
        refine ⟨29201196143818924673943653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19467464095879283115962435 29201196143818924673943653)
        ·
          refine ⟨5475224276966048376364435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29201196143818924673943653 5475224276966048376364435)
          ·
            refine ⟨8212836415449072564546653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5475224276966048376364435 8212836415449072564546653)
            ·
              refine ⟨3079813655793402211704995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8212836415449072564546653 3079813655793402211704995)
              ·
                refine ⟨4619720483690103317557493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3079813655793402211704995 4619720483690103317557493)
                ·
                  refine ⟨433098795345947186021015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4619720483690103317557493 433098795345947186021015)
                  ·
                    rfl

theorem cell21_1897778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 3, 1, 5].length) (baseStart_1897778 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1897778 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1897778 prefixEnd_1897778 := by exact prefixLift 1897778
  have htrace : WordTrace (prefixWord ++ tailWord_1897778) baseStart_1897778 baseEnd_1897778 := by
    simpa [prefixWord, tailWord_1897778, baseEnd_1897778] using wordTrace_append hprefix tailTrace_1897778
  have hstable : (prefixWord ++ tailWord_1897778).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1897778).length < 2 ^ (prefixWord ++ tailWord_1897778).sum := by decide
  have hdescent : baseEnd_1897778 < baseStart_1897778 := by decide
  rcases family_descends (prefixWord ++ tailWord_1897778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1897792 : List Nat := [2, 1, 1, 2, 2, 1, 5, 3, 4]
def baseStart_1897792 : Nat := 118140960795 + 1897792 * 2 ^ 59
def prefixEnd_1897792 : Nat := 4983230072969 + 3 ^ 40 * 1897792 * 2
def baseEnd_1897792 : Nat := 433101990336686272787653

theorem tailTrace_1897792 : CollatzResearch.WordTrace tailWord_1897792 prefixEnd_1897792 433101990336686272787653 := by
  unfold tailWord_1897792
  simp only [CollatzResearch.WordTrace]
  refine ⟨34609080370315587957215815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46145440493754117276287753 34609080370315587957215815)
  ·
    refine ⟨51913620555473381935823723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34609080370315587957215815 51913620555473381935823723)
    ·
      refine ⟨77870430833210072903735585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51913620555473381935823723 77870430833210072903735585)
      ·
        refine ⟨58402823124907554677801689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77870430833210072903735585 58402823124907554677801689)
        ·
          refine ⟨43802117343680666008351267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58402823124907554677801689 43802117343680666008351267)
          ·
            refine ⟨65703176015520999012526901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43802117343680666008351267 65703176015520999012526901)
            ·
              refine ⟨6159672751455093657424397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65703176015520999012526901 6159672751455093657424397)
              ·
                refine ⟨2309877281795660121534149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6159672751455093657424397 2309877281795660121534149)
                ·
                  refine ⟨433101990336686272787653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2309877281795660121534149 433101990336686272787653)
                  ·
                    rfl

theorem cell21_1897792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 3, 4].length) (baseStart_1897792 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1897792 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1897792 prefixEnd_1897792 := by exact prefixLift 1897792
  have htrace : WordTrace (prefixWord ++ tailWord_1897792) baseStart_1897792 baseEnd_1897792 := by
    simpa [prefixWord, tailWord_1897792, baseEnd_1897792] using wordTrace_append hprefix tailTrace_1897792
  have hstable : (prefixWord ++ tailWord_1897792).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1897792).length < 2 ^ (prefixWord ++ tailWord_1897792).sum := by decide
  have hdescent : baseEnd_1897792 < baseStart_1897792 := by decide
  rcases family_descends (prefixWord ++ tailWord_1897792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1897806 : List Nat := [4, 1, 1, 1, 1, 1, 3, 9]
def baseStart_1897806 : Nat := 118140960795 + 1897806 * 2 ^ 59
def prefixEnd_1897806 : Nat := 4983230072969 + 3 ^ 40 * 1897806 * 2
def baseEnd_1897806 : Nat := 144368395109141786518097

theorem tailTrace_1897806 : CollatzResearch.WordTrace tailWord_1897806 prefixEnd_1897806 144368395109141786518097 := by
  unfold tailWord_1897806
  simp only [CollatzResearch.WordTrace]
  refine ⟨8652333920322557038180159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46145780908386970870294181 8652333920322557038180159)
  ·
    refine ⟨12978500880483835557270239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8652333920322557038180159 12978500880483835557270239)
    ·
      refine ⟨19467751320725753335905359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12978500880483835557270239 19467751320725753335905359)
      ·
        refine ⟨29201626981088630003858039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19467751320725753335905359 29201626981088630003858039)
        ·
          refine ⟨43802440471632945005787059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29201626981088630003858039 43802440471632945005787059)
          ·
            refine ⟨65703660707449417508680589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43802440471632945005787059 65703660707449417508680589)
            ·
              refine ⟨24638872765293531565755221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65703660707449417508680589 24638872765293531565755221)
              ·
                refine ⟨144368395109141786518097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24638872765293531565755221 144368395109141786518097)
                ·
                  rfl

theorem cell21_1897806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 9].length) (baseStart_1897806 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1897806 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1897806 prefixEnd_1897806 := by exact prefixLift 1897806
  have htrace : WordTrace (prefixWord ++ tailWord_1897806) baseStart_1897806 baseEnd_1897806 := by
    simpa [prefixWord, tailWord_1897806, baseEnd_1897806] using wordTrace_append hprefix tailTrace_1897806
  have hstable : (prefixWord ++ tailWord_1897806).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1897806).length < 2 ^ (prefixWord ++ tailWord_1897806).sum := by decide
  have hdescent : baseEnd_1897806 < baseStart_1897806 := by decide
  rcases family_descends (prefixWord ++ tailWord_1897806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1897882 : List Nat := [3, 1, 1, 4, 1, 1, 10]
def baseStart_1897882 : Nat := 118140960795 + 1897882 * 2 ^ 59
def prefixEnd_1897882 : Nat := 4983230072969 + 3 ^ 40 * 1897882 * 2
def baseEnd_1897882 : Nat := 48124725506985124031941

theorem tailTrace_1897882 : CollatzResearch.WordTrace tailWord_1897882 prefixEnd_1897882 48124725506985124031941 := by
  unfold tailWord_1897882
  simp only [CollatzResearch.WordTrace]
  refine ⟨17305360827576280321301975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46147628873536747523471933 17305360827576280321301975)
  ·
    refine ⟨25958041241364420481952963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17305360827576280321301975 25958041241364420481952963)
    ·
      refine ⟨38937061862046630722929445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25958041241364420481952963 38937061862046630722929445)
      ·
        refine ⟨7300699099133743260549271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38937061862046630722929445 7300699099133743260549271)
        ·
          refine ⟨10951048648700614890823907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7300699099133743260549271 10951048648700614890823907)
          ·
            refine ⟨16426572973050922336235861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10951048648700614890823907 16426572973050922336235861)
            ·
              refine ⟨48124725506985124031941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 16426572973050922336235861 48124725506985124031941)
              ·
                rfl

theorem cell21_1897882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 10].length) (baseStart_1897882 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1897882 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1897882 prefixEnd_1897882 := by exact prefixLift 1897882
  have htrace : WordTrace (prefixWord ++ tailWord_1897882) baseStart_1897882 baseEnd_1897882 := by
    simpa [prefixWord, tailWord_1897882, baseEnd_1897882] using wordTrace_append hprefix tailTrace_1897882
  have hstable : (prefixWord ++ tailWord_1897882).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1897882).length < 2 ^ (prefixWord ++ tailWord_1897882).sum := by decide
  have hdescent : baseEnd_1897882 < baseStart_1897882 := by decide
  rcases family_descends (prefixWord ++ tailWord_1897882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1897885 : List Nat := [1, 4, 2, 1, 3, 1, 3, 2, 4]
def baseStart_1897885 : Nat := 118140960795 + 1897885 * 2 ^ 59
def prefixEnd_1897885 : Nat := 4983230072969 + 3 ^ 40 * 1897885 * 2
def baseEnd_1897885 : Nat := 433123214203738777737463

theorem tailTrace_1897885 : CollatzResearch.WordTrace tailWord_1897885 prefixEnd_1897885 433123214203738777737463 := by
  unfold tailWord_1897885
  simp only [CollatzResearch.WordTrace]
  refine ⟨69221552729294252797567109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46147701819529501865044739 69221552729294252797567109)
  ·
    refine ⟨12979041136742672399543833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69221552729294252797567109 12979041136742672399543833)
    ·
      refine ⟨9734280852557004299657875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12979041136742672399543833 9734280852557004299657875)
      ·
        refine ⟨14601421278835506449486813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9734280852557004299657875 14601421278835506449486813)
        ·
          refine ⟨5475532979563314918557555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14601421278835506449486813 5475532979563314918557555)
          ·
            refine ⟨8213299469344972377836333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5475532979563314918557555 8213299469344972377836333)
            ·
              refine ⟨3079987301004364641688625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8213299469344972377836333 3079987301004364641688625)
              ·
                refine ⟨2309990475753273481266469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3079987301004364641688625 2309990475753273481266469)
                ·
                  refine ⟨433123214203738777737463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2309990475753273481266469 433123214203738777737463)
                  ·
                    rfl

theorem cell21_1897885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 3, 2, 4].length) (baseStart_1897885 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1897885 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1897885 prefixEnd_1897885 := by exact prefixLift 1897885
  have htrace : WordTrace (prefixWord ++ tailWord_1897885) baseStart_1897885 baseEnd_1897885 := by
    simpa [prefixWord, tailWord_1897885, baseEnd_1897885] using wordTrace_append hprefix tailTrace_1897885
  have hstable : (prefixWord ++ tailWord_1897885).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1897885).length < 2 ^ (prefixWord ++ tailWord_1897885).sum := by decide
  have hdescent : baseEnd_1897885 < baseStart_1897885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1897885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1897927 : List Nat := [1, 1, 4, 1, 1, 3, 1, 1, 8]
def baseStart_1897927 : Nat := 118140960795 + 1897927 * 2 ^ 59
def prefixEnd_1897927 : Nat := 4983230072969 + 3 ^ 40 * 1897927 * 2
def baseEnd_1897927 : Nat := 433132799175956038037377

theorem tailTrace_1897927 : CollatzResearch.WordTrace tailWord_1897927 prefixEnd_1897927 433132799175956038037377 := by
  unfold tailWord_1897927
  simp only [CollatzResearch.WordTrace]
  refine ⟨69223084595142093970596035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46148723063428062647064023 69223084595142093970596035)
  ·
    refine ⟨103834626892713140955894053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69223084595142093970596035 103834626892713140955894053)
    ·
      refine ⟨19468992542383713929230135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103834626892713140955894053 19468992542383713929230135)
      ·
        refine ⟨29203488813575570893845203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19468992542383713929230135 29203488813575570893845203)
        ·
          refine ⟨43805233220363356340767805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29203488813575570893845203 43805233220363356340767805)
          ·
            refine ⟨16426962457636258627787927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43805233220363356340767805 16426962457636258627787927)
            ·
              refine ⟨24640443686454387941681891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16426962457636258627787927 24640443686454387941681891)
              ·
                refine ⟨36960665529681581912522837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24640443686454387941681891 36960665529681581912522837)
                ·
                  refine ⟨433132799175956038037377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36960665529681581912522837 433132799175956038037377)
                  ·
                    rfl

theorem cell21_1897927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 1, 8].length) (baseStart_1897927 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1897927 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1897927 prefixEnd_1897927 := by exact prefixLift 1897927
  have htrace : WordTrace (prefixWord ++ tailWord_1897927) baseStart_1897927 baseEnd_1897927 := by
    simpa [prefixWord, tailWord_1897927, baseEnd_1897927] using wordTrace_append hprefix tailTrace_1897927
  have hstable : (prefixWord ++ tailWord_1897927).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1897927).length < 2 ^ (prefixWord ++ tailWord_1897927).sum := by decide
  have hdescent : baseEnd_1897927 < baseStart_1897927 := by decide
  rcases family_descends (prefixWord ++ tailWord_1897927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1898048 : List Nat := [2, 1, 1, 2, 2, 2, 1, 1, 9]
def baseStart_1898048 : Nat := 118140960795 + 1898048 * 2 ^ 59
def prefixEnd_1898048 : Nat := 4983230072969 + 3 ^ 40 * 1898048 * 2
def baseEnd_1898048 : Nat := 433160413024486716520463

theorem tailTrace_1898048 : CollatzResearch.WordTrace tailWord_1898048 prefixEnd_1898048 433160413024486716520463 := by
  unfold tailWord_1898048
  simp only [CollatzResearch.WordTrace]
  refine ⟨34613748913851865817875399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46151665218469154423833865 34613748913851865817875399)
  ·
    refine ⟨51920623370777798726813099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34613748913851865817875399 51920623370777798726813099)
    ·
      refine ⟨77880935056166698090219649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51920623370777798726813099 77880935056166698090219649)
      ·
        refine ⟨58410701292125023567664737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77880935056166698090219649 58410701292125023567664737)
        ·
          refine ⟨43808025969093767675748553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58410701292125023567664737 43808025969093767675748553)
          ·
            refine ⟨32856019476820325756811415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43808025969093767675748553 32856019476820325756811415)
            ·
              refine ⟨49284029215230488635217123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32856019476820325756811415 49284029215230488635217123)
              ·
                refine ⟨73926043822845732952825685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49284029215230488635217123 73926043822845732952825685)
                ·
                  refine ⟨433160413024486716520463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 73926043822845732952825685 433160413024486716520463)
                  ·
                    rfl

theorem cell21_1898048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 9].length) (baseStart_1898048 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1898048 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1898048 prefixEnd_1898048 := by exact prefixLift 1898048
  have htrace : WordTrace (prefixWord ++ tailWord_1898048) baseStart_1898048 baseEnd_1898048 := by
    simpa [prefixWord, tailWord_1898048, baseEnd_1898048] using wordTrace_append hprefix tailTrace_1898048
  have hstable : (prefixWord ++ tailWord_1898048).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1898048).length < 2 ^ (prefixWord ++ tailWord_1898048).sum := by decide
  have hdescent : baseEnd_1898048 < baseStart_1898048 := by decide
  rcases family_descends (prefixWord ++ tailWord_1898048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1898054 : List Nat := [6, 1, 1, 1, 3, 1, 1, 1, 6]
def baseStart_1898054 : Nat := 118140960795 + 1898054 * 2 ^ 59
def prefixEnd_1898054 : Nat := 4983230072969 + 3 ^ 40 * 1898054 * 2
def baseEnd_1898054 : Nat := 433161782306232039420451

theorem tailTrace_1898054 : CollatzResearch.WordTrace tailWord_1898054 prefixEnd_1898054 433161782306232039420451 := by
  unfold tailWord_1898054
  simp only [CollatzResearch.WordTrace]
  refine ⟨2163366145802562333139663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 46151811110454663106979477 2163366145802562333139663)
  ·
    refine ⟨3245049218703843499709495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2163366145802562333139663 3245049218703843499709495)
    ·
      refine ⟨4867573828055765249564243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3245049218703843499709495 4867573828055765249564243)
      ·
        refine ⟨7301360742083647874346365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4867573828055765249564243 7301360742083647874346365)
        ·
          refine ⟨2738010278281367952879887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7301360742083647874346365 2738010278281367952879887)
          ·
            refine ⟨4107015417422051929319831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2738010278281367952879887 4107015417422051929319831)
            ·
              refine ⟨6160523126133077893979747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4107015417422051929319831 6160523126133077893979747)
              ·
                refine ⟨9240784689199616840969621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6160523126133077893979747 9240784689199616840969621)
                ·
                  refine ⟨433161782306232039420451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9240784689199616840969621 433161782306232039420451)
                  ·
                    rfl

theorem cell21_1898054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_1898054 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1898054 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1898054 prefixEnd_1898054 := by exact prefixLift 1898054
  have htrace : WordTrace (prefixWord ++ tailWord_1898054) baseStart_1898054 baseEnd_1898054 := by
    simpa [prefixWord, tailWord_1898054, baseEnd_1898054] using wordTrace_append hprefix tailTrace_1898054
  have hstable : (prefixWord ++ tailWord_1898054).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1898054).length < 2 ^ (prefixWord ++ tailWord_1898054).sum := by decide
  have hdescent : baseEnd_1898054 < baseStart_1898054 := by decide
  rcases family_descends (prefixWord ++ tailWord_1898054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1898065 : List Nat := [1, 2, 2, 1, 3, 2, 4, 1, 5]
def baseStart_1898065 : Nat := 118140960795 + 1898065 * 2 ^ 59
def prefixEnd_1898065 : Nat := 4983230072969 + 3 ^ 40 * 1898065 * 2
def baseEnd_1898065 : Nat := 433164292656098464737095

theorem tailTrace_1898065 : CollatzResearch.WordTrace tailWord_1898065 prefixEnd_1898065 433164292656098464737095 := by
  unfold tailWord_1898065
  simp only [CollatzResearch.WordTrace]
  refine ⟨69228117868642143539119649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46152078579094762359413099 69228117868642143539119649)
  ·
    refine ⟨51921088401481607654339737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69228117868642143539119649 51921088401481607654339737)
    ·
      refine ⟨38940816301111205740754803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51921088401481607654339737 38940816301111205740754803)
      ·
        refine ⟨58411224451666808611132205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38940816301111205740754803 58411224451666808611132205)
        ·
          refine ⟨21904209169375053229174577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58411224451666808611132205 21904209169375053229174577)
          ·
            refine ⟨16428156877031289921880933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21904209169375053229174577 16428156877031289921880933)
            ·
              refine ⟨3080279414443366860352675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16428156877031289921880933 3080279414443366860352675)
              ·
                refine ⟨4620419121665050290529013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3080279414443366860352675 4620419121665050290529013)
                ·
                  refine ⟨433164292656098464737095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4620419121665050290529013 433164292656098464737095)
                  ·
                    rfl

theorem cell21_1898065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 4, 1, 5].length) (baseStart_1898065 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1898065 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1898065 prefixEnd_1898065 := by exact prefixLift 1898065
  have htrace : WordTrace (prefixWord ++ tailWord_1898065) baseStart_1898065 baseEnd_1898065 := by
    simpa [prefixWord, tailWord_1898065, baseEnd_1898065] using wordTrace_append hprefix tailTrace_1898065
  have hstable : (prefixWord ++ tailWord_1898065).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1898065).length < 2 ^ (prefixWord ++ tailWord_1898065).sum := by decide
  have hdescent : baseEnd_1898065 < baseStart_1898065 := by decide
  rcases family_descends (prefixWord ++ tailWord_1898065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1898116 : List Nat := [2, 3, 2, 1, 4, 1, 3, 2, 3]
def baseStart_1898116 : Nat := 118140960795 + 1898116 * 2 ^ 59
def prefixEnd_1898116 : Nat := 4983230072969 + 3 ^ 40 * 1898116 * 2
def baseEnd_1898116 : Nat := 433175931550933709386991

theorem tailTrace_1898116 : CollatzResearch.WordTrace tailWord_1898116 prefixEnd_1898116 433175931550933709386991 := by
  unfold tailWord_1898116
  simp only [CollatzResearch.WordTrace]
  refine ⟨34614988995728689624613101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46153318660971586166150801 34614988995728689624613101)
  ·
    refine ⟨12980620873398258609229913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34614988995728689624613101 12980620873398258609229913)
    ·
      refine ⟨9735465655048693956922435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12980620873398258609229913 9735465655048693956922435)
      ·
        refine ⟨14603198482573040935383653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9735465655048693956922435 14603198482573040935383653)
        ·
          refine ⟨2738099715482445175384435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14603198482573040935383653 2738099715482445175384435)
          ·
            refine ⟨4107149573223667763076653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2738099715482445175384435 4107149573223667763076653)
            ·
              refine ⟨1540181089958875411153745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4107149573223667763076653 1540181089958875411153745)
              ·
                refine ⟨1155135817469156558365309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1540181089958875411153745 1155135817469156558365309)
                ·
                  refine ⟨433175931550933709386991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1155135817469156558365309 433175931550933709386991)
                  ·
                    rfl

theorem cell21_1898116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 3, 2, 3].length) (baseStart_1898116 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1898116 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1898116 prefixEnd_1898116 := by exact prefixLift 1898116
  have htrace : WordTrace (prefixWord ++ tailWord_1898116) baseStart_1898116 baseEnd_1898116 := by
    simpa [prefixWord, tailWord_1898116, baseEnd_1898116] using wordTrace_append hprefix tailTrace_1898116
  have hstable : (prefixWord ++ tailWord_1898116).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1898116).length < 2 ^ (prefixWord ++ tailWord_1898116).sum := by decide
  have hdescent : baseEnd_1898116 < baseStart_1898116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1898116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1898172 : List Nat := [2, 2, 2, 3, 1, 2, 1, 4, 4]
def baseStart_1898172 : Nat := 118140960795 + 1898172 * 2 ^ 59
def prefixEnd_1898172 : Nat := 4983230072969 + 3 ^ 40 * 1898172 * 2
def baseEnd_1898172 : Nat := 433188711513890056453543

theorem tailTrace_1898172 : CollatzResearch.WordTrace tailWord_1898172 prefixEnd_1898172 433188711513890056453543 := by
  unfold tailWord_1898172
  simp only [CollatzResearch.WordTrace]
  refine ⟨34616010239627250406632385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46154680319503000542176513 34616010239627250406632385)
  ·
    refine ⟨25962007679720437804974289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34616010239627250406632385 25962007679720437804974289)
    ·
      refine ⟨19471505759790328353730717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25962007679720437804974289 19471505759790328353730717)
      ·
        refine ⟨7301814659921373132649019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19471505759790328353730717 7301814659921373132649019)
        ·
          refine ⟨10952721989882059698973529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7301814659921373132649019 10952721989882059698973529)
          ·
            refine ⟨8214541492411544774230147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10952721989882059698973529 8214541492411544774230147)
            ·
              refine ⟨12321812238617317161345221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8214541492411544774230147 12321812238617317161345221)
              ·
                refine ⟨2310339794740746967752229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12321812238617317161345221 2310339794740746967752229)
                ·
                  refine ⟨433188711513890056453543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2310339794740746967752229 433188711513890056453543)
                  ·
                    rfl

theorem cell21_1898172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 4, 4].length) (baseStart_1898172 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1898172 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1898172 prefixEnd_1898172 := by exact prefixLift 1898172
  have htrace : WordTrace (prefixWord ++ tailWord_1898172) baseStart_1898172 baseEnd_1898172 := by
    simpa [prefixWord, tailWord_1898172, baseEnd_1898172] using wordTrace_append hprefix tailTrace_1898172
  have hstable : (prefixWord ++ tailWord_1898172).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1898172).length < 2 ^ (prefixWord ++ tailWord_1898172).sum := by decide
  have hdescent : baseEnd_1898172 < baseStart_1898172 := by decide
  rcases family_descends (prefixWord ++ tailWord_1898172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1898178 : List Nat := [3, 5, 1, 2, 1, 2, 1, 6]
def baseStart_1898178 : Nat := 118140960795 + 1898178 * 2 ^ 59
def prefixEnd_1898178 : Nat := 4983230072969 + 3 ^ 40 * 1898178 * 2
def baseEnd_1898178 : Nat := 144396693598545126451177

theorem tailTrace_1898178 : CollatzResearch.WordTrace tailWord_1898178 prefixEnd_1898178 144396693598545126451177 := by
  unfold tailWord_1898178
  simp only [CollatzResearch.WordTrace]
  refine ⟨17308059829308190959495797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46154826211488509225322125 17308059829308190959495797)
  ·
    refine ⟨1622630608997642902452731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17308059829308190959495797 1622630608997642902452731)
    ·
      refine ⟨2433945913496464353679097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1622630608997642902452731 2433945913496464353679097)
      ·
        refine ⟨1825459435122348265259323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2433945913496464353679097 1825459435122348265259323)
        ·
          refine ⟨2738189152683522397888985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1825459435122348265259323 2738189152683522397888985)
          ·
            refine ⟨2053641864512641798416739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2738189152683522397888985 2053641864512641798416739)
            ·
              refine ⟨3080462796768962697625109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2053641864512641798416739 3080462796768962697625109)
              ·
                refine ⟨144396693598545126451177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3080462796768962697625109 144396693598545126451177)
                ·
                  rfl

theorem cell21_1898178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 1, 6].length) (baseStart_1898178 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1898178 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1898178 prefixEnd_1898178 := by exact prefixLift 1898178
  have htrace : WordTrace (prefixWord ++ tailWord_1898178) baseStart_1898178 baseEnd_1898178 := by
    simpa [prefixWord, tailWord_1898178, baseEnd_1898178] using wordTrace_append hprefix tailTrace_1898178
  have hstable : (prefixWord ++ tailWord_1898178).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1898178).length < 2 ^ (prefixWord ++ tailWord_1898178).sum := by decide
  have hdescent : baseEnd_1898178 < baseStart_1898178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1898178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1898338 : List Nat := [3, 3, 2, 1, 2, 10]
def baseStart_1898338 : Nat := 118140960795 + 1898338 * 2 ^ 59
def prefixEnd_1898338 : Nat := 4983230072969 + 3 ^ 40 * 1898338 * 2
def baseEnd_1898338 : Nat := 16045429443537431729131

theorem tailTrace_1898338 : CollatzResearch.WordTrace tailWord_1898338 prefixEnd_1898338 16045429443537431729131 := by
  unfold tailWord_1898338
  simp only [CollatzResearch.WordTrace]
  refine ⟨17309518749163277790951917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46158716664435407442538445 17309518749163277790951917)
  ·
    refine ⟨6491069530936229171606969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17309518749163277790951917 6491069530936229171606969)
    ·
      refine ⟨4868302148202171878705227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6491069530936229171606969 4868302148202171878705227)
      ·
        refine ⟨7302453222303257818057841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4868302148202171878705227 7302453222303257818057841)
        ·
          refine ⟨5476839916727443363543381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7302453222303257818057841 5476839916727443363543381)
          ·
            refine ⟨16045429443537431729131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5476839916727443363543381 16045429443537431729131)
            ·
              rfl

theorem cell21_1898338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 10].length) (baseStart_1898338 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1898338 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1898338 prefixEnd_1898338 := by exact prefixLift 1898338
  have htrace : WordTrace (prefixWord ++ tailWord_1898338) baseStart_1898338 baseEnd_1898338 := by
    simpa [prefixWord, tailWord_1898338, baseEnd_1898338] using wordTrace_append hprefix tailTrace_1898338
  have hstable : (prefixWord ++ tailWord_1898338).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1898338).length < 2 ^ (prefixWord ++ tailWord_1898338).sum := by decide
  have hdescent : baseEnd_1898338 < baseStart_1898338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1898338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1898352 : List Nat := [2, 1, 1, 1, 4, 1, 1, 5, 5]
def baseStart_1898352 : Nat := 118140960795 + 1898352 * 2 ^ 59
def prefixEnd_1898352 : Nat := 4983230072969 + 3 ^ 40 * 1898352 * 2
def baseEnd_1898352 : Nat := 433229789966249743453175

theorem tailTrace_1898352 : CollatzResearch.WordTrace tailWord_1898352 prefixEnd_1898352 433229789966249743453175 := by
  unfold tailWord_1898352
  simp only [CollatzResearch.WordTrace]
  refine ⟨34619292809301195777408655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46159057079068261036544873 34619292809301195777408655)
  ·
    refine ⟨51928939213951793666112983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34619292809301195777408655 51928939213951793666112983)
    ·
      refine ⟨77893408820927690499169475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51928939213951793666112983 77893408820927690499169475)
      ·
        refine ⟨116840113231391535748754213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77893408820927690499169475 116840113231391535748754213)
        ·
          refine ⟨21907521230885912952891415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 116840113231391535748754213 21907521230885912952891415)
          ·
            refine ⟨32861281846328869429337123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21907521230885912952891415 32861281846328869429337123)
            ·
              refine ⟨49291922769493304144005685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32861281846328869429337123 49291922769493304144005685)
              ·
                refine ⟨4621117759639997263500533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49291922769493304144005685 4621117759639997263500533)
                ·
                  refine ⟨433229789966249743453175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4621117759639997263500533 433229789966249743453175)
                  ·
                    rfl

theorem cell21_1898352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 5, 5].length) (baseStart_1898352 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1898352 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1898352 prefixEnd_1898352 := by exact prefixLift 1898352
  have htrace : WordTrace (prefixWord ++ tailWord_1898352) baseStart_1898352 baseEnd_1898352 := by
    simpa [prefixWord, tailWord_1898352, baseEnd_1898352] using wordTrace_append hprefix tailTrace_1898352
  have hstable : (prefixWord ++ tailWord_1898352).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1898352).length < 2 ^ (prefixWord ++ tailWord_1898352).sum := by decide
  have hdescent : baseEnd_1898352 < baseStart_1898352 := by decide
  rcases family_descends (prefixWord ++ tailWord_1898352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1898417 : List Nat := [1, 2, 2, 4, 2, 2, 3, 1, 4]
def baseStart_1898417 : Nat := 118140960795 + 1898417 * 2 ^ 59
def prefixEnd_1898417 : Nat := 4983230072969 + 3 ^ 40 * 1898417 * 2
def baseEnd_1898417 : Nat := 433244623851824074869709

theorem tailTrace_1898417 : CollatzResearch.WordTrace tailWord_1898417 prefixEnd_1898417 433244623851824074869709 := by
  unfold tailWord_1898417
  simp only [CollatzResearch.WordTrace]
  refine ⟨69240956363366907655933505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46160637575577938437289003 69240956363366907655933505)
  ·
    refine ⟨51930717272525180741950129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69240956363366907655933505 51930717272525180741950129)
    ·
      refine ⟨38948037954393885556462597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51930717272525180741950129 38948037954393885556462597)
      ·
        refine ⟨7302757116448853541836737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38948037954393885556462597 7302757116448853541836737)
        ·
          refine ⟨5477067837336640156377553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7302757116448853541836737 5477067837336640156377553)
          ·
            refine ⟨4107800878002480117283165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5477067837336640156377553 4107800878002480117283165)
            ·
              refine ⟨1540425329250930043981187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4107800878002480117283165 1540425329250930043981187)
              ·
                refine ⟨2310637993876395065971781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1540425329250930043981187 2310637993876395065971781)
                ·
                  refine ⟨433244623851824074869709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2310637993876395065971781 433244623851824074869709)
                  ·
                    rfl

theorem cell21_1898417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 3, 1, 4].length) (baseStart_1898417 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1898417 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1898417 prefixEnd_1898417 := by exact prefixLift 1898417
  have htrace : WordTrace (prefixWord ++ tailWord_1898417) baseStart_1898417 baseEnd_1898417 := by
    simpa [prefixWord, tailWord_1898417, baseEnd_1898417] using wordTrace_append hprefix tailTrace_1898417
  have hstable : (prefixWord ++ tailWord_1898417).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1898417).length < 2 ^ (prefixWord ++ tailWord_1898417).sum := by decide
  have hdescent : baseEnd_1898417 < baseStart_1898417 := by decide
  rcases family_descends (prefixWord ++ tailWord_1898417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1898549 : List Nat := [1, 3, 3, 1, 1, 1, 2, 9]
def baseStart_1898549 : Nat := 118140960795 + 1898549 * 2 ^ 59
def prefixEnd_1898549 : Nat := 4983230072969 + 3 ^ 40 * 1898549 * 2
def baseEnd_1898549 : Nat := 144424916016740392889813

theorem tailTrace_1898549 : CollatzResearch.WordTrace tailWord_1898549 prefixEnd_1898549 144424916016740392889813 := by
  unfold tailWord_1898549
  simp only [CollatzResearch.WordTrace]
  refine ⟨69245770798888694199738701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46163847199259129466492467 69245770798888694199738701)
  ·
    refine ⟨25967164049583260324902013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69245770798888694199738701 25967164049583260324902013)
    ·
      refine ⟨9737686518593722621838255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25967164049583260324902013 9737686518593722621838255)
      ·
        refine ⟨14606529777890583932757383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9737686518593722621838255 14606529777890583932757383)
        ·
          refine ⟨21909794666835875899136075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14606529777890583932757383 21909794666835875899136075)
          ·
            refine ⟨32864692000253813848704113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21909794666835875899136075 32864692000253813848704113)
            ·
              refine ⟨24648519000190360386528085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32864692000253813848704113 24648519000190360386528085)
              ·
                refine ⟨144424916016740392889813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24648519000190360386528085 144424916016740392889813)
                ·
                  rfl

theorem cell21_1898549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 9].length) (baseStart_1898549 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1898549 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1898549 prefixEnd_1898549 := by exact prefixLift 1898549
  have htrace : WordTrace (prefixWord ++ tailWord_1898549) baseStart_1898549 baseEnd_1898549 := by
    simpa [prefixWord, tailWord_1898549, baseEnd_1898549] using wordTrace_append hprefix tailTrace_1898549
  have hstable : (prefixWord ++ tailWord_1898549).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1898549).length < 2 ^ (prefixWord ++ tailWord_1898549).sum := by decide
  have hdescent : baseEnd_1898549 < baseStart_1898549 := by decide
  rcases family_descends (prefixWord ++ tailWord_1898549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1898642 : List Nat := [3, 2, 3, 1, 1, 1, 4, 6]
def baseStart_1898642 : Nat := 118140960795 + 1898642 * 2 ^ 59
def prefixEnd_1898642 : Nat := 4983230072969 + 3 ^ 40 * 1898642 * 2
def baseEnd_1898642 : Nat := 144431990639091227873083

theorem tailTrace_1898642 : CollatzResearch.WordTrace tailWord_1898642 prefixEnd_1898642 144431990639091227873083 := by
  unfold tailWord_1898642
  simp only [CollatzResearch.WordTrace]
  refine ⟨17312290696887942770718545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46166108525034514055249453 17312290696887942770718545)
  ·
    refine ⟨12984218022665957078038909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17312290696887942770718545 12984218022665957078038909)
    ·
      refine ⟨4869081758499733904264591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12984218022665957078038909 4869081758499733904264591)
      ·
        refine ⟨7303622637749600856396887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4869081758499733904264591 7303622637749600856396887)
        ·
          refine ⟨10955433956624401284595331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7303622637749600856396887 10955433956624401284595331)
          ·
            refine ⟨16433150934936601926892997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10955433956624401284595331 16433150934936601926892997)
            ·
              refine ⟨3081215800300612861292437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16433150934936601926892997 3081215800300612861292437)
              ·
                refine ⟨144431990639091227873083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3081215800300612861292437 144431990639091227873083)
                ·
                  rfl

theorem cell21_1898642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 4, 6].length) (baseStart_1898642 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1898642 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1898642 prefixEnd_1898642 := by exact prefixLift 1898642
  have htrace : WordTrace (prefixWord ++ tailWord_1898642) baseStart_1898642 baseEnd_1898642 := by
    simpa [prefixWord, tailWord_1898642, baseEnd_1898642] using wordTrace_append hprefix tailTrace_1898642
  have hstable : (prefixWord ++ tailWord_1898642).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1898642).length < 2 ^ (prefixWord ++ tailWord_1898642).sum := by decide
  have hdescent : baseEnd_1898642 < baseStart_1898642 := by decide
  rcases family_descends (prefixWord ++ tailWord_1898642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1898676 : List Nat := [2, 5, 3, 1, 1, 9]
def baseStart_1898676 : Nat := 118140960795 + 1898676 * 2 ^ 59
def prefixEnd_1898676 : Nat := 4983230072969 + 3 ^ 40 * 1898676 * 2
def baseEnd_1898676 : Nat := 16048286340018414076019

theorem tailTrace_1898676 : CollatzResearch.WordTrace tailWord_1898676 prefixEnd_1898676 16048286340018414076019 := by
  unfold tailWord_1898676
  simp only [CollatzResearch.WordTrace]
  refine ⟨34625201434714297444805941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46166935246285729926407921 34625201434714297444805941)
  ·
    refine ⟨3246112634504465385450557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34625201434714297444805941 3246112634504465385450557)
    ·
      refine ⟨1217292237939174519543959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3246112634504465385450557 1217292237939174519543959)
      ·
        refine ⟨1825938356908761779315939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1217292237939174519543959 1825938356908761779315939)
        ·
          refine ⟨2738907535363142668973909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1825938356908761779315939 2738907535363142668973909)
          ·
            refine ⟨16048286340018414076019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2738907535363142668973909 16048286340018414076019)
            ·
              rfl

theorem cell21_1898676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 9].length) (baseStart_1898676 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1898676 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1898676 prefixEnd_1898676 := by exact prefixLift 1898676
  have htrace : WordTrace (prefixWord ++ tailWord_1898676) baseStart_1898676 baseEnd_1898676 := by
    simpa [prefixWord, tailWord_1898676, baseEnd_1898676] using wordTrace_append hprefix tailTrace_1898676
  have hstable : (prefixWord ++ tailWord_1898676).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1898676).length < 2 ^ (prefixWord ++ tailWord_1898676).sum := by decide
  have hdescent : baseEnd_1898676 < baseStart_1898676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1898676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1898715 : List Nat := [1, 1, 1, 1, 1, 1, 1, 7, 7]
def baseStart_1898715 : Nat := 118140960795 + 1898715 * 2 ^ 59
def prefixEnd_1898715 : Nat := 4983230072969 + 3 ^ 40 * 1898715 * 2
def baseEnd_1898715 : Nat := 433312631511841778902433

theorem tailTrace_1898715 : CollatzResearch.WordTrace tailWord_1898715 prefixEnd_1898715 433312631511841778902433 := by
  unfold tailWord_1898715
  simp only [CollatzResearch.WordTrace]
  refine ⟨69251825316287304550281599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46167883544191536366854399 69251825316287304550281599)
  ·
    refine ⟨103877737974430956825422399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69251825316287304550281599 103877737974430956825422399)
    ·
      refine ⟨155816606961646435238133599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103877737974430956825422399 155816606961646435238133599)
      ·
        refine ⟨233724910442469652857200399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155816606961646435238133599 233724910442469652857200399)
        ·
          refine ⟨350587365663704479285800599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233724910442469652857200399 350587365663704479285800599)
          ·
            refine ⟨525881048495556718928700899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 350587365663704479285800599 525881048495556718928700899)
            ·
              refine ⟨788821572743335078393051349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 525881048495556718928700899 788821572743335078393051349)
              ·
                refine ⟨18488005611171915899837141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 788821572743335078393051349 18488005611171915899837141)
                ·
                  refine ⟨433312631511841778902433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18488005611171915899837141 433312631511841778902433)
                  ·
                    rfl

theorem cell21_1898715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7, 7].length) (baseStart_1898715 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1898715 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1898715 prefixEnd_1898715 := by exact prefixLift 1898715
  have htrace : WordTrace (prefixWord ++ tailWord_1898715) baseStart_1898715 baseEnd_1898715 := by
    simpa [prefixWord, tailWord_1898715, baseEnd_1898715] using wordTrace_append hprefix tailTrace_1898715
  have hstable : (prefixWord ++ tailWord_1898715).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1898715).length < 2 ^ (prefixWord ++ tailWord_1898715).sum := by decide
  have hdescent : baseEnd_1898715 < baseStart_1898715 := by decide
  rcases family_descends (prefixWord ++ tailWord_1898715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1898808 : List Nat := [2, 1, 2, 1, 3, 1, 5, 1, 5]
def baseStart_1898808 : Nat := 118140960795 + 1898808 * 2 ^ 59
def prefixEnd_1898808 : Nat := 4983230072969 + 3 ^ 40 * 1898808 * 2
def baseEnd_1898808 : Nat := 433333855378894283852243

theorem tailTrace_1898808 : CollatzResearch.WordTrace tailWord_1898808 prefixEnd_1898808 433333855378894283852243 := by
  unfold tailWord_1898808
  simp only [CollatzResearch.WordTrace]
  refine ⟨34627608652475190716708539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46170144869966920955611385 34627608652475190716708539)
  ·
    refine ⟨51941412978712786075062809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34627608652475190716708539 51941412978712786075062809)
    ·
      refine ⟨38956059734034589556297107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51941412978712786075062809 38956059734034589556297107)
      ·
        refine ⟨58434089601051884334445661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38956059734034589556297107 58434089601051884334445661)
        ·
          refine ⟨21912783600394456625417123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58434089601051884334445661 21912783600394456625417123)
          ·
            refine ⟨32869175400591684938125685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21912783600394456625417123 32869175400591684938125685)
            ·
              refine ⟨3081485193805470462949283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32869175400591684938125685 3081485193805470462949283)
              ·
                refine ⟨4622227790708205694423925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3081485193805470462949283 4622227790708205694423925)
                ·
                  refine ⟨433333855378894283852243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4622227790708205694423925 433333855378894283852243)
                  ·
                    rfl

theorem cell21_1898808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 5, 1, 5].length) (baseStart_1898808 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1898808 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1898808 prefixEnd_1898808 := by exact prefixLift 1898808
  have htrace : WordTrace (prefixWord ++ tailWord_1898808) baseStart_1898808 baseEnd_1898808 := by
    simpa [prefixWord, tailWord_1898808, baseEnd_1898808] using wordTrace_append hprefix tailTrace_1898808
  have hstable : (prefixWord ++ tailWord_1898808).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1898808).length < 2 ^ (prefixWord ++ tailWord_1898808).sum := by decide
  have hdescent : baseEnd_1898808 < baseStart_1898808 := by decide
  rcases family_descends (prefixWord ++ tailWord_1898808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1898856 : List Nat := [2, 1, 4, 2, 2, 2, 2, 2, 4]
def baseStart_1898856 : Nat := 118140960795 + 1898856 * 2 ^ 59
def prefixEnd_1898856 : Nat := 4983230072969 + 3 ^ 40 * 1898856 * 2
def baseEnd_1898856 : Nat := 433344809632856867052145

theorem tailTrace_1898856 : CollatzResearch.WordTrace tailWord_1898856 prefixEnd_1898856 433344809632856867052145 := by
  unfold tailWord_1898856
  simp only [CollatzResearch.WordTrace]
  refine ⟨34628484004388242815582211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46171312005850990420776281 34628484004388242815582211)
  ·
    refine ⟨51942726006582364223373317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34628484004388242815582211 51942726006582364223373317)
    ·
      refine ⟨9739261126234193291882497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51942726006582364223373317 9739261126234193291882497)
      ·
        refine ⟨7304445844675644968911873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9739261126234193291882497 7304445844675644968911873)
        ·
          refine ⟨5478334383506733726683905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7304445844675644968911873 5478334383506733726683905)
          ·
            refine ⟨4108750787630050295012929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5478334383506733726683905 4108750787630050295012929)
            ·
              refine ⟨3081563090722537721259697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4108750787630050295012929 3081563090722537721259697)
              ·
                refine ⟨2311172318041903290944773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3081563090722537721259697 2311172318041903290944773)
                ·
                  refine ⟨433344809632856867052145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2311172318041903290944773 433344809632856867052145)
                  ·
                    rfl

theorem cell21_1898856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 2, 2, 4].length) (baseStart_1898856 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1898856 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1898856 prefixEnd_1898856 := by exact prefixLift 1898856
  have htrace : WordTrace (prefixWord ++ tailWord_1898856) baseStart_1898856 baseEnd_1898856 := by
    simpa [prefixWord, tailWord_1898856, baseEnd_1898856] using wordTrace_append hprefix tailTrace_1898856
  have hstable : (prefixWord ++ tailWord_1898856).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1898856).length < 2 ^ (prefixWord ++ tailWord_1898856).sum := by decide
  have hdescent : baseEnd_1898856 < baseStart_1898856 := by decide
  rcases family_descends (prefixWord ++ tailWord_1898856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1898884 : List Nat := [2, 3, 2, 1, 1, 2, 3, 2, 5]
def baseStart_1898884 : Nat := 118140960795 + 1898884 * 2 ^ 59
def prefixEnd_1898884 : Nat := 4983230072969 + 3 ^ 40 * 1898884 * 2
def baseEnd_1898884 : Nat := 433351199614335040585421

theorem tailTrace_1898884 : CollatzResearch.WordTrace tailWord_1898884 prefixEnd_1898884 433351199614335040585421 := by
  unfold tailWord_1898884
  simp only [CollatzResearch.WordTrace]
  refine ⟨34628994626337523206591853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46171992835116697608789137 34628994626337523206591853)
  ·
    refine ⟨12985872984876571202471945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34628994626337523206591853 12985872984876571202471945)
    ·
      refine ⟨9739404738657428401853959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12985872984876571202471945 9739404738657428401853959)
      ·
        refine ⟨14609107107986142602780939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9739404738657428401853959 14609107107986142602780939)
        ·
          refine ⟨21913660661979213904171409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14609107107986142602780939 21913660661979213904171409)
          ·
            refine ⟨16435245496484410428128557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21913660661979213904171409 16435245496484410428128557)
            ·
              refine ⟨6163217061181653910548209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16435245496484410428128557 6163217061181653910548209)
              ·
                refine ⟨4622412795886240432911157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6163217061181653910548209 4622412795886240432911157)
                ·
                  refine ⟨433351199614335040585421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4622412795886240432911157 433351199614335040585421)
                  ·
                    rfl

theorem cell21_1898884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 2, 5].length) (baseStart_1898884 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1898884 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1898884 prefixEnd_1898884 := by exact prefixLift 1898884
  have htrace : WordTrace (prefixWord ++ tailWord_1898884) baseStart_1898884 baseEnd_1898884 := by
    simpa [prefixWord, tailWord_1898884, baseEnd_1898884] using wordTrace_append hprefix tailTrace_1898884
  have hstable : (prefixWord ++ tailWord_1898884).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1898884).length < 2 ^ (prefixWord ++ tailWord_1898884).sum := by decide
  have hdescent : baseEnd_1898884 < baseStart_1898884 := by decide
  rcases family_descends (prefixWord ++ tailWord_1898884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1898915 : List Nat := [1, 1, 1, 4, 1, 4, 3, 2, 4]
def baseStart_1898915 : Nat := 118140960795 + 1898915 * 2 ^ 59
def prefixEnd_1898915 : Nat := 4983230072969 + 3 ^ 40 * 1898915 * 2
def baseEnd_1898915 : Nat := 433358274236685875568691

theorem tailTrace_1898915 : CollatzResearch.WordTrace tailWord_1898915 prefixEnd_1898915 433358274236685875568691 := by
  unfold tailWord_1898915
  simp only [CollatzResearch.WordTrace]
  refine ⟨69259119915562738707562199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46172746610375159138374799 69259119915562738707562199)
  ·
    refine ⟨103888679873344108061343299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69259119915562738707562199 103888679873344108061343299)
    ·
      refine ⟨155833019810016162092014949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103888679873344108061343299 155833019810016162092014949)
      ·
        refine ⟨29218691214378030392252803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 155833019810016162092014949 29218691214378030392252803)
        ·
          refine ⟨43828036821567045588379205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29218691214378030392252803 43828036821567045588379205)
          ·
            refine ⟨8217756904043821047821101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43828036821567045588379205 8217756904043821047821101)
            ·
              refine ⟨3081658839016432892932913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8217756904043821047821101 3081658839016432892932913)
              ·
                refine ⟨2311244129262324669699685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3081658839016432892932913 2311244129262324669699685)
                ·
                  refine ⟨433358274236685875568691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2311244129262324669699685 433358274236685875568691)
                  ·
                    rfl

theorem cell21_1898915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 3, 2, 4].length) (baseStart_1898915 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1898915 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1898915 prefixEnd_1898915 := by exact prefixLift 1898915
  have htrace : WordTrace (prefixWord ++ tailWord_1898915) baseStart_1898915 baseEnd_1898915 := by
    simpa [prefixWord, tailWord_1898915, baseEnd_1898915] using wordTrace_append hprefix tailTrace_1898915
  have hstable : (prefixWord ++ tailWord_1898915).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1898915).length < 2 ^ (prefixWord ++ tailWord_1898915).sum := by decide
  have hdescent : baseEnd_1898915 < baseStart_1898915 := by decide
  rcases family_descends (prefixWord ++ tailWord_1898915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1899028 : List Nat := [2, 4, 3, 1, 1, 3, 2, 2, 3]
def baseStart_1899028 : Nat := 118140960795 + 1899028 * 2 ^ 59
def prefixEnd_1899028 : Nat := 4983230072969 + 3 ^ 40 * 1899028 * 2
def baseEnd_1899028 : Nat := 433384062376222790185127

theorem tailTrace_1899028 : CollatzResearch.WordTrace tailWord_1899028 prefixEnd_1899028 433384062376222790185127 := by
  unfold tailWord_1899028
  simp only [CollatzResearch.WordTrace]
  refine ⟨34631620682076679503212869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46175494242768906004283825 34631620682076679503212869)
  ·
    refine ⟨6493428877889377406852413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34631620682076679503212869 6493428877889377406852413)
    ·
      refine ⟨2435035829208516527569655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6493428877889377406852413 2435035829208516527569655)
      ·
        refine ⟨3652553743812774791354483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2435035829208516527569655 3652553743812774791354483)
        ·
          refine ⟨5478830615719162187031725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3652553743812774791354483 5478830615719162187031725)
          ·
            refine ⟨2054561480894685820136897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5478830615719162187031725 2054561480894685820136897)
            ·
              refine ⟨1540921110671014365102673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2054561480894685820136897 1540921110671014365102673)
              ·
                refine ⟨1155690833003260773827005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1540921110671014365102673 1155690833003260773827005)
                ·
                  refine ⟨433384062376222790185127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1155690833003260773827005 433384062376222790185127)
                  ·
                    rfl

theorem cell21_1899028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 2, 2, 3].length) (baseStart_1899028 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1899028 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1899028 prefixEnd_1899028 := by exact prefixLift 1899028
  have htrace : WordTrace (prefixWord ++ tailWord_1899028) baseStart_1899028 baseEnd_1899028 := by
    simpa [prefixWord, tailWord_1899028, baseEnd_1899028] using wordTrace_append hprefix tailTrace_1899028
  have hstable : (prefixWord ++ tailWord_1899028).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1899028).length < 2 ^ (prefixWord ++ tailWord_1899028).sum := by decide
  have hdescent : baseEnd_1899028 < baseStart_1899028 := by decide
  rcases family_descends (prefixWord ++ tailWord_1899028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1899129 : List Nat := [1, 2, 1, 3, 3, 2, 3, 3, 3]
def baseStart_1899129 : Nat := 118140960795 + 1899129 * 2 ^ 59
def prefixEnd_1899129 : Nat := 4983230072969 + 3 ^ 40 * 1899129 * 2
def baseEnd_1899129 : Nat := 433407111952269059001587

theorem tailTrace_1899129 : CollatzResearch.WordTrace tailWord_1899129 prefixEnd_1899129 433407111952269059001587 := by
  unfold tailWord_1899129
  simp only [CollatzResearch.WordTrace]
  refine ⟨69266925136787453255852441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46177950091191635503901627 69266925136787453255852441)
  ·
    refine ⟨51950193852590589941889331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69266925136787453255852441 51950193852590589941889331)
    ·
      refine ⟨77925290778885884912833997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51950193852590589941889331 77925290778885884912833997)
      ·
        refine ⟨29221984042082206842312749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77925290778885884912833997 29221984042082206842312749)
        ·
          refine ⟨10958244015780827565867281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29221984042082206842312749 10958244015780827565867281)
          ·
            refine ⟨8218683011835620674400461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10958244015780827565867281 8218683011835620674400461)
            ·
              refine ⟨3082006129438357752900173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8218683011835620674400461 3082006129438357752900173)
              ·
                refine ⟨1155752298539384157337565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3082006129438357752900173 1155752298539384157337565)
                ·
                  refine ⟨433407111952269059001587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1155752298539384157337565 433407111952269059001587)
                  ·
                    rfl

theorem cell21_1899129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 3, 3, 3].length) (baseStart_1899129 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1899129 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1899129 prefixEnd_1899129 := by exact prefixLift 1899129
  have htrace : WordTrace (prefixWord ++ tailWord_1899129) baseStart_1899129 baseEnd_1899129 := by
    simpa [prefixWord, tailWord_1899129, baseEnd_1899129] using wordTrace_append hprefix tailTrace_1899129
  have hstable : (prefixWord ++ tailWord_1899129).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1899129).length < 2 ^ (prefixWord ++ tailWord_1899129).sum := by decide
  have hdescent : baseEnd_1899129 < baseStart_1899129 := by decide
  rcases family_descends (prefixWord ++ tailWord_1899129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1899146 : List Nat := [3, 1, 2, 3, 4, 1, 1, 1, 5]
def baseStart_1899146 : Nat := 118140960795 + 1899146 * 2 ^ 59
def prefixEnd_1899146 : Nat := 4983230072969 + 3 ^ 40 * 1899146 * 2
def baseEnd_1899146 : Nat := 433410991583880807218219

theorem tailTrace_1899146 : CollatzResearch.WordTrace tailWord_1899146 prefixEnd_1899146 433410991583880807218219 := by
  unfold tailWord_1899146
  simp only [CollatzResearch.WordTrace]
  refine ⟨17316886294431466289805323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46178363451817243439480861 17316886294431466289805323)
  ·
    refine ⟨25975329441647199434707985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17316886294431466289805323 25975329441647199434707985)
    ·
      refine ⟨19481497081235399576030989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25975329441647199434707985 19481497081235399576030989)
      ·
        refine ⟨7305561405463274841011621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19481497081235399576030989 7305561405463274841011621)
        ·
          refine ⟨1369792763524364032689679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7305561405463274841011621 1369792763524364032689679)
          ·
            refine ⟨2054689145286546049034519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1369792763524364032689679 2054689145286546049034519)
            ·
              refine ⟨3082033717929819073551779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2054689145286546049034519 3082033717929819073551779)
              ·
                refine ⟨4623050576894728610327669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3082033717929819073551779 4623050576894728610327669)
                ·
                  refine ⟨433410991583880807218219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4623050576894728610327669 433410991583880807218219)
                  ·
                    rfl

theorem cell21_1899146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 1, 1, 5].length) (baseStart_1899146 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1899146 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1899146 prefixEnd_1899146 := by exact prefixLift 1899146
  have htrace : WordTrace (prefixWord ++ tailWord_1899146) baseStart_1899146 baseEnd_1899146 := by
    simpa [prefixWord, tailWord_1899146, baseEnd_1899146] using wordTrace_append hprefix tailTrace_1899146
  have hstable : (prefixWord ++ tailWord_1899146).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1899146).length < 2 ^ (prefixWord ++ tailWord_1899146).sum := by decide
  have hdescent : baseEnd_1899146 < baseStart_1899146 := by decide
  rcases family_descends (prefixWord ++ tailWord_1899146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1899253 : List Nat := [1, 3, 6, 1, 1, 1, 1, 1, 6]
def baseStart_1899253 : Nat := 118140960795 + 1899253 * 2 ^ 59
def prefixEnd_1899253 : Nat := 4983230072969 + 3 ^ 40 * 1899253 * 2
def baseEnd_1899253 : Nat := 433435410441672398934667

theorem tailTrace_1899253 : CollatzResearch.WordTrace tailWord_1899253 prefixEnd_1899253 433435410441672398934667 := by
  unfold tailWord_1899253
  simp only [CollatzResearch.WordTrace]
  refine ⟨69271447788338222433366413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46180965192225481622244275 69271447788338222433366413)
  ·
    refine ⟨25976792920626833412512405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69271447788338222433366413 25976792920626833412512405)
    ·
      refine ⟨1217662168154382816211519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 25976792920626833412512405 1217662168154382816211519)
      ·
        refine ⟨1826493252231574224317279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1217662168154382816211519 1826493252231574224317279)
        ·
          refine ⟨2739739878347361336475919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1826493252231574224317279 2739739878347361336475919)
          ·
            refine ⟨4109609817521042004713879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2739739878347361336475919 4109609817521042004713879)
            ·
              refine ⟨6164414726281563007070819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4109609817521042004713879 6164414726281563007070819)
              ·
                refine ⟨9246622089422344510606229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6164414726281563007070819 9246622089422344510606229)
                ·
                  refine ⟨433435410441672398934667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9246622089422344510606229 433435410441672398934667)
                  ·
                    rfl

theorem cell21_1899253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 1, 6].length) (baseStart_1899253 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1899253 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1899253 prefixEnd_1899253 := by exact prefixLift 1899253
  have htrace : WordTrace (prefixWord ++ tailWord_1899253) baseStart_1899253 baseEnd_1899253 := by
    simpa [prefixWord, tailWord_1899253, baseEnd_1899253] using wordTrace_append hprefix tailTrace_1899253
  have hstable : (prefixWord ++ tailWord_1899253).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1899253).length < 2 ^ (prefixWord ++ tailWord_1899253).sum := by decide
  have hdescent : baseEnd_1899253 < baseStart_1899253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1899253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1899298 : List Nat := [3, 3, 1, 1, 2, 4, 1, 3, 3]
def baseStart_1899298 : Nat := 118140960795 + 1899298 * 2 ^ 59
def prefixEnd_1899298 : Nat := 4983230072969 + 3 ^ 40 * 1899298 * 2
def baseEnd_1899298 : Nat := 433445680054762320684575

theorem tailTrace_1899298 : CollatzResearch.WordTrace tailWord_1899298 prefixEnd_1899298 433445680054762320684575 := by
  unfold tailWord_1899298
  simp only [CollatzResearch.WordTrace]
  refine ⟨17318272268293798779688637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46182059382116796745836365 17318272268293798779688637)
  ·
    refine ⟨6494352100610174542383239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17318272268293798779688637 6494352100610174542383239)
    ·
      refine ⟨9741528150915261813574859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6494352100610174542383239 9741528150915261813574859)
      ·
        refine ⟨14612292226372892720362289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9741528150915261813574859 14612292226372892720362289)
        ·
          refine ⟨10959219169779669540271717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14612292226372892720362289 10959219169779669540271717)
          ·
            refine ⟨2054853594333688038800947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10959219169779669540271717 2054853594333688038800947)
            ·
              refine ⟨3082280391500532058201421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2054853594333688038800947 3082280391500532058201421)
              ·
                refine ⟨1155855146812699521825533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3082280391500532058201421 1155855146812699521825533)
                ·
                  refine ⟨433445680054762320684575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1155855146812699521825533 433445680054762320684575)
                  ·
                    rfl

theorem cell21_1899298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 1, 3, 3].length) (baseStart_1899298 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1899298 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1899298 prefixEnd_1899298 := by exact prefixLift 1899298
  have htrace : WordTrace (prefixWord ++ tailWord_1899298) baseStart_1899298 baseEnd_1899298 := by
    simpa [prefixWord, tailWord_1899298, baseEnd_1899298] using wordTrace_append hprefix tailTrace_1899298
  have hstable : (prefixWord ++ tailWord_1899298).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1899298).length < 2 ^ (prefixWord ++ tailWord_1899298).sum := by decide
  have hdescent : baseEnd_1899298 < baseStart_1899298 := by decide
  rcases family_descends (prefixWord ++ tailWord_1899298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1899326 : List Nat := [4, 2, 1, 2, 3, 1, 2, 6]
def baseStart_1899326 : Nat := 118140960795 + 1899326 * 2 ^ 59
def prefixEnd_1899326 : Nat := 4983230072969 + 3 ^ 40 * 1899326 * 2
def baseEnd_1899326 : Nat := 144484023345413498072617

theorem tailTrace_1899326 : CollatzResearch.WordTrace tailWord_1899326 prefixEnd_1899326 144484023345413498072617 := by
  unfold tailWord_1899326
  simp only [CollatzResearch.WordTrace]
  refine ⟨8659263789634219487596729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46182740211382503933849221 8659263789634219487596729)
  ·
    refine ⟨6494447842225664615697547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8659263789634219487596729 6494447842225664615697547)
    ·
      refine ⟨9741671763338496923546321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6494447842225664615697547 9741671763338496923546321)
      ·
        refine ⟨7306253822503872692659741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9741671763338496923546321 7306253822503872692659741)
        ·
          refine ⟨2739845183438952259747403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7306253822503872692659741 2739845183438952259747403)
          ·
            refine ⟨4109767775158428389621105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2739845183438952259747403 4109767775158428389621105)
            ·
              refine ⟨3082325831368821292215829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4109767775158428389621105 3082325831368821292215829)
              ·
                refine ⟨144484023345413498072617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3082325831368821292215829 144484023345413498072617)
                ·
                  rfl

theorem cell21_1899326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 2, 6].length) (baseStart_1899326 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1899326 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1899326 prefixEnd_1899326 := by exact prefixLift 1899326
  have htrace : WordTrace (prefixWord ++ tailWord_1899326) baseStart_1899326 baseEnd_1899326 := by
    simpa [prefixWord, tailWord_1899326, baseEnd_1899326] using wordTrace_append hprefix tailTrace_1899326
  have hstable : (prefixWord ++ tailWord_1899326).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1899326).length < 2 ^ (prefixWord ++ tailWord_1899326).sum := by decide
  have hdescent : baseEnd_1899326 < baseStart_1899326 := by decide
  rcases family_descends (prefixWord ++ tailWord_1899326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1899368 : List Nat := [2, 1, 4, 2, 1, 11]
def baseStart_1899368 : Nat := 118140960795 + 1899368 * 2 ^ 59
def prefixEnd_1899368 : Nat := 4983230072969 + 3 ^ 40 * 1899368 * 2
def baseEnd_1899368 : Nat := 16054135370683620537695

theorem tailTrace_1899368 : CollatzResearch.WordTrace tailWord_1899368 prefixEnd_1899368 16054135370683620537695 := by
  unfold tailWord_1899368
  simp only [CollatzResearch.WordTrace]
  refine ⟨34637821091460798536901379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46183761455281064715868505 34637821091460798536901379)
  ·
    refine ⟨51956731637191197805352069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34637821091460798536901379 51956731637191197805352069)
    ·
      refine ⟨9741887181973349588503513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51956731637191197805352069 9741887181973349588503513)
      ·
        refine ⟨7306415386480012191377635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9741887181973349588503513 7306415386480012191377635)
        ·
          refine ⟨10959623079720018287066453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7306415386480012191377635 10959623079720018287066453)
          ·
            refine ⟨16054135370683620537695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 10959623079720018287066453 16054135370683620537695)
            ·
              rfl

theorem cell21_1899368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 11].length) (baseStart_1899368 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1899368 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1899368 prefixEnd_1899368 := by exact prefixLift 1899368
  have htrace : WordTrace (prefixWord ++ tailWord_1899368) baseStart_1899368 baseEnd_1899368 := by
    simpa [prefixWord, tailWord_1899368, baseEnd_1899368] using wordTrace_append hprefix tailTrace_1899368
  have hstable : (prefixWord ++ tailWord_1899368).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1899368).length < 2 ^ (prefixWord ++ tailWord_1899368).sum := by decide
  have hdescent : baseEnd_1899368 < baseStart_1899368 := by decide
  rcases family_descends (prefixWord ++ tailWord_1899368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1899374 : List Nat := [4, 1, 2, 3, 2, 1, 1, 4, 3]
def baseStart_1899374 : Nat := 118140960795 + 1899374 * 2 ^ 59
def prefixEnd_1899374 : Nat := 4983230072969 + 3 ^ 40 * 1899374 * 2
def baseEnd_1899374 : Nat := 433463024290203077417753

theorem tailTrace_1899374 : CollatzResearch.WordTrace tailWord_1899374 prefixEnd_1899374 433463024290203077417753 := by
  unfold tailWord_1899374
  simp only [CollatzResearch.WordTrace]
  refine ⟨8659482627612482512315147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46183907347266573399014117 8659482627612482512315147)
  ·
    refine ⟨12989223941418723768472721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8659482627612482512315147 12989223941418723768472721)
    ·
      refine ⟨9741917956064042826354541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12989223941418723768472721 9741917956064042826354541)
      ·
        refine ⟨3653219233524016059882953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9741917956064042826354541 3653219233524016059882953)
        ·
          refine ⟨2739914425143012044912215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3653219233524016059882953 2739914425143012044912215)
          ·
            refine ⟨4109871637714518067368323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2739914425143012044912215 4109871637714518067368323)
            ·
              refine ⟨6164807456571777101052485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4109871637714518067368323 6164807456571777101052485)
              ·
                refine ⟨1155901398107208206447341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6164807456571777101052485 1155901398107208206447341)
                ·
                  refine ⟨433463024290203077417753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1155901398107208206447341 433463024290203077417753)
                  ·
                    rfl

theorem cell21_1899374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 4, 3].length) (baseStart_1899374 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1899374 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1899374 prefixEnd_1899374 := by exact prefixLift 1899374
  have htrace : WordTrace (prefixWord ++ tailWord_1899374) baseStart_1899374 baseEnd_1899374 := by
    simpa [prefixWord, tailWord_1899374, baseEnd_1899374] using wordTrace_append hprefix tailTrace_1899374
  have hstable : (prefixWord ++ tailWord_1899374).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1899374).length < 2 ^ (prefixWord ++ tailWord_1899374).sum := by decide
  have hdescent : baseEnd_1899374 < baseStart_1899374 := by decide
  rcases family_descends (prefixWord ++ tailWord_1899374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1899385 : List Nat := [1, 2, 1, 3, 2, 5, 1, 6]
def baseStart_1899385 : Nat := 118140960795 + 1899385 * 2 ^ 59
def prefixEnd_1899385 : Nat := 4983230072969 + 3 ^ 40 * 1899385 * 2
def baseEnd_1899385 : Nat := 144488511546689834244799

theorem tailTrace_1899385 : CollatzResearch.WordTrace tailWord_1899385 prefixEnd_1899385 144488511546689834244799 := by
  unfold tailWord_1899385
  simp only [CollatzResearch.WordTrace]
  refine ⟨69276262223860008977171609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46184174815906672651447739 69276262223860008977171609)
  ·
    refine ⟨51957196667895006732878707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69276262223860008977171609 51957196667895006732878707)
    ·
      refine ⟨77935795001842510099318061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51957196667895006732878707 77935795001842510099318061)
      ·
        refine ⟨29225923125690941287244273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77935795001842510099318061 29225923125690941287244273)
        ·
          refine ⟨21919442344268205965433205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29225923125690941287244273 21919442344268205965433205)
          ·
            refine ⟨2054947719775144309259363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21919442344268205965433205 2054947719775144309259363)
            ·
              refine ⟨3082421579662716463889045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2054947719775144309259363 3082421579662716463889045)
              ·
                refine ⟨144488511546689834244799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3082421579662716463889045 144488511546689834244799)
                ·
                  rfl

theorem cell21_1899385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 1, 6].length) (baseStart_1899385 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1899385 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1899385 prefixEnd_1899385 := by exact prefixLift 1899385
  have htrace : WordTrace (prefixWord ++ tailWord_1899385) baseStart_1899385 baseEnd_1899385 := by
    simpa [prefixWord, tailWord_1899385, baseEnd_1899385] using wordTrace_append hprefix tailTrace_1899385
  have hstable : (prefixWord ++ tailWord_1899385).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1899385).length < 2 ^ (prefixWord ++ tailWord_1899385).sum := by decide
  have hdescent : baseEnd_1899385 < baseStart_1899385 := by decide
  rcases family_descends (prefixWord ++ tailWord_1899385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1899399 : List Nat := [1, 1, 4, 2, 3, 1, 1, 1, 7]
def baseStart_1899399 : Nat := 118140960795 + 1899399 * 2 ^ 59
def prefixEnd_1899399 : Nat := 4983230072969 + 3 ^ 40 * 1899399 * 2
def baseEnd_1899399 : Nat := 433468729630808589501035

theorem tailTrace_1899399 : CollatzResearch.WordTrace tailWord_1899399 prefixEnd_1899399 433468729630808589501035 := by
  unfold tailWord_1899399
  simp only [CollatzResearch.WordTrace]
  refine ⟨69276772845809289368181251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46184515230539526245454167 69276772845809289368181251)
  ·
    refine ⟨103915159268713934052271877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69276772845809289368181251 103915159268713934052271877)
    ·
      refine ⟨19484092362883862634800977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103915159268713934052271877 19484092362883862634800977)
      ·
        refine ⟨14613069272162896976100733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19484092362883862634800977 14613069272162896976100733)
        ·
          refine ⟨5479900977061086366037775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14613069272162896976100733 5479900977061086366037775)
          ·
            refine ⟨8219851465591629549056663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5479900977061086366037775 8219851465591629549056663)
            ·
              refine ⟨12329777198387444323584995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8219851465591629549056663 12329777198387444323584995)
              ·
                refine ⟨18494665797581166485377493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12329777198387444323584995 18494665797581166485377493)
                ·
                  refine ⟨433468729630808589501035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18494665797581166485377493 433468729630808589501035)
                  ·
                    rfl

theorem cell21_1899399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 1, 7].length) (baseStart_1899399 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1899399 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1899399 prefixEnd_1899399 := by exact prefixLift 1899399
  have htrace : WordTrace (prefixWord ++ tailWord_1899399) baseStart_1899399 baseEnd_1899399 := by
    simpa [prefixWord, tailWord_1899399, baseEnd_1899399] using wordTrace_append hprefix tailTrace_1899399
  have hstable : (prefixWord ++ tailWord_1899399).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1899399).length < 2 ^ (prefixWord ++ tailWord_1899399).sum := by decide
  have hdescent : baseEnd_1899399 < baseStart_1899399 := by decide
  rcases family_descends (prefixWord ++ tailWord_1899399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1899402 : List Nat := [3, 1, 2, 4, 1, 2, 3, 5]
def baseStart_1899402 : Nat := 118140960795 + 1899402 * 2 ^ 59
def prefixEnd_1899402 : Nat := 4983230072969 + 3 ^ 40 * 1899402 * 2
def baseEnd_1899402 : Nat := 144489804757227083650343

theorem tailTrace_1899402 : CollatzResearch.WordTrace tailWord_1899402 prefixEnd_1899402 144489804757227083650343 := by
  unfold tailWord_1899402
  simp only [CollatzResearch.WordTrace]
  refine ⟨17319220566199605220135115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46184588176532280587026973 17319220566199605220135115)
  ·
    refine ⟨25978830849299407830202673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17319220566199605220135115 25978830849299407830202673)
    ·
      refine ⟨19484123136974555872652005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25978830849299407830202673 19484123136974555872652005)
      ·
        refine ⟨3653273088182729226122251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19484123136974555872652005 3653273088182729226122251)
        ·
          refine ⟨5479909632274093839183377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3653273088182729226122251 5479909632274093839183377)
          ·
            refine ⟨4109932224205570379387533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5479909632274093839183377 4109932224205570379387533)
            ·
              refine ⟨1541224584077088892270325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4109932224205570379387533 1541224584077088892270325)
              ·
                refine ⟨144489804757227083650343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1541224584077088892270325 144489804757227083650343)
                ·
                  rfl

theorem cell21_1899402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 3, 5].length) (baseStart_1899402 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1899402 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1899402 prefixEnd_1899402 := by exact prefixLift 1899402
  have htrace : WordTrace (prefixWord ++ tailWord_1899402) baseStart_1899402 baseEnd_1899402 := by
    simpa [prefixWord, tailWord_1899402, baseEnd_1899402] using wordTrace_append hprefix tailTrace_1899402
  have hstable : (prefixWord ++ tailWord_1899402).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1899402).length < 2 ^ (prefixWord ++ tailWord_1899402).sum := by decide
  have hdescent : baseEnd_1899402 < baseStart_1899402 := by decide
  rcases family_descends (prefixWord ++ tailWord_1899402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1899478 : List Nat := [5, 2, 1, 1, 2, 3, 7]
def baseStart_1899478 : Nat := 118140960795 + 1899478 * 2 ^ 59
def prefixEnd_1899478 : Nat := 4983230072969 + 3 ^ 40 * 1899478 * 2
def baseEnd_1899478 : Nat := 48165195389680223076023

theorem tailTrace_1899478 : CollatzResearch.WordTrace tailWord_1899478 prefixEnd_1899478 48165195389680223076023 := by
  unfold tailWord_1899478
  simp only [CollatzResearch.WordTrace]
  refine ⟨4329978388282692866269193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46186436141682057240204725 4329978388282692866269193)
  ·
    refine ⟨3247483791212019649701895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4329978388282692866269193 3247483791212019649701895)
    ·
      refine ⟨4871225686818029474552843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3247483791212019649701895 4871225686818029474552843)
      ·
        refine ⟨7306838530227044211829265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4871225686818029474552843 7306838530227044211829265)
        ·
          refine ⟨5480128897670283158871949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7306838530227044211829265 5480128897670283158871949)
          ·
            refine ⟨2055048336626356184576981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5480128897670283158871949 2055048336626356184576981)
            ·
              refine ⟨48165195389680223076023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2055048336626356184576981 48165195389680223076023)
              ·
                rfl

theorem cell21_1899478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 7].length) (baseStart_1899478 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1899478 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1899478 prefixEnd_1899478 := by exact prefixLift 1899478
  have htrace : WordTrace (prefixWord ++ tailWord_1899478) baseStart_1899478 baseEnd_1899478 := by
    simpa [prefixWord, tailWord_1899478, baseEnd_1899478] using wordTrace_append hprefix tailTrace_1899478
  have hstable : (prefixWord ++ tailWord_1899478).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1899478).length < 2 ^ (prefixWord ++ tailWord_1899478).sum := by decide
  have hdescent : baseEnd_1899478 < baseStart_1899478 := by decide
  rcases family_descends (prefixWord ++ tailWord_1899478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1899630 : List Nat := [4, 1, 2, 2, 1, 4, 2, 5]
def baseStart_1899630 : Nat := 118140960795 + 1899630 * 2 ^ 59
def prefixEnd_1899630 : Nat := 4983230072969 + 3 ^ 40 * 1899630 * 2
def baseEnd_1899630 : Nat := 144507148992667840383521

theorem tailTrace_1899630 : CollatzResearch.WordTrace tailWord_1899630 prefixEnd_1899630 144507148992667840383521 := by
  unfold tailWord_1899630
  simp only [CollatzResearch.WordTrace]
  refine ⟨8660649763496551977480043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46190132071981610546560229 8660649763496551977480043)
  ·
    refine ⟨12990974645244827966220065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8660649763496551977480043 12990974645244827966220065)
    ·
      refine ⟨9743230983933620974665049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12990974645244827966220065 9743230983933620974665049)
      ·
        refine ⟨7307423237950215730998787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9743230983933620974665049 7307423237950215730998787)
        ·
          refine ⟨10961134856925323596498181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7307423237950215730998787 10961134856925323596498181)
          ·
            refine ⟨2055212785673498174343409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10961134856925323596498181 2055212785673498174343409)
            ·
              refine ⟨1541409589255123630757557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2055212785673498174343409 1541409589255123630757557)
              ·
                refine ⟨144507148992667840383521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1541409589255123630757557 144507148992667840383521)
                ·
                  rfl

theorem cell21_1899630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 2, 5].length) (baseStart_1899630 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1899630 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1899630 prefixEnd_1899630 := by exact prefixLift 1899630
  have htrace : WordTrace (prefixWord ++ tailWord_1899630) baseStart_1899630 baseEnd_1899630 := by
    simpa [prefixWord, tailWord_1899630, baseEnd_1899630] using wordTrace_append hprefix tailTrace_1899630
  have hstable : (prefixWord ++ tailWord_1899630).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1899630).length < 2 ^ (prefixWord ++ tailWord_1899630).sum := by decide
  have hdescent : baseEnd_1899630 < baseStart_1899630 := by decide
  rcases family_descends (prefixWord ++ tailWord_1899630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1899658 : List Nat := [3, 1, 2, 3, 1, 1, 2, 4, 4]
def baseStart_1899658 : Nat := 118140960795 + 1899658 * 2 ^ 59
def prefixEnd_1899658 : Nat := 4983230072969 + 3 ^ 40 * 1899658 * 2
def baseEnd_1899658 : Nat := 433527836959481694683839

theorem tailTrace_1899658 : CollatzResearch.WordTrace tailWord_1899658 prefixEnd_1899658 433527836959481694683839 := by
  unfold tailWord_1899658
  simp only [CollatzResearch.WordTrace]
  refine ⟨17321554837967744150464907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46190812901247317734573085 17321554837967744150464907)
  ·
    refine ⟨25982332256951616225697361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17321554837967744150464907 25982332256951616225697361)
    ·
      refine ⟨19486749192713712169273021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25982332256951616225697361 19486749192713712169273021)
      ·
        refine ⟨7307530947267642063477383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19486749192713712169273021 7307530947267642063477383)
        ·
          refine ⟨10961296420901463095216075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7307530947267642063477383 10961296420901463095216075)
          ·
            refine ⟨16441944631352194642824113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10961296420901463095216075 16441944631352194642824113)
            ·
              refine ⟨12331458473514145982118085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16441944631352194642824113 12331458473514145982118085)
              ·
                refine ⟨2312148463783902371647141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12331458473514145982118085 2312148463783902371647141)
                ·
                  refine ⟨433527836959481694683839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2312148463783902371647141 433527836959481694683839)
                  ·
                    rfl

theorem cell21_1899658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 4, 4].length) (baseStart_1899658 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1899658 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1899658 prefixEnd_1899658 := by exact prefixLift 1899658
  have htrace : WordTrace (prefixWord ++ tailWord_1899658) baseStart_1899658 baseEnd_1899658 := by
    simpa [prefixWord, tailWord_1899658, baseEnd_1899658] using wordTrace_append hprefix tailTrace_1899658
  have hstable : (prefixWord ++ tailWord_1899658).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1899658).length < 2 ^ (prefixWord ++ tailWord_1899658).sum := by decide
  have hdescent : baseEnd_1899658 < baseStart_1899658 := by decide
  rcases family_descends (prefixWord ++ tailWord_1899658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1899672 : List Nat := [2, 1, 2, 4, 2, 1, 1, 8]
def baseStart_1899672 : Nat := 118140960795 + 1899672 * 2 ^ 59
def prefixEnd_1899672 : Nat := 4983230072969 + 3 ^ 40 * 1899672 * 2
def baseEnd_1899672 : Nat := 144510343983406927150159

theorem tailTrace_1899672 : CollatzResearch.WordTrace tailWord_1899672 prefixEnd_1899672 144510343983406927150159 := by
  unfold tailWord_1899672
  simp only [CollatzResearch.WordTrace]
  refine ⟨34643364986910128496434635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46191153315880171328579513 34643364986910128496434635)
  ·
    refine ⟨51965047480365192744651953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34643364986910128496434635 51965047480365192744651953)
    ·
      refine ⟨38973785610273894558488965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51965047480365192744651953 38973785610273894558488965)
      ·
        refine ⟨7307584801926355229716681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38973785610273894558488965 7307584801926355229716681)
        ·
          refine ⟨5480688601444766422287511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7307584801926355229716681 5480688601444766422287511)
          ·
            refine ⟨8221032902167149633431267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5480688601444766422287511 8221032902167149633431267)
            ·
              refine ⟨12331549353250724450146901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8221032902167149633431267 12331549353250724450146901)
              ·
                refine ⟨144510343983406927150159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12331549353250724450146901 144510343983406927150159)
                ·
                  rfl

theorem cell21_1899672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 8].length) (baseStart_1899672 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1899672 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1899672 prefixEnd_1899672 := by exact prefixLift 1899672
  have htrace : WordTrace (prefixWord ++ tailWord_1899672) baseStart_1899672 baseEnd_1899672 := by
    simpa [prefixWord, tailWord_1899672, baseEnd_1899672] using wordTrace_append hprefix tailTrace_1899672
  have hstable : (prefixWord ++ tailWord_1899672).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1899672).length < 2 ^ (prefixWord ++ tailWord_1899672).sum := by decide
  have hdescent : baseEnd_1899672 < baseStart_1899672 := by decide
  rcases family_descends (prefixWord ++ tailWord_1899672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1899779 : List Nat := [1, 1, 1, 3, 2, 5, 2, 1, 5]
def baseStart_1899779 : Nat := 118140960795 + 1899779 * 2 ^ 59
def prefixEnd_1899779 : Nat := 4983230072969 + 3 ^ 40 * 1899779 * 2
def baseEnd_1899779 : Nat := 433555450808012373166925

theorem tailTrace_1899779 : CollatzResearch.WordTrace tailWord_1899779 prefixEnd_1899779 433555450808012373166925 := by
  unfold tailWord_1899779
  simp only [CollatzResearch.WordTrace]
  refine ⟨69290632584432614267014391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46193755056288409511342927 69290632584432614267014391)
  ·
    refine ⟨103935948876648921400521587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69290632584432614267014391 103935948876648921400521587)
    ·
      refine ⟨155903923314973382100782381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103935948876648921400521587 155903923314973382100782381)
      ·
        refine ⟨58463971243115018287793393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155903923314973382100782381 58463971243115018287793393)
        ·
          refine ⟨43847978432336263715845045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58463971243115018287793393 43847978432336263715845045)
          ·
            refine ⟨4110747978031524723360473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43847978432336263715845045 4110747978031524723360473)
            ·
              refine ⟨3083060983523643542520355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4110747978031524723360473 3083060983523643542520355)
              ·
                refine ⟨4624591475285465313780533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3083060983523643542520355 4624591475285465313780533)
                ·
                  refine ⟨433555450808012373166925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4624591475285465313780533 433555450808012373166925)
                  ·
                    rfl

theorem cell21_1899779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 2, 1, 5].length) (baseStart_1899779 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1899779 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1899779 prefixEnd_1899779 := by exact prefixLift 1899779
  have htrace : WordTrace (prefixWord ++ tailWord_1899779) baseStart_1899779 baseEnd_1899779 := by
    simpa [prefixWord, tailWord_1899779, baseEnd_1899779] using wordTrace_append hprefix tailTrace_1899779
  have hstable : (prefixWord ++ tailWord_1899779).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1899779).length < 2 ^ (prefixWord ++ tailWord_1899779).sum := by decide
  have hdescent : baseEnd_1899779 < baseStart_1899779 := by decide
  rcases family_descends (prefixWord ++ tailWord_1899779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1899813 : List Nat := [1, 3, 1, 2, 4, 3, 1, 3, 3]
def baseStart_1899813 : Nat := 118140960795 + 1899813 * 2 ^ 59
def prefixEnd_1899813 : Nat := 4983230072969 + 3 ^ 40 * 1899813 * 2
def baseEnd_1899813 : Nat := 433563210071235869600189

theorem tailTrace_1899813 : CollatzResearch.WordTrace tailWord_1899813 prefixEnd_1899813 433563210071235869600189 := by
  unfold tailWord_1899813
  simp only [CollatzResearch.WordTrace]
  refine ⟨69291872666309438073752093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46194581777539625382501395 69291872666309438073752093)
  ·
    refine ⟨25984452249866039277657035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69291872666309438073752093 25984452249866039277657035)
    ·
      refine ⟨38976678374799058916485553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25984452249866039277657035 38976678374799058916485553)
      ·
        refine ⟨29232508781099294187364165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38976678374799058916485553 29232508781099294187364165)
        ·
          refine ⟨5481095396456117660130781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29232508781099294187364165 5481095396456117660130781)
          ·
            refine ⟨2055410773671044122549043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5481095396456117660130781 2055410773671044122549043)
            ·
              refine ⟨3083116160506566183823565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2055410773671044122549043 3083116160506566183823565)
              ·
                refine ⟨1156168560189962318933837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3083116160506566183823565 1156168560189962318933837)
                ·
                  refine ⟨433563210071235869600189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1156168560189962318933837 433563210071235869600189)
                  ·
                    rfl

theorem cell21_1899813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 1, 3, 3].length) (baseStart_1899813 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1899813 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1899813 prefixEnd_1899813 := by exact prefixLift 1899813
  have htrace : WordTrace (prefixWord ++ tailWord_1899813) baseStart_1899813 baseEnd_1899813 := by
    simpa [prefixWord, tailWord_1899813, baseEnd_1899813] using wordTrace_append hprefix tailTrace_1899813
  have hstable : (prefixWord ++ tailWord_1899813).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1899813).length < 2 ^ (prefixWord ++ tailWord_1899813).sum := by decide
  have hdescent : baseEnd_1899813 < baseStart_1899813 := by decide
  rcases family_descends (prefixWord ++ tailWord_1899813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1899830 : List Nat := [5, 1, 2, 3, 1, 2, 1, 1, 5]
def baseStart_1899830 : Nat := 118140960795 + 1899830 * 2 ^ 59
def prefixEnd_1899830 : Nat := 4983230072969 + 3 ^ 40 * 1899830 * 2
def baseEnd_1899830 : Nat := 433567089702847617816821

theorem tailTrace_1899830 : CollatzResearch.WordTrace tailWord_1899830 prefixEnd_1899830 433567089702847617816821 := by
  unfold tailWord_1899830
  simp only [CollatzResearch.WordTrace]
  refine ⟨4330780794202990623570059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46194995138165233318080629 4330780794202990623570059)
  ·
    refine ⟨6496171191304485935355089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4330780794202990623570059 6496171191304485935355089)
    ·
      refine ⟨4872128393478364451516317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6496171191304485935355089 4872128393478364451516317)
      ·
        refine ⟨1827048147554386669318619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4872128393478364451516317 1827048147554386669318619)
        ·
          refine ⟨2740572221331580003977929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1827048147554386669318619 2740572221331580003977929)
          ·
            refine ⟨2055429165998685002983447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2740572221331580003977929 2055429165998685002983447)
            ·
              refine ⟨3083143748998027504475171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2055429165998685002983447 3083143748998027504475171)
              ·
                refine ⟨4624715623497041256712757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3083143748998027504475171 4624715623497041256712757)
                ·
                  refine ⟨433567089702847617816821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4624715623497041256712757 433567089702847617816821)
                  ·
                    rfl

theorem cell21_1899830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 1, 1, 5].length) (baseStart_1899830 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1899830 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1899830 prefixEnd_1899830 := by exact prefixLift 1899830
  have htrace : WordTrace (prefixWord ++ tailWord_1899830) baseStart_1899830 baseEnd_1899830 := by
    simpa [prefixWord, tailWord_1899830, baseEnd_1899830] using wordTrace_append hprefix tailTrace_1899830
  have hstable : (prefixWord ++ tailWord_1899830).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1899830).length < 2 ^ (prefixWord ++ tailWord_1899830).sum := by decide
  have hdescent : baseEnd_1899830 < baseStart_1899830 := by decide
  rcases family_descends (prefixWord ++ tailWord_1899830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1899841 : List Nat := [1, 2, 5, 2, 1, 2, 2, 6]
def baseStart_1899841 : Nat := 118140960795 + 1899841 * 2 ^ 59
def prefixEnd_1899841 : Nat := 4983230072969 + 3 ^ 40 * 1899841 * 2
def baseEnd_1899841 : Nat := 144523200017571347711155

theorem tailTrace_1899841 : CollatzResearch.WordTrace tailWord_1899841 prefixEnd_1899841 144523200017571347711155 := by
  unfold tailWord_1899841
  simp only [CollatzResearch.WordTrace]
  refine ⟨69292893910207998855771377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46195262606805332570514251 69292893910207998855771377)
  ·
    refine ⟨51969670432655999141828533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69292893910207998855771377 51969670432655999141828533)
    ·
      refine ⟨4872156603061499919546425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 51969670432655999141828533 4872156603061499919546425)
      ·
        refine ⟨3654117452296124939659819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4872156603061499919546425 3654117452296124939659819)
        ·
          refine ⟨5481176178444187409489729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3654117452296124939659819 5481176178444187409489729)
          ·
            refine ⟨4110882133833140557117297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5481176178444187409489729 4110882133833140557117297)
            ·
              refine ⟨3083161600374855417837973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4110882133833140557117297 3083161600374855417837973)
              ·
                refine ⟨144523200017571347711155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3083161600374855417837973 144523200017571347711155)
                ·
                  rfl

theorem cell21_1899841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 2, 6].length) (baseStart_1899841 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1899841 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1899841 prefixEnd_1899841 := by exact prefixLift 1899841
  have htrace : WordTrace (prefixWord ++ tailWord_1899841) baseStart_1899841 baseEnd_1899841 := by
    simpa [prefixWord, tailWord_1899841, baseEnd_1899841] using wordTrace_append hprefix tailTrace_1899841
  have hstable : (prefixWord ++ tailWord_1899841).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1899841).length < 2 ^ (prefixWord ++ tailWord_1899841).sum := by decide
  have hdescent : baseEnd_1899841 < baseStart_1899841 := by decide
  rcases family_descends (prefixWord ++ tailWord_1899841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1899844 : List Nat := [2, 3, 4, 1, 1, 1, 4, 1, 4]
def baseStart_1899844 : Nat := 118140960795 + 1899844 * 2 ^ 59
def prefixEnd_1899844 : Nat := 4983230072969 + 3 ^ 40 * 1899844 * 2
def baseEnd_1899844 : Nat := 433570284693586704583459

theorem tailTrace_1899844 : CollatzResearch.WordTrace tailWord_1899844 prefixEnd_1899844 433570284693586704583459 := by
  unfold tailWord_1899844
  simp only [CollatzResearch.WordTrace]
  refine ⟨34646501664598565184065293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46195335552798086912087057 34646501664598565184065293)
  ·
    refine ⟨12992438124224461944024485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34646501664598565184065293 12992438124224461944024485)
    ·
      refine ⟨2436082148292086614504591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12992438124224461944024485 2436082148292086614504591)
      ·
        refine ⟨3654123222438129921756887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2436082148292086614504591 3654123222438129921756887)
        ·
          refine ⟨5481184833657194882635331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3654123222438129921756887 5481184833657194882635331)
          ·
            refine ⟨8221777250485792323952997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5481184833657194882635331 8221777250485792323952997)
            ·
              refine ⟨1541583234466086060741187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8221777250485792323952997 1541583234466086060741187)
              ·
                refine ⟨2312374851699129091111781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1541583234466086060741187 2312374851699129091111781)
                ·
                  refine ⟨433570284693586704583459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2312374851699129091111781 433570284693586704583459)
                  ·
                    rfl

theorem cell21_1899844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 4, 1, 4].length) (baseStart_1899844 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1899844 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1899844 prefixEnd_1899844 := by exact prefixLift 1899844
  have htrace : WordTrace (prefixWord ++ tailWord_1899844) baseStart_1899844 baseEnd_1899844 := by
    simpa [prefixWord, tailWord_1899844, baseEnd_1899844] using wordTrace_append hprefix tailTrace_1899844
  have hstable : (prefixWord ++ tailWord_1899844).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1899844).length < 2 ^ (prefixWord ++ tailWord_1899844).sum := by decide
  have hdescent : baseEnd_1899844 < baseStart_1899844 := by decide
  rcases family_descends (prefixWord ++ tailWord_1899844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1899959 : List Nat := [1, 1, 3, 1, 3, 2, 2, 8]
def baseStart_1899959 : Nat := 118140960795 + 1899959 * 2 ^ 59
def prefixEnd_1899959 : Nat := 4983230072969 + 3 ^ 40 * 1899959 * 2
def baseEnd_1899959 : Nat := 144532176420124020055519

theorem tailTrace_1899959 : CollatzResearch.WordTrace tailWord_1899959 prefixEnd_1899959 144532176420124020055519 := by
  unfold tailWord_1899959
  simp only [CollatzResearch.WordTrace]
  refine ⟨69297197723780505008566931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46198131815853670005711287 69297197723780505008566931)
  ·
    refine ⟨103945796585670757512850397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69297197723780505008566931 103945796585670757512850397)
    ·
      refine ⟨38979673719626534067318899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103945796585670757512850397 38979673719626534067318899)
      ·
        refine ⟨58469510579439801100978349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38979673719626534067318899 58469510579439801100978349)
        ·
          refine ⟨21926066467289925412866881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58469510579439801100978349 21926066467289925412866881)
          ·
            refine ⟨16444549850467444059650161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21926066467289925412866881 16444549850467444059650161)
            ·
              refine ⟨12333412387850583044737621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16444549850467444059650161 12333412387850583044737621)
              ·
                refine ⟨144532176420124020055519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12333412387850583044737621 144532176420124020055519)
                ·
                  rfl

theorem cell21_1899959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 8].length) (baseStart_1899959 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1899959 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1899959 prefixEnd_1899959 := by exact prefixLift 1899959
  have htrace : WordTrace (prefixWord ++ tailWord_1899959) baseStart_1899959 baseEnd_1899959 := by
    simpa [prefixWord, tailWord_1899959, baseEnd_1899959] using wordTrace_append hprefix tailTrace_1899959
  have hstable : (prefixWord ++ tailWord_1899959).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1899959).length < 2 ^ (prefixWord ++ tailWord_1899959).sum := by decide
  have hdescent : baseEnd_1899959 < baseStart_1899959 := by decide
  rcases family_descends (prefixWord ++ tailWord_1899959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1900007 : List Nat := [1, 1, 5, 2, 1, 2, 3, 1, 5]
def baseStart_1900007 : Nat := 118140960795 + 1900007 * 2 ^ 59
def prefixEnd_1900007 : Nat := 4983230072969 + 3 ^ 40 * 1900007 * 2
def baseEnd_1900007 : Nat := 433607483514334643366459

theorem tailTrace_1900007 : CollatzResearch.WordTrace tailWord_1900007 prefixEnd_1900007 433607483514334643366459 := by
  unfold tailWord_1900007
  simp only [CollatzResearch.WordTrace]
  refine ⟨69298948427606609206314275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46199298951737739470876183 69298948427606609206314275)
  ·
    refine ⟨103948422641409913809471413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69298948427606609206314275 103948422641409913809471413)
    ·
      refine ⟨9745164622632179419637945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 103948422641409913809471413 9745164622632179419637945)
      ·
        refine ⟨7308873466974134564728459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9745164622632179419637945 7308873466974134564728459)
        ·
          refine ⟨10963310200461201847092689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7308873466974134564728459 10963310200461201847092689)
          ·
            refine ⟨8222482650345901385319517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10963310200461201847092689 8222482650345901385319517)
            ·
              refine ⟨3083430993879713019494819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8222482650345901385319517 3083430993879713019494819)
              ·
                refine ⟨4625146490819569529242229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3083430993879713019494819 4625146490819569529242229)
                ·
                  refine ⟨433607483514334643366459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4625146490819569529242229 433607483514334643366459)
                  ·
                    rfl

theorem cell21_1900007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 3, 1, 5].length) (baseStart_1900007 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1900007 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1900007 prefixEnd_1900007 := by exact prefixLift 1900007
  have htrace : WordTrace (prefixWord ++ tailWord_1900007) baseStart_1900007 baseEnd_1900007 := by
    simpa [prefixWord, tailWord_1900007, baseEnd_1900007] using wordTrace_append hprefix tailTrace_1900007
  have hstable : (prefixWord ++ tailWord_1900007).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1900007).length < 2 ^ (prefixWord ++ tailWord_1900007).sum := by decide
  have hdescent : baseEnd_1900007 < baseStart_1900007 := by decide
  rcases family_descends (prefixWord ++ tailWord_1900007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1900013 : List Nat := [1, 5, 1, 3, 3, 1, 2, 1, 4]
def baseStart_1900013 : Nat := 118140960795 + 1900013 * 2 ^ 59
def prefixEnd_1900013 : Nat := 4983230072969 + 3 ^ 40 * 1900013 * 2
def baseEnd_1900013 : Nat := 433608852796079966266447

theorem tailTrace_1900013 : CollatzResearch.WordTrace tailWord_1900013 prefixEnd_1900013 433608852796079966266447 := by
  unfold tailWord_1900013
  simp only [CollatzResearch.WordTrace]
  refine ⟨69299167265584872231032693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46199444843723248154021795 69299167265584872231032693)
  ·
    refine ⟨6496796931148581771659315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 69299167265584872231032693 6496796931148581771659315)
    ·
      refine ⟨9745195396722872657488973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6496796931148581771659315 9745195396722872657488973)
      ·
        refine ⟨3654448273771077246558365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9745195396722872657488973 3654448273771077246558365)
        ·
          refine ⟨1370418102664153967459387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3654448273771077246558365 1370418102664153967459387)
          ·
            refine ⟨2055627153996230951189081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1370418102664153967459387 2055627153996230951189081)
            ·
              refine ⟨1541720365497173213391811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2055627153996230951189081 1541720365497173213391811)
              ·
                refine ⟨2312580548245759820087717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1541720365497173213391811 2312580548245759820087717)
                ·
                  refine ⟨433608852796079966266447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2312580548245759820087717 433608852796079966266447)
                  ·
                    rfl

theorem cell21_1900013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 2, 1, 4].length) (baseStart_1900013 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1900013 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1900013 prefixEnd_1900013 := by exact prefixLift 1900013
  have htrace : WordTrace (prefixWord ++ tailWord_1900013) baseStart_1900013 baseEnd_1900013 := by
    simpa [prefixWord, tailWord_1900013, baseEnd_1900013] using wordTrace_append hprefix tailTrace_1900013
  have hstable : (prefixWord ++ tailWord_1900013).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1900013).length < 2 ^ (prefixWord ++ tailWord_1900013).sum := by decide
  have hdescent : baseEnd_1900013 < baseStart_1900013 := by decide
  rcases family_descends (prefixWord ++ tailWord_1900013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1900052 : List Nat := [2, 4, 3, 1, 11]
def baseStart_1900052 : Nat := 118140960795 + 1900052 * 2 ^ 59
def prefixEnd_1900052 : Nat := 4983230072969 + 3 ^ 40 * 1900052 * 2
def baseEnd_1900052 : Nat := 5353305594165735371807

theorem tailTrace_1900052 : CollatzResearch.WordTrace tailWord_1900052 prefixEnd_1900052 5353305594165735371807 := by
  unfold tailWord_1900052
  simp only [CollatzResearch.WordTrace]
  refine ⟨34650294856221790945851205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46200393141629054594468273 34650294856221790945851205)
  ·
    refine ⟨6496930285541585802347101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34650294856221790945851205 6496930285541585802347101)
    ·
      refine ⟨2436348857078094675880163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6496930285541585802347101 2436348857078094675880163)
      ·
        refine ⟨3654523285617142013820245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2436348857078094675880163 3654523285617142013820245)
        ·
          refine ⟨5353305594165735371807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 3654523285617142013820245 5353305594165735371807)
          ·
            rfl

theorem cell21_1900052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 11].length) (baseStart_1900052 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1900052 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1900052 prefixEnd_1900052 := by exact prefixLift 1900052
  have htrace : WordTrace (prefixWord ++ tailWord_1900052) baseStart_1900052 baseEnd_1900052 := by
    simpa [prefixWord, tailWord_1900052, baseEnd_1900052] using wordTrace_append hprefix tailTrace_1900052
  have hstable : (prefixWord ++ tailWord_1900052).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1900052).length < 2 ^ (prefixWord ++ tailWord_1900052).sum := by decide
  have hdescent : baseEnd_1900052 < baseStart_1900052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1900052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1900080 : List Nat := [2, 1, 1, 1, 2, 3, 1, 2, 8]
def baseStart_1900080 : Nat := 118140960795 + 1900080 * 2 ^ 59
def prefixEnd_1900080 : Nat := 4983230072969 + 3 ^ 40 * 1900080 * 2
def baseEnd_1900080 : Nat := 433624143108902738649643

theorem tailTrace_1900080 : CollatzResearch.WordTrace tailWord_1900080 prefixEnd_1900080 433624143108902738649643 := by
  unfold tailWord_1900080
  simp only [CollatzResearch.WordTrace]
  refine ⟨34650805478171071336860847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46201073970894761782481129 34650805478171071336860847)
  ·
    refine ⟨51976208217256607005291271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34650805478171071336860847 51976208217256607005291271)
    ·
      refine ⟨77964312325884910507936907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51976208217256607005291271 77964312325884910507936907)
      ·
        refine ⟨116946468488827365761905361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77964312325884910507936907 116946468488827365761905361)
        ·
          refine ⟨87709851366620524321429021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116946468488827365761905361 87709851366620524321429021)
          ·
            refine ⟨32891194262482696620535883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87709851366620524321429021 32891194262482696620535883)
            ·
              refine ⟨49336791393724044930803825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32891194262482696620535883 49336791393724044930803825)
              ·
                refine ⟨37002593545293033698102869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49336791393724044930803825 37002593545293033698102869)
                ·
                  refine ⟨433624143108902738649643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37002593545293033698102869 433624143108902738649643)
                  ·
                    rfl

theorem cell21_1900080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 8].length) (baseStart_1900080 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1900080 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1900080 prefixEnd_1900080 := by exact prefixLift 1900080
  have htrace : WordTrace (prefixWord ++ tailWord_1900080) baseStart_1900080 baseEnd_1900080 := by
    simpa [prefixWord, tailWord_1900080, baseEnd_1900080] using wordTrace_append hprefix tailTrace_1900080
  have hstable : (prefixWord ++ tailWord_1900080).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1900080).length < 2 ^ (prefixWord ++ tailWord_1900080).sum := by decide
  have hdescent : baseEnd_1900080 < baseStart_1900080 := by decide
  rcases family_descends (prefixWord ++ tailWord_1900080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1900086 : List Nat := [5, 1, 2, 1, 3, 1, 3, 5]
def baseStart_1900086 : Nat := 118140960795 + 1900086 * 2 ^ 59
def prefixEnd_1900086 : Nat := 4983230072969 + 3 ^ 40 * 1900086 * 2
def baseEnd_1900086 : Nat := 144541837463549353849877

theorem tailTrace_1900086 : CollatzResearch.WordTrace tailWord_1900086 prefixEnd_1900086 144541837463549353849877 := by
  unfold tailWord_1900086
  simp only [CollatzResearch.WordTrace]
  refine ⟨4331364362145025356152507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46201219862880270465626741 4331364362145025356152507)
  ·
    refine ⟨6497046543217538034228761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4331364362145025356152507 6497046543217538034228761)
    ·
      refine ⟨4872784907413153525671571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6497046543217538034228761 4872784907413153525671571)
      ·
        refine ⟨7309177361119730288507357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4872784907413153525671571 7309177361119730288507357)
        ·
          refine ⟨2740941510419898858190259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7309177361119730288507357 2740941510419898858190259)
          ·
            refine ⟨4111412265629848287285389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2740941510419898858190259 4111412265629848287285389)
            ·
              refine ⟨1541779599611193107732021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4111412265629848287285389 1541779599611193107732021)
              ·
                refine ⟨144541837463549353849877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1541779599611193107732021 144541837463549353849877)
                ·
                  rfl

theorem cell21_1900086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 3, 5].length) (baseStart_1900086 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1900086 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1900086 prefixEnd_1900086 := by exact prefixLift 1900086
  have htrace : WordTrace (prefixWord ++ tailWord_1900086) baseStart_1900086 baseEnd_1900086 := by
    simpa [prefixWord, tailWord_1900086, baseEnd_1900086] using wordTrace_append hprefix tailTrace_1900086
  have hstable : (prefixWord ++ tailWord_1900086).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1900086).length < 2 ^ (prefixWord ++ tailWord_1900086).sum := by decide
  have hdescent : baseEnd_1900086 < baseStart_1900086 := by decide
  rcases family_descends (prefixWord ++ tailWord_1900086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1900097 : List Nat := [1, 2, 5, 1, 1, 1, 2, 2, 6]
def baseStart_1900097 : Nat := 118140960795 + 1900097 * 2 ^ 59
def prefixEnd_1900097 : Nat := 4983230072969 + 3 ^ 40 * 1900097 * 2
def baseEnd_1900097 : Nat := 433628022740514486866275

theorem tailTrace_1900097 : CollatzResearch.WordTrace tailWord_1900097 prefixEnd_1900097 433628022740514486866275 := by
  unfold tailWord_1900097
  simp only [CollatzResearch.WordTrace]
  refine ⟨69302230997280554577090545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46201487331520369718060363 69302230997280554577090545)
  ·
    refine ⟨51976673247960415932817909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69302230997280554577090545 51976673247960415932817909)
    ·
      refine ⟨4872813116996288993701679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 51976673247960415932817909 4872813116996288993701679)
      ·
        refine ⟨7309219675494433490552519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4872813116996288993701679 7309219675494433490552519)
        ·
          refine ⟨10963829513241650235828779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7309219675494433490552519 10963829513241650235828779)
          ·
            refine ⟨16445744269862475353743169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10963829513241650235828779 16445744269862475353743169)
            ·
              refine ⟨12334308202396856515307377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16445744269862475353743169 12334308202396856515307377)
              ·
                refine ⟨9250731151797642386480533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12334308202396856515307377 9250731151797642386480533)
                ·
                  refine ⟨433628022740514486866275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9250731151797642386480533 433628022740514486866275)
                  ·
                    rfl

theorem cell21_1900097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 2, 6].length) (baseStart_1900097 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1900097 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1900097 prefixEnd_1900097 := by exact prefixLift 1900097
  have htrace : WordTrace (prefixWord ++ tailWord_1900097) baseStart_1900097 baseEnd_1900097 := by
    simpa [prefixWord, tailWord_1900097, baseEnd_1900097] using wordTrace_append hprefix tailTrace_1900097
  have hstable : (prefixWord ++ tailWord_1900097).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1900097).length < 2 ^ (prefixWord ++ tailWord_1900097).sum := by decide
  have hdescent : baseEnd_1900097 < baseStart_1900097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1900097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1900114 : List Nat := [3, 2, 2, 1, 2, 2, 3, 2, 4]
def baseStart_1900114 : Nat := 118140960795 + 1900114 * 2 ^ 59
def prefixEnd_1900114 : Nat := 4983230072969 + 3 ^ 40 * 1900114 * 2
def baseEnd_1900114 : Nat := 433631902372126235082907

theorem tailTrace_1900114 : CollatzResearch.WordTrace tailWord_1900114 prefixEnd_1900114 433631902372126235082907 := by
  unfold tailWord_1900114
  simp only [CollatzResearch.WordTrace]
  refine ⟨17325712759554741620114849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46201900692145977653639597 17325712759554741620114849)
  ·
    refine ⟨12994284569666056215086137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17325712759554741620114849 12994284569666056215086137)
    ·
      refine ⟨9745713427249542161314603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12994284569666056215086137 9745713427249542161314603)
      ·
        refine ⟨14618570140874313241971905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9745713427249542161314603 14618570140874313241971905)
        ·
          refine ⟨10963927605655734931478929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14618570140874313241971905 10963927605655734931478929)
          ·
            refine ⟨8222945704241801198609197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10963927605655734931478929 8222945704241801198609197)
            ·
              refine ⟨3083604639090675449478449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8222945704241801198609197 3083604639090675449478449)
              ·
                refine ⟨2312703479318006587108837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3083604639090675449478449 2312703479318006587108837)
                ·
                  refine ⟨433631902372126235082907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2312703479318006587108837 433631902372126235082907)
                  ·
                    rfl

theorem cell21_1900114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 3, 2, 4].length) (baseStart_1900114 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1900114 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1900114 prefixEnd_1900114 := by exact prefixLift 1900114
  have htrace : WordTrace (prefixWord ++ tailWord_1900114) baseStart_1900114 baseEnd_1900114 := by
    simpa [prefixWord, tailWord_1900114, baseEnd_1900114] using wordTrace_append hprefix tailTrace_1900114
  have hstable : (prefixWord ++ tailWord_1900114).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1900114).length < 2 ^ (prefixWord ++ tailWord_1900114).sum := by decide
  have hdescent : baseEnd_1900114 < baseStart_1900114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1900114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1900249 : List Nat := [1, 2, 1, 2, 3, 3, 2, 3, 4]
def baseStart_1900249 : Nat := 118140960795 + 1900249 * 2 ^ 59
def prefixEnd_1900249 : Nat := 4983230072969 + 3 ^ 40 * 1900249 * 2
def baseEnd_1900249 : Nat := 433662711211396000332631

theorem tailTrace_1900249 : CollatzResearch.WordTrace tailWord_1900249 prefixEnd_1900249 433662711211396000332631 := by
  unfold tailWord_1900249
  simp only [CollatzResearch.WordTrace]
  refine ⟨69307774892729884536623801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46205183261819923024415867 69307774892729884536623801)
  ·
    refine ⟨51980831169547413402467851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69307774892729884536623801 51980831169547413402467851)
    ·
      refine ⟨77971246754321120103701777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51980831169547413402467851 77971246754321120103701777)
      ·
        refine ⟨58478435065740840077776333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77971246754321120103701777 58478435065740840077776333)
        ·
          refine ⟨21929413149652815029166125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58478435065740840077776333 21929413149652815029166125)
          ·
            refine ⟨8223529931119805635937297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21929413149652815029166125 8223529931119805635937297)
            ·
              refine ⟨6167647448339854226952973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8223529931119805635937297 6167647448339854226952973)
              ·
                refine ⟨2312867793127445335107365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6167647448339854226952973 2312867793127445335107365)
                ·
                  refine ⟨433662711211396000332631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2312867793127445335107365 433662711211396000332631)
                  ·
                    rfl

theorem cell21_1900249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 3, 4].length) (baseStart_1900249 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1900249 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1900249 prefixEnd_1900249 := by exact prefixLift 1900249
  have htrace : WordTrace (prefixWord ++ tailWord_1900249) baseStart_1900249 baseEnd_1900249 := by
    simpa [prefixWord, tailWord_1900249, baseEnd_1900249] using wordTrace_append hprefix tailTrace_1900249
  have hstable : (prefixWord ++ tailWord_1900249).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1900249).length < 2 ^ (prefixWord ++ tailWord_1900249).sum := by decide
  have hdescent : baseEnd_1900249 < baseStart_1900249 := by decide
  rcases family_descends (prefixWord ++ tailWord_1900249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1900252 : List Nat := [2, 2, 5, 1, 2, 1, 1, 2, 5]
def baseStart_1900252 : Nat := 118140960795 + 1900252 * 2 ^ 59
def prefixEnd_1900252 : Nat := 4983230072969 + 3 ^ 40 * 1900252 * 2
def baseEnd_1900252 : Nat := 433663395852268661782625

theorem tailTrace_1900252 : CollatzResearch.WordTrace tailWord_1900252 prefixEnd_1900252 433663395852268661782625 := by
  unfold tailWord_1900252
  simp only [CollatzResearch.WordTrace]
  refine ⟨34653942155859508024491505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46205256207812677365988673 34653942155859508024491505)
  ·
    refine ⟨25990456616894631018368629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34653942155859508024491505 25990456616894631018368629)
    ·
      refine ⟨2436605307833871657972059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25990456616894631018368629 2436605307833871657972059)
      ·
        refine ⟨3654907961750807486958089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2436605307833871657972059 3654907961750807486958089)
        ·
          refine ⟨2741180971313105615218567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3654907961750807486958089 2741180971313105615218567)
          ·
            refine ⟨4111771456969658422827851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2741180971313105615218567 4111771456969658422827851)
            ·
              refine ⟨6167657185454487634241777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4111771456969658422827851 6167657185454487634241777)
              ·
                refine ⟨4625742889090865725681333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6167657185454487634241777 4625742889090865725681333)
                ·
                  refine ⟨433663395852268661782625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4625742889090865725681333 433663395852268661782625)
                  ·
                    rfl

theorem cell21_1900252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 2, 5].length) (baseStart_1900252 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1900252 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1900252 prefixEnd_1900252 := by exact prefixLift 1900252
  have htrace : WordTrace (prefixWord ++ tailWord_1900252) baseStart_1900252 baseEnd_1900252 := by
    simpa [prefixWord, tailWord_1900252, baseEnd_1900252] using wordTrace_append hprefix tailTrace_1900252
  have hstable : (prefixWord ++ tailWord_1900252).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1900252).length < 2 ^ (prefixWord ++ tailWord_1900252).sum := by decide
  have hdescent : baseEnd_1900252 < baseStart_1900252 := by decide
  rcases family_descends (prefixWord ++ tailWord_1900252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1900328 : List Nat := [2, 1, 5, 1, 1, 2, 3, 3, 3]
def baseStart_1900328 : Nat := 118140960795 + 1900328 * 2 ^ 59
def prefixEnd_1900328 : Nat := 4983230072969 + 3 ^ 40 * 1900328 * 2
def baseEnd_1900328 : Nat := 433680740087709418515803

theorem tailTrace_1900328 : CollatzResearch.WordTrace tailWord_1900328 prefixEnd_1900328 433680740087709418515803 := by
  unfold tailWord_1900328
  simp only [CollatzResearch.WordTrace]
  refine ⟨34655328129721840514374819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46207104172962454019166425 34655328129721840514374819)
  ·
    refine ⟨51982992194582760771562229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34655328129721840514374819 51982992194582760771562229)
    ·
      refine ⟨4873405518242133822333959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 51982992194582760771562229 4873405518242133822333959)
      ·
        refine ⟨7310108277363200733500939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4873405518242133822333959 7310108277363200733500939)
        ·
          refine ⟨10965162416044801100251409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7310108277363200733500939 10965162416044801100251409)
          ·
            refine ⟨8223871812033600825188557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10965162416044801100251409 8223871812033600825188557)
            ·
              refine ⟨3083951929512600309445709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8223871812033600825188557 3083951929512600309445709)
              ·
                refine ⟨1156481973567225116042141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3083951929512600309445709 1156481973567225116042141)
                ·
                  refine ⟨433680740087709418515803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1156481973567225116042141 433680740087709418515803)
                  ·
                    rfl

theorem cell21_1900328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 3, 3, 3].length) (baseStart_1900328 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1900328 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1900328 prefixEnd_1900328 := by exact prefixLift 1900328
  have htrace : WordTrace (prefixWord ++ tailWord_1900328) baseStart_1900328 baseEnd_1900328 := by
    simpa [prefixWord, tailWord_1900328, baseEnd_1900328] using wordTrace_append hprefix tailTrace_1900328
  have hstable : (prefixWord ++ tailWord_1900328).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1900328).length < 2 ^ (prefixWord ++ tailWord_1900328).sum := by decide
  have hdescent : baseEnd_1900328 < baseStart_1900328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1900328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1900342 : List Nat := [5, 1, 2, 2, 1, 1, 2, 1, 6]
def baseStart_1900342 : Nat := 118140960795 + 1900342 * 2 ^ 59
def prefixEnd_1900342 : Nat := 4983230072969 + 3 ^ 40 * 1900342 * 2
def baseEnd_1900342 : Nat := 433683935078448505282441

theorem tailTrace_1900342 : CollatzResearch.WordTrace tailWord_1900342 prefixEnd_1900342 433683935078448505282441 := by
  unfold tailWord_1900342
  simp only [CollatzResearch.WordTrace]
  refine ⟨4331947930087060088734955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46207444587595307613172853 4331947930087060088734955)
  ·
    refine ⟨6497921895130590133102433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4331947930087060088734955 6497921895130590133102433)
    ·
      refine ⟨4873441421347942599826825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6497921895130590133102433 4873441421347942599826825)
      ·
        refine ⟨3655081066010956949870119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4873441421347942599826825 3655081066010956949870119)
        ·
          refine ⟨5482621599016435424805179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3655081066010956949870119 5482621599016435424805179)
          ·
            refine ⟨8223932398524653137207769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5482621599016435424805179 8223932398524653137207769)
            ·
              refine ⟨6167949298893489852905827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8223932398524653137207769 6167949298893489852905827)
              ·
                refine ⟨9251923948340234779358741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6167949298893489852905827 9251923948340234779358741)
                ·
                  refine ⟨433683935078448505282441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9251923948340234779358741 433683935078448505282441)
                  ·
                    rfl

theorem cell21_1900342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 1, 6].length) (baseStart_1900342 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1900342 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1900342 prefixEnd_1900342 := by exact prefixLift 1900342
  have htrace : WordTrace (prefixWord ++ tailWord_1900342) baseStart_1900342 baseEnd_1900342 := by
    simpa [prefixWord, tailWord_1900342, baseEnd_1900342] using wordTrace_append hprefix tailTrace_1900342
  have hstable : (prefixWord ++ tailWord_1900342).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1900342).length < 2 ^ (prefixWord ++ tailWord_1900342).sum := by decide
  have hdescent : baseEnd_1900342 < baseStart_1900342 := by decide
  rcases family_descends (prefixWord ++ tailWord_1900342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1900345 : List Nat := [1, 2, 1, 7, 2, 1, 1, 1, 5]
def baseStart_1900345 : Nat := 118140960795 + 1900345 * 2 ^ 59
def prefixEnd_1900345 : Nat := 4983230072969 + 3 ^ 40 * 1900345 * 2
def baseEnd_1900345 : Nat := 433684619719321166732435

theorem tailTrace_1900345 : CollatzResearch.WordTrace tailWord_1900345 prefixEnd_1900345 433684619719321166732435 := by
  unfold tailWord_1900345
  simp only [CollatzResearch.WordTrace]
  refine ⟨69311276300382092932118489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46207517533588061954745659 69311276300382092932118489)
  ·
    refine ⟨51983457225286569699088867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69311276300382092932118489 51983457225286569699088867)
    ·
      refine ⟨77975185837929854548633301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51983457225286569699088867 77975185837929854548633301)
      ·
        refine ⟨1827543418076480965983593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 77975185837929854548633301 1827543418076480965983593)
        ·
          refine ⟨1370657563557360724487695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1827543418076480965983593 1370657563557360724487695)
          ·
            refine ⟨2055986345336041086731543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1370657563557360724487695 2055986345336041086731543)
            ·
              refine ⟨3083979518004061630097315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2055986345336041086731543 3083979518004061630097315)
              ·
                refine ⟨4625969277006092445145973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3083979518004061630097315 4625969277006092445145973)
                ·
                  refine ⟨433684619719321166732435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4625969277006092445145973 433684619719321166732435)
                  ·
                    rfl

theorem cell21_1900345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 1, 1, 5].length) (baseStart_1900345 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1900345 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1900345 prefixEnd_1900345 := by exact prefixLift 1900345
  have htrace : WordTrace (prefixWord ++ tailWord_1900345) baseStart_1900345 baseEnd_1900345 := by
    simpa [prefixWord, tailWord_1900345, baseEnd_1900345] using wordTrace_append hprefix tailTrace_1900345
  have hstable : (prefixWord ++ tailWord_1900345).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1900345).length < 2 ^ (prefixWord ++ tailWord_1900345).sum := by decide
  have hdescent : baseEnd_1900345 < baseStart_1900345 := by decide
  rcases family_descends (prefixWord ++ tailWord_1900345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1900401 : List Nat := [1, 2, 2, 2, 1, 3, 4, 2, 4]
def baseStart_1900401 : Nat := 118140960795 + 1900401 * 2 ^ 59
def prefixEnd_1900401 : Nat := 4983230072969 + 3 ^ 40 * 1900401 * 2
def baseEnd_1900401 : Nat := 433697399682277513798987

theorem tailTrace_1900401 : CollatzResearch.WordTrace tailWord_1900401 prefixEnd_1900401 433697399682277513798987 := by
  unfold tailWord_1900401
  simp only [CollatzResearch.WordTrace]
  refine ⟨69313318788179214496157057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46208879192119476330771371 69313318788179214496157057)
  ·
    refine ⟨51984989091134410872117793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69313318788179214496157057 51984989091134410872117793)
    ·
      refine ⟨38988741818350808154088345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51984989091134410872117793 38988741818350808154088345)
      ·
        refine ⟨29241556363763106115566259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38988741818350808154088345 29241556363763106115566259)
        ·
          refine ⟨43862334545644659173349389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29241556363763106115566259 43862334545644659173349389)
          ·
            refine ⟨16448375454616747190006021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43862334545644659173349389 16448375454616747190006021)
            ·
              refine ⟨3084070397740640098126129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16448375454616747190006021 3084070397740640098126129)
              ·
                refine ⟨2313052798305480073594597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3084070397740640098126129 2313052798305480073594597)
                ·
                  refine ⟨433697399682277513798987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2313052798305480073594597 433697399682277513798987)
                  ·
                    rfl

theorem cell21_1900401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 4, 2, 4].length) (baseStart_1900401 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1900401 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1900401 prefixEnd_1900401 := by exact prefixLift 1900401
  have htrace : WordTrace (prefixWord ++ tailWord_1900401) baseStart_1900401 baseEnd_1900401 := by
    simpa [prefixWord, tailWord_1900401, baseEnd_1900401] using wordTrace_append hprefix tailTrace_1900401
  have hstable : (prefixWord ++ tailWord_1900401).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1900401).length < 2 ^ (prefixWord ++ tailWord_1900401).sum := by decide
  have hdescent : baseEnd_1900401 < baseStart_1900401 := by decide
  rcases family_descends (prefixWord ++ tailWord_1900401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1900514 : List Nat := [3, 3, 3, 1, 2, 1, 3, 2, 3]
def baseStart_1900514 : Nat := 118140960795 + 1900514 * 2 ^ 59
def prefixEnd_1900514 : Nat := 4983230072969 + 3 ^ 40 * 1900514 * 2
def baseEnd_1900514 : Nat := 433723187821814428415423

theorem tailTrace_1900514 : CollatzResearch.WordTrace tailWord_1900514 prefixEnd_1900514 433723187821814428415423 := by
  unfold tailWord_1900514
  simp only [CollatzResearch.WordTrace]
  refine ⟨17329360059192458698755149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46211626824513223196680397 17329360059192458698755149)
  ·
    refine ⟨6498510022197172012033181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17329360059192458698755149 6498510022197172012033181)
    ·
      refine ⟨2436941258323939504512443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6498510022197172012033181 2436941258323939504512443)
      ·
        refine ⟨3655411887485909256768665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2436941258323939504512443 3655411887485909256768665)
        ·
          refine ⟨2741558915614431942576499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3655411887485909256768665 2741558915614431942576499)
          ·
            refine ⟨4112338373421647913864749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2741558915614431942576499 4112338373421647913864749)
            ·
              refine ⟨1542126890033117967699281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4112338373421647913864749 1542126890033117967699281)
              ·
                refine ⟨1156595167524838475774461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1542126890033117967699281 1156595167524838475774461)
                ·
                  refine ⟨433723187821814428415423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1156595167524838475774461 433723187821814428415423)
                  ·
                    rfl

theorem cell21_1900514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 3, 2, 3].length) (baseStart_1900514 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1900514 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1900514 prefixEnd_1900514 := by exact prefixLift 1900514
  have htrace : WordTrace (prefixWord ++ tailWord_1900514) baseStart_1900514 baseEnd_1900514 := by
    simpa [prefixWord, tailWord_1900514, baseEnd_1900514] using wordTrace_append hprefix tailTrace_1900514
  have hstable : (prefixWord ++ tailWord_1900514).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1900514).length < 2 ^ (prefixWord ++ tailWord_1900514).sum := by decide
  have hdescent : baseEnd_1900514 < baseStart_1900514 := by decide
  rcases family_descends (prefixWord ++ tailWord_1900514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1900525 : List Nat := [1, 5, 1, 4, 1, 1, 2, 6]
def baseStart_1900525 : Nat := 118140960795 + 1900525 * 2 ^ 59
def prefixEnd_1900525 : Nat := 4983230072969 + 3 ^ 40 * 1900525 * 2
def baseEnd_1900525 : Nat := 144575232723893617910689

theorem tailTrace_1900525 : CollatzResearch.WordTrace tailWord_1900525 prefixEnd_1900525 144575232723893617910689 := by
  unfold tailWord_1900525
  simp only [CollatzResearch.WordTrace]
  refine ⟨69317841439729983673671029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46211894293153322449114019 69317841439729983673671029)
  ·
    refine ⟨6498547634974685969406659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 69317841439729983673671029 6498547634974685969406659)
    ·
      refine ⟨9747821452462028954109989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6498547634974685969406659 9747821452462028954109989)
      ·
        refine ⟨1827716522336630428895623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9747821452462028954109989 1827716522336630428895623)
        ·
          refine ⟨2741574783504945643343435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1827716522336630428895623 2741574783504945643343435)
          ·
            refine ⟨4112362175257418465015153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2741574783504945643343435 4112362175257418465015153)
            ·
              refine ⟨3084271631443063848761365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4112362175257418465015153 3084271631443063848761365)
              ·
                refine ⟨144575232723893617910689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3084271631443063848761365 144575232723893617910689)
                ·
                  rfl

theorem cell21_1900525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 2, 6].length) (baseStart_1900525 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1900525 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1900525 prefixEnd_1900525 := by exact prefixLift 1900525
  have htrace : WordTrace (prefixWord ++ tailWord_1900525) baseStart_1900525 baseEnd_1900525 := by
    simpa [prefixWord, tailWord_1900525, baseEnd_1900525] using wordTrace_append hprefix tailTrace_1900525
  have hstable : (prefixWord ++ tailWord_1900525).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1900525).length < 2 ^ (prefixWord ++ tailWord_1900525).sum := by decide
  have hdescent : baseEnd_1900525 < baseStart_1900525 := by decide
  rcases family_descends (prefixWord ++ tailWord_1900525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1900567 : List Nat := [1, 1, 3, 5, 2, 9]
def baseStart_1900567 : Nat := 118140960795 + 1900567 * 2 ^ 59
def prefixEnd_1900567 : Nat := 4983230072969 + 3 ^ 40 * 1900567 * 2
def baseEnd_1900567 : Nat := 16064269746070300519703

theorem tailTrace_1900567 : CollatzResearch.WordTrace tailWord_1900567 prefixEnd_1900567 16064269746070300519703 := by
  unfold tailWord_1900567
  simp only [CollatzResearch.WordTrace]
  refine ⟨69319373305577824846699955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46212915537051883231133303 69319373305577824846699955)
  ·
    refine ⟨103979059958366737270049933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69319373305577824846699955 103979059958366737270049933)
    ·
      refine ⟨38992147484387526476268725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103979059958366737270049933 38992147484387526476268725)
      ·
        refine ⟨3655513826661330607150193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 38992147484387526476268725 3655513826661330607150193)
        ·
          refine ⟨2741635369995997955362645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3655513826661330607150193 2741635369995997955362645)
          ·
            refine ⟨16064269746070300519703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2741635369995997955362645 16064269746070300519703)
            ·
              rfl

theorem cell21_1900567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 9].length) (baseStart_1900567 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1900567 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1900567 prefixEnd_1900567 := by exact prefixLift 1900567
  have htrace : WordTrace (prefixWord ++ tailWord_1900567) baseStart_1900567 baseEnd_1900567 := by
    simpa [prefixWord, tailWord_1900567, baseEnd_1900567] using wordTrace_append hprefix tailTrace_1900567
  have hstable : (prefixWord ++ tailWord_1900567).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1900567).length < 2 ^ (prefixWord ++ tailWord_1900567).sum := by decide
  have hdescent : baseEnd_1900567 < baseStart_1900567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1900567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1900573 : List Nat := [1, 4, 2, 2, 2, 3, 2, 2, 3]
def baseStart_1900573 : Nat := 118140960795 + 1900573 * 2 ^ 59
def prefixEnd_1900573 : Nat := 4983230072969 + 3 ^ 40 * 1900573 * 2
def baseEnd_1900573 : Nat := 433736652425643436931969

theorem tailTrace_1900573 : CollatzResearch.WordTrace tailWord_1900573 prefixEnd_1900573 433736652425643436931969 := by
  unfold tailWord_1900573
  simp only [CollatzResearch.WordTrace]
  refine ⟨69319592143556087871418373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46213061429037391914278915 69319592143556087871418373)
  ·
    refine ⟨12997423526916766475890945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69319592143556087871418373 12997423526916766475890945)
    ·
      refine ⟨9748067645187574856918209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12997423526916766475890945 9748067645187574856918209)
      ·
        refine ⟨7311050733890681142688657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9748067645187574856918209 7311050733890681142688657)
        ·
          refine ⟨5483288050418010857016493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7311050733890681142688657 5483288050418010857016493)
          ·
            refine ⟨2056233018906754071381185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5483288050418010857016493 2056233018906754071381185)
            ·
              refine ⟨1542174764180065553535889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2056233018906754071381185 1542174764180065553535889)
              ·
                refine ⟨1156631073135049165151917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1542174764180065553535889 1156631073135049165151917)
                ·
                  refine ⟨433736652425643436931969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1156631073135049165151917 433736652425643436931969)
                  ·
                    rfl

theorem cell21_1900573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 2, 2, 3].length) (baseStart_1900573 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1900573 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1900573 prefixEnd_1900573 := by exact prefixLift 1900573
  have htrace : WordTrace (prefixWord ++ tailWord_1900573) baseStart_1900573 baseEnd_1900573 := by
    simpa [prefixWord, tailWord_1900573, baseEnd_1900573] using wordTrace_append hprefix tailTrace_1900573
  have hstable : (prefixWord ++ tailWord_1900573).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1900573).length < 2 ^ (prefixWord ++ tailWord_1900573).sum := by decide
  have hdescent : baseEnd_1900573 < baseStart_1900573 := by decide
  rcases family_descends (prefixWord ++ tailWord_1900573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1900615 : List Nat := [1, 1, 4, 1, 3, 1, 4, 3, 3]
def baseStart_1900615 : Nat := 118140960795 + 1900615 * 2 ^ 59
def prefixEnd_1900615 : Nat := 4983230072969 + 3 ^ 40 * 1900615 * 2
def baseEnd_1900615 : Nat := 433746237397860697231883

theorem tailTrace_1900615 : CollatzResearch.WordTrace tailWord_1900615 prefixEnd_1900615 433746237397860697231883 := by
  unfold tailWord_1900615
  simp only [CollatzResearch.WordTrace]
  refine ⟨69321124009403929044447299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46214082672935952696298199 69321124009403929044447299)
  ·
    refine ⟨103981686014105893566670949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69321124009403929044447299 103981686014105893566670949)
    ·
      refine ⟨19496566127644855043750803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103981686014105893566670949 19496566127644855043750803)
      ·
        refine ⟨29244849191467282565626205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19496566127644855043750803 29244849191467282565626205)
        ·
          refine ⟨10966818446800230962109827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29244849191467282565626205 10966818446800230962109827)
          ·
            refine ⟨16450227670200346443164741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10966818446800230962109827 16450227670200346443164741)
            ·
              refine ⟨3084417688162564958093389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16450227670200346443164741 3084417688162564958093389)
              ·
                refine ⟨1156656633060961859285021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3084417688162564958093389 1156656633060961859285021)
                ·
                  refine ⟨433746237397860697231883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1156656633060961859285021 433746237397860697231883)
                  ·
                    rfl

theorem cell21_1900615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 4, 3, 3].length) (baseStart_1900615 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1900615 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1900615 prefixEnd_1900615 := by exact prefixLift 1900615
  have htrace : WordTrace (prefixWord ++ tailWord_1900615) baseStart_1900615 baseEnd_1900615 := by
    simpa [prefixWord, tailWord_1900615, baseEnd_1900615] using wordTrace_append hprefix tailTrace_1900615
  have hstable : (prefixWord ++ tailWord_1900615).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1900615).length < 2 ^ (prefixWord ++ tailWord_1900615).sum := by decide
  have hdescent : baseEnd_1900615 < baseStart_1900615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1900615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1900629 : List Nat := [1, 3, 2, 2, 1, 3, 3, 2, 4]
def baseStart_1900629 : Nat := 118140960795 + 1900629 * 2 ^ 59
def prefixEnd_1900629 : Nat := 4983230072969 + 3 ^ 40 * 1900629 * 2
def baseEnd_1900629 : Nat := 433749432388599783998521

theorem tailTrace_1900629 : CollatzResearch.WordTrace tailWord_1900629 prefixEnd_1900629 433749432388599783998521 := by
  unfold tailWord_1900629
  simp only [CollatzResearch.WordTrace]
  refine ⟨69321634631353209435456941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46214423087568806290304627 69321634631353209435456941)
  ·
    refine ⟨25995612986757453538296353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69321634631353209435456941 25995612986757453538296353)
    ·
      refine ⟨19496709740068090153722265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25995612986757453538296353 19496709740068090153722265)
      ·
        refine ⟨14622532305051067615291699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19496709740068090153722265 14622532305051067615291699)
        ·
          refine ⟨21933798457576601422937549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14622532305051067615291699 21933798457576601422937549)
          ·
            refine ⟨8225174421591225533601581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21933798457576601422937549 8225174421591225533601581)
            ·
              refine ⟨3084440408096709575100593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8225174421591225533601581 3084440408096709575100593)
              ·
                refine ⟨2313330306072532181325445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3084440408096709575100593 2313330306072532181325445)
                ·
                  refine ⟨433749432388599783998521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2313330306072532181325445 433749432388599783998521)
                  ·
                    rfl

theorem cell21_1900629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 3, 2, 4].length) (baseStart_1900629 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1900629 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1900629 prefixEnd_1900629 := by exact prefixLift 1900629
  have htrace : WordTrace (prefixWord ++ tailWord_1900629) baseStart_1900629 baseEnd_1900629 := by
    simpa [prefixWord, tailWord_1900629, baseEnd_1900629] using wordTrace_append hprefix tailTrace_1900629
  have hstable : (prefixWord ++ tailWord_1900629).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1900629).length < 2 ^ (prefixWord ++ tailWord_1900629).sum := by decide
  have hdescent : baseEnd_1900629 < baseStart_1900629 := by decide
  rcases family_descends (prefixWord ++ tailWord_1900629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1900657 : List Nat := [1, 2, 2, 2, 1, 1, 3, 4, 5]
def baseStart_1900657 : Nat := 118140960795 + 1900657 * 2 ^ 59
def prefixEnd_1900657 : Nat := 4983230072969 + 3 ^ 40 * 1900657 * 2
def baseEnd_1900657 : Nat := 433755822370077957531797

theorem tailTrace_1900657 : CollatzResearch.WordTrace tailWord_1900657 prefixEnd_1900657 433755822370077957531797 := by
  unfold tailWord_1900657
  simp only [CollatzResearch.WordTrace]
  refine ⟨69322655875251770217476225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46215103916834513478317483 69322655875251770217476225)
  ·
    refine ⟨51991991906438827663107169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69322655875251770217476225 51991991906438827663107169)
    ·
      refine ⟨38993993929829120747330377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51991991906438827663107169 38993993929829120747330377)
      ·
        refine ⟨29245495447371840560497783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38993993929829120747330377 29245495447371840560497783)
        ·
          refine ⟨43868243171057760840746675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29245495447371840560497783 43868243171057760840746675)
          ·
            refine ⟨65802364756586641261120013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43868243171057760840746675 65802364756586641261120013)
            ·
              refine ⟨24675886783719990472920005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65802364756586641261120013 24675886783719990472920005)
              ·
                refine ⟨4626728771947498213672501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24675886783719990472920005 4626728771947498213672501)
                ·
                  refine ⟨433755822370077957531797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4626728771947498213672501 433755822370077957531797)
                  ·
                    rfl

theorem cell21_1900657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 4, 5].length) (baseStart_1900657 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1900657 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1900657 prefixEnd_1900657 := by exact prefixLift 1900657
  have htrace : WordTrace (prefixWord ++ tailWord_1900657) baseStart_1900657 baseEnd_1900657 := by
    simpa [prefixWord, tailWord_1900657, baseEnd_1900657] using wordTrace_append hprefix tailTrace_1900657
  have hstable : (prefixWord ++ tailWord_1900657).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1900657).length < 2 ^ (prefixWord ++ tailWord_1900657).sum := by decide
  have hdescent : baseEnd_1900657 < baseStart_1900657 := by decide
  rcases family_descends (prefixWord ++ tailWord_1900657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1900688 : List Nat := [2, 1, 1, 1, 1, 1, 6, 4, 4]
def baseStart_1900688 : Nat := 118140960795 + 1900688 * 2 ^ 59
def prefixEnd_1900688 : Nat := 4983230072969 + 3 ^ 40 * 1900688 * 2
def baseEnd_1900688 : Nat := 433762896992428792515067

theorem tailTrace_1900688 : CollatzResearch.WordTrace tailWord_1900688 prefixEnd_1900688 433762896992428792515067 := by
  unfold tailWord_1900688
  simp only [CollatzResearch.WordTrace]
  refine ⟨34661893269069731255927359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46215857692092975007903145 34661893269069731255927359)
  ·
    refine ⟨51992839903604596883891039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34661893269069731255927359 51992839903604596883891039)
    ·
      refine ⟨77989259855406895325836559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51992839903604596883891039 77989259855406895325836559)
      ·
        refine ⟨116983889783110342988754839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77989259855406895325836559 116983889783110342988754839)
        ·
          refine ⟨175475834674665514483132259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116983889783110342988754839 175475834674665514483132259)
          ·
            refine ⟨263213752011998271724698389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175475834674665514483132259 263213752011998271724698389)
            ·
              refine ⟨12338144625562418987095237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 263213752011998271724698389 12338144625562418987095237)
              ·
                refine ⟨2313402117292953560080357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12338144625562418987095237 2313402117292953560080357)
                ·
                  refine ⟨433762896992428792515067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2313402117292953560080357 433762896992428792515067)
                  ·
                    rfl

theorem cell21_1900688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 4, 4].length) (baseStart_1900688 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1900688 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1900688 prefixEnd_1900688 := by exact prefixLift 1900688
  have htrace : WordTrace (prefixWord ++ tailWord_1900688) baseStart_1900688 baseEnd_1900688 := by
    simpa [prefixWord, tailWord_1900688, baseEnd_1900688] using wordTrace_append hprefix tailTrace_1900688
  have hstable : (prefixWord ++ tailWord_1900688).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1900688).length < 2 ^ (prefixWord ++ tailWord_1900688).sum := by decide
  have hdescent : baseEnd_1900688 < baseStart_1900688 := by decide
  rcases family_descends (prefixWord ++ tailWord_1900688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1900705 : List Nat := [1, 2, 3, 3, 1, 3, 1, 3, 4]
def baseStart_1900705 : Nat := 118140960795 + 1900705 * 2 ^ 59
def prefixEnd_1900705 : Nat := 4983230072969 + 3 ^ 40 * 1900705 * 2
def baseEnd_1900705 : Nat := 433766776624040540731699

theorem tailTrace_1900705 : CollatzResearch.WordTrace tailWord_1900705 prefixEnd_1900705 433766776624040540731699 := by
  unfold tailWord_1900705
  simp only [CollatzResearch.WordTrace]
  refine ⟨69324406579077874415223569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46216271052718582943482379 69324406579077874415223569)
  ·
    refine ⟨51993304934308405811417677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69324406579077874415223569 51993304934308405811417677)
    ·
      refine ⟨19497489350365652179281629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51993304934308405811417677 19497489350365652179281629)
      ·
        refine ⟨7311558506387119567230611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19497489350365652179281629 7311558506387119567230611)
        ·
          refine ⟨10967337759580679350845917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7311558506387119567230611 10967337759580679350845917)
          ·
            refine ⟨4112751659842754756567219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10967337759580679350845917 4112751659842754756567219)
            ·
              refine ⟨6169127489764132134850829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4112751659842754756567219 6169127489764132134850829)
              ·
                refine ⟨2313422808661549550569061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6169127489764132134850829 2313422808661549550569061)
                ·
                  refine ⟨433766776624040540731699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2313422808661549550569061 433766776624040540731699)
                  ·
                    rfl

theorem cell21_1900705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 3, 4].length) (baseStart_1900705 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1900705 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1900705 prefixEnd_1900705 := by exact prefixLift 1900705
  have htrace : WordTrace (prefixWord ++ tailWord_1900705) baseStart_1900705 baseEnd_1900705 := by
    simpa [prefixWord, tailWord_1900705, baseEnd_1900705] using wordTrace_append hprefix tailTrace_1900705
  have hstable : (prefixWord ++ tailWord_1900705).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1900705).length < 2 ^ (prefixWord ++ tailWord_1900705).sum := by decide
  have hdescent : baseEnd_1900705 < baseStart_1900705 := by decide
  rcases family_descends (prefixWord ++ tailWord_1900705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1900809 : List Nat := [1, 2, 1, 1, 3, 4, 1, 3, 5]
def baseStart_1900809 : Nat := 118140960795 + 1900809 * 2 ^ 59
def prefixEnd_1900809 : Nat := 4983230072969 + 3 ^ 40 * 1900809 * 2
def baseEnd_1900809 : Nat := 433790510840959470998153

theorem tailTrace_1900809 : CollatzResearch.WordTrace tailWord_1900809 prefixEnd_1900809 433790510840959470998153 := by
  unfold tailWord_1900809
  simp only [CollatzResearch.WordTrace]
  refine ⟨69328199770701100177009481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46218799847134066784672987 69328199770701100177009481)
  ·
    refine ⟨51996149828025825132757111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69328199770701100177009481 51996149828025825132757111)
    ·
      refine ⟨77994224742038737699135667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51996149828025825132757111 77994224742038737699135667)
      ·
        refine ⟨116991337113058106548703501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77994224742038737699135667 116991337113058106548703501)
        ·
          refine ⟨43871751417396789955763813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116991337113058106548703501 43871751417396789955763813)
          ·
            refine ⟨8225953390761898116705715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43871751417396789955763813 8225953390761898116705715)
            ·
              refine ⟨12338930086142847175058573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8225953390761898116705715 12338930086142847175058573)
              ·
                refine ⟨4627098782303567690646965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12338930086142847175058573 4627098782303567690646965)
                ·
                  refine ⟨433790510840959470998153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4627098782303567690646965 433790510840959470998153)
                  ·
                    rfl

theorem cell21_1900809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 3, 5].length) (baseStart_1900809 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1900809 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1900809 prefixEnd_1900809 := by exact prefixLift 1900809
  have htrace : WordTrace (prefixWord ++ tailWord_1900809) baseStart_1900809 baseEnd_1900809 := by
    simpa [prefixWord, tailWord_1900809, baseEnd_1900809] using wordTrace_append hprefix tailTrace_1900809
  have hstable : (prefixWord ++ tailWord_1900809).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1900809).length < 2 ^ (prefixWord ++ tailWord_1900809).sum := by decide
  have hdescent : baseEnd_1900809 < baseStart_1900809 := by decide
  rcases family_descends (prefixWord ++ tailWord_1900809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1900829 : List Nat := [1, 4, 2, 3, 2, 2, 2, 5]
def baseStart_1900829 : Nat := 118140960795 + 1900829 * 2 ^ 59
def prefixEnd_1900829 : Nat := 4983230072969 + 3 ^ 40 * 1900829 * 2
def baseEnd_1900829 : Nat := 144598358371147960221593

theorem tailTrace_1900829 : CollatzResearch.WordTrace tailWord_1900829 prefixEnd_1900829 144598358371147960221593 := by
  unfold tailWord_1900829
  simp only [CollatzResearch.WordTrace]
  refine ⟨69328929230628643592737541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46219286153752429061825027 69328929230628643592737541)
  ·
    refine ⟨12999174230742870673638289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69328929230628643592737541 12999174230742870673638289)
    ·
      refine ⟨9749380673057153005228717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12999174230742870673638289 9749380673057153005228717)
      ·
        refine ⟨3656017752396432376960769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9749380673057153005228717 3656017752396432376960769)
        ·
          refine ⟨2742013314297324282720577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3656017752396432376960769 2742013314297324282720577)
          ·
            refine ⟨2056509985722993212040433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2742013314297324282720577 2056509985722993212040433)
            ·
              refine ⟨1542382489292244909030325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2056509985722993212040433 1542382489292244909030325)
              ·
                refine ⟨144598358371147960221593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1542382489292244909030325 144598358371147960221593)
                ·
                  rfl

theorem cell21_1900829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 2, 5].length) (baseStart_1900829 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1900829 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1900829 prefixEnd_1900829 := by exact prefixLift 1900829
  have htrace : WordTrace (prefixWord ++ tailWord_1900829) baseStart_1900829 baseEnd_1900829 := by
    simpa [prefixWord, tailWord_1900829, baseEnd_1900829] using wordTrace_append hprefix tailTrace_1900829
  have hstable : (prefixWord ++ tailWord_1900829).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1900829).length < 2 ^ (prefixWord ++ tailWord_1900829).sum := by decide
  have hdescent : baseEnd_1900829 < baseStart_1900829 := by decide
  rcases family_descends (prefixWord ++ tailWord_1900829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1900978 : List Nat := [3, 2, 1, 1, 1, 1, 3, 6, 3]
def baseStart_1900978 : Nat := 118140960795 + 1900978 * 2 ^ 59
def prefixEnd_1900978 : Nat := 4983230072969 + 3 ^ 40 * 1900978 * 2
def baseEnd_1900978 : Nat := 433829078943452732681141

theorem tailTrace_1900978 : CollatzResearch.WordTrace tailWord_1900978 prefixEnd_1900978 433829078943452732681141 := by
  unfold tailWord_1900978
  simp only [CollatzResearch.WordTrace]
  refine ⟨17333590926772210509977897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46222909138059228026607725 17333590926772210509977897)
  ·
    refine ⟨13000193195079157882483423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17333590926772210509977897 13000193195079157882483423)
    ·
      refine ⟨19500289792618736823725135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13000193195079157882483423 19500289792618736823725135)
      ·
        refine ⟨29250434688928105235587703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19500289792618736823725135 29250434688928105235587703)
        ·
          refine ⟨43875652033392157853381555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29250434688928105235587703 43875652033392157853381555)
          ·
            refine ⟨65813478050088236780072333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43875652033392157853381555 65813478050088236780072333)
            ·
              refine ⟨24680054268783088792527125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65813478050088236780072333 24680054268783088792527125)
              ·
                refine ⟨1156877543849207287149709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 24680054268783088792527125 1156877543849207287149709)
                ·
                  refine ⟨433829078943452732681141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1156877543849207287149709 433829078943452732681141)
                  ·
                    rfl

theorem cell21_1900978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 6, 3].length) (baseStart_1900978 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1900978 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1900978 prefixEnd_1900978 := by exact prefixLift 1900978
  have htrace : WordTrace (prefixWord ++ tailWord_1900978) baseStart_1900978 baseEnd_1900978 := by
    simpa [prefixWord, tailWord_1900978, baseEnd_1900978] using wordTrace_append hprefix tailTrace_1900978
  have hstable : (prefixWord ++ tailWord_1900978).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1900978).length < 2 ^ (prefixWord ++ tailWord_1900978).sum := by decide
  have hdescent : baseEnd_1900978 < baseStart_1900978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1900978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1901012 : List Nat := [2, 4, 1, 2, 2, 3, 1, 3, 3]
def baseStart_1901012 : Nat := 118140960795 + 1901012 * 2 ^ 59
def prefixEnd_1901012 : Nat := 4983230072969 + 3 ^ 40 * 1901012 * 2
def baseEnd_1901012 : Nat := 433836838206676229114405

theorem tailTrace_1901012 : CollatzResearch.WordTrace tailWord_1901012 prefixEnd_1901012 433836838206676229114405 := by
  unfold tailWord_1901012
  simp only [CollatzResearch.WordTrace]
  refine ⟨34667801894482832923324645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46223735859310443897766193 34667801894482832923324645)
  ·
    refine ⟨6500212855215531173123371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34667801894482832923324645 6500212855215531173123371)
    ·
      refine ⟨9750319282823296759685057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6500212855215531173123371 9750319282823296759685057)
      ·
        refine ⟨7312739462117472569763793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9750319282823296759685057 7312739462117472569763793)
        ·
          refine ⟨5484554596588104427322845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7312739462117472569763793 5484554596588104427322845)
          ·
            refine ⟨2056707973720539160246067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5484554596588104427322845 2056707973720539160246067)
            ·
              refine ⟨3085061960580808740369101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2056707973720539160246067 3085061960580808740369101)
              ·
                refine ⟨1156898235217803277638413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3085061960580808740369101 1156898235217803277638413)
                ·
                  refine ⟨433836838206676229114405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1156898235217803277638413 433836838206676229114405)
                  ·
                    rfl

theorem cell21_1901012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 1, 3, 3].length) (baseStart_1901012 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1901012 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1901012 prefixEnd_1901012 := by exact prefixLift 1901012
  have htrace : WordTrace (prefixWord ++ tailWord_1901012) baseStart_1901012 baseEnd_1901012 := by
    simpa [prefixWord, tailWord_1901012, baseEnd_1901012] using wordTrace_append hprefix tailTrace_1901012
  have hstable : (prefixWord ++ tailWord_1901012).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1901012).length < 2 ^ (prefixWord ++ tailWord_1901012).sum := by decide
  have hdescent : baseEnd_1901012 < baseStart_1901012 := by decide
  rcases family_descends (prefixWord ++ tailWord_1901012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1901085 : List Nat := [1, 4, 2, 2, 1, 3, 2, 2, 4]
def baseStart_1901085 : Nat := 118140960795 + 1901085 * 2 ^ 59
def prefixEnd_1901085 : Nat := 4983230072969 + 3 ^ 40 * 1901085 * 2
def baseEnd_1901085 : Nat := 433853497801244324397589

theorem tailTrace_1901085 : CollatzResearch.WordTrace tailWord_1901085 prefixEnd_1901085 433853497801244324397589 := by
  unfold tailWord_1901085
  simp only [CollatzResearch.WordTrace]
  refine ⟨69338266317701199314056709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46225510878467466209371139 69338266317701199314056709)
  ·
    refine ⟨13000924934568974871385633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69338266317701199314056709 13000924934568974871385633)
    ·
      refine ⟨9750693700926731153539225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13000924934568974871385633 9750693700926731153539225)
      ·
        refine ⟨7313020275695048365154419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9750693700926731153539225 7313020275695048365154419)
        ·
          refine ⟨10969530413542572547731629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7313020275695048365154419 10969530413542572547731629)
          ·
            refine ⟨4113573905078464705399361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10969530413542572547731629 4113573905078464705399361)
            ·
              refine ⟨3085180428808848529049521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4113573905078464705399361 3085180428808848529049521)
              ·
                refine ⟨2313885321606636396787141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3085180428808848529049521 2313885321606636396787141)
                ·
                  refine ⟨433853497801244324397589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2313885321606636396787141 433853497801244324397589)
                  ·
                    rfl

theorem cell21_1901085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 2, 2, 4].length) (baseStart_1901085 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1901085 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1901085 prefixEnd_1901085 := by exact prefixLift 1901085
  have htrace : WordTrace (prefixWord ++ tailWord_1901085) baseStart_1901085 baseEnd_1901085 := by
    simpa [prefixWord, tailWord_1901085, baseEnd_1901085] using wordTrace_append hprefix tailTrace_1901085
  have hstable : (prefixWord ++ tailWord_1901085).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1901085).length < 2 ^ (prefixWord ++ tailWord_1901085).sum := by decide
  have hdescent : baseEnd_1901085 < baseStart_1901085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1901085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1901113 : List Nat := [1, 2, 1, 5, 1, 1, 3, 2, 5]
def baseStart_1901113 : Nat := 118140960795 + 1901113 * 2 ^ 59
def prefixEnd_1901113 : Nat := 4983230072969 + 3 ^ 40 * 1901113 * 2
def baseEnd_1901113 : Nat := 433859887782722497930865

theorem tailTrace_1901113 : CollatzResearch.WordTrace tailWord_1901113 prefixEnd_1901113 433859887782722497930865 := by
  unfold tailWord_1901113
  simp only [CollatzResearch.WordTrace]
  refine ⟨69339287561599760096075993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46226191707733173397383995 69339287561599760096075993)
  ·
    refine ⟨52004465671199820072056995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69339287561599760096075993 52004465671199820072056995)
    ·
      refine ⟨78006698506799730108085493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52004465671199820072056995 78006698506799730108085493)
      ·
        refine ⟨7313127985012474697633015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 78006698506799730108085493 7313127985012474697633015)
        ·
          refine ⟨10969691977518712046449523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7313127985012474697633015 10969691977518712046449523)
          ·
            refine ⟨16454537966278068069674285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10969691977518712046449523 16454537966278068069674285)
            ·
              refine ⟨6170451737354275526127857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16454537966278068069674285 6170451737354275526127857)
              ·
                refine ⟨4627838803015706644595893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6170451737354275526127857 4627838803015706644595893)
                ·
                  refine ⟨433859887782722497930865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4627838803015706644595893 433859887782722497930865)
                  ·
                    rfl

theorem cell21_1901113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 2, 5].length) (baseStart_1901113 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1901113 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1901113 prefixEnd_1901113 := by exact prefixLift 1901113
  have htrace : WordTrace (prefixWord ++ tailWord_1901113) baseStart_1901113 baseEnd_1901113 := by
    simpa [prefixWord, tailWord_1901113, baseEnd_1901113] using wordTrace_append hprefix tailTrace_1901113
  have hstable : (prefixWord ++ tailWord_1901113).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1901113).length < 2 ^ (prefixWord ++ tailWord_1901113).sum := by decide
  have hdescent : baseEnd_1901113 < baseStart_1901113 := by decide
  rcases family_descends (prefixWord ++ tailWord_1901113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1901130 : List Nat := [3, 1, 2, 1, 1, 4, 1, 5, 3]
def baseStart_1901130 : Nat := 118140960795 + 1901130 * 2 ^ 59
def prefixEnd_1901130 : Nat := 4983230072969 + 3 ^ 40 * 1901130 * 2
def baseEnd_1901130 : Nat := 433863767414334246147497

theorem tailTrace_1901130 : CollatzResearch.WordTrace tailWord_1901130 prefixEnd_1901130 433863767414334246147497 := by
  unfold tailWord_1901130
  simp only [CollatzResearch.WordTrace]
  refine ⟨17334976900634542999861211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46226605068358781332963229 17334976900634542999861211)
  ·
    refine ⟨26002465350951814499791817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17334976900634542999861211 26002465350951814499791817)
    ·
      refine ⟨19501849013213860874843863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26002465350951814499791817 19501849013213860874843863)
      ·
        refine ⟨29252773519820791312265795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19501849013213860874843863 29252773519820791312265795)
        ·
          refine ⟨43879160279731186968398693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29252773519820791312265795 43879160279731186968398693)
          ·
            refine ⟨8227342552449597556574755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43879160279731186968398693 8227342552449597556574755)
            ·
              refine ⟨12341013828674396334862133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8227342552449597556574755 12341013828674396334862133)
              ·
                refine ⟨1156970046438224656393325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12341013828674396334862133 1156970046438224656393325)
                ·
                  refine ⟨433863767414334246147497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1156970046438224656393325 433863767414334246147497)
                  ·
                    rfl

theorem cell21_1901130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 5, 3].length) (baseStart_1901130 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1901130 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1901130 prefixEnd_1901130 := by exact prefixLift 1901130
  have htrace : WordTrace (prefixWord ++ tailWord_1901130) baseStart_1901130 baseEnd_1901130 := by
    simpa [prefixWord, tailWord_1901130, baseEnd_1901130] using wordTrace_append hprefix tailTrace_1901130
  have hstable : (prefixWord ++ tailWord_1901130).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1901130).length < 2 ^ (prefixWord ++ tailWord_1901130).sum := by decide
  have hdescent : baseEnd_1901130 < baseStart_1901130 := by decide
  rcases family_descends (prefixWord ++ tailWord_1901130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1901144 : List Nat := [2, 1, 2, 2, 1, 2, 5, 2, 4]
def baseStart_1901144 : Nat := 118140960795 + 1901144 * 2 ^ 59
def prefixEnd_1901144 : Nat := 4983230072969 + 3 ^ 40 * 1901144 * 2
def baseEnd_1901144 : Nat := 433866962405073332914135

theorem tailTrace_1901144 : CollatzResearch.WordTrace tailWord_1901144 prefixEnd_1901144 433866962405073332914135 := by
  unfold tailWord_1901144
  simp only [CollatzResearch.WordTrace]
  refine ⟨34670209112243726195227243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46226945482991634926969657 34670209112243726195227243)
  ·
    refine ⟨52005313668365589292840865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34670209112243726195227243 52005313668365589292840865)
    ·
      refine ⟨39003985251274191969630649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52005313668365589292840865 39003985251274191969630649)
      ·
        refine ⟨29252988938455643977222987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39003985251274191969630649 29252988938455643977222987)
        ·
          refine ⟨43879483407683465965834481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29252988938455643977222987 43879483407683465965834481)
          ·
            refine ⟨32909612555762599474375861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43879483407683465965834481 32909612555762599474375861)
            ·
              refine ⟨3085276177102743700722737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32909612555762599474375861 3085276177102743700722737)
              ·
                refine ⟨2313957132827057775542053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3085276177102743700722737 2313957132827057775542053)
                ·
                  refine ⟨433866962405073332914135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2313957132827057775542053 433866962405073332914135)
                  ·
                    rfl

theorem cell21_1901144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 5, 2, 4].length) (baseStart_1901144 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1901144 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1901144 prefixEnd_1901144 := by exact prefixLift 1901144
  have htrace : WordTrace (prefixWord ++ tailWord_1901144) baseStart_1901144 baseEnd_1901144 := by
    simpa [prefixWord, tailWord_1901144, baseEnd_1901144] using wordTrace_append hprefix tailTrace_1901144
  have hstable : (prefixWord ++ tailWord_1901144).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1901144).length < 2 ^ (prefixWord ++ tailWord_1901144).sum := by decide
  have hdescent : baseEnd_1901144 < baseStart_1901144 := by decide
  rcases family_descends (prefixWord ++ tailWord_1901144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1901220 : List Nat := [2, 3, 1, 2, 2, 1, 3, 3, 4]
def baseStart_1901220 : Nat := 118140960795 + 1901220 * 2 ^ 59
def prefixEnd_1901220 : Nat := 4983230072969 + 3 ^ 40 * 1901220 * 2
def baseEnd_1901220 : Nat := 433884306640514089647313

theorem tailTrace_1901220 : CollatzResearch.WordTrace tailWord_1901220 prefixEnd_1901220 433884306640514089647313 := by
  unfold tailWord_1901220
  simp only [CollatzResearch.WordTrace]
  refine ⟨34671595086106058685110557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46228793448141411580147409 34671595086106058685110557)
  ·
    refine ⟨13001848157289772006916459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34671595086106058685110557 13001848157289772006916459)
    ·
      refine ⟨19502772235934658010374689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13001848157289772006916459 19502772235934658010374689)
      ·
        refine ⟨14627079176950993507781017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19502772235934658010374689 14627079176950993507781017)
        ·
          refine ⟨10970309382713245130835763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14627079176950993507781017 10970309382713245130835763)
          ·
            refine ⟨16455464074069867696253645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10970309382713245130835763 16455464074069867696253645)
            ·
              refine ⟨6170799027776200386095117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16455464074069867696253645 6170799027776200386095117)
              ·
                refine ⟨2314049635416075144785669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6170799027776200386095117 2314049635416075144785669)
                ·
                  refine ⟨433884306640514089647313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2314049635416075144785669 433884306640514089647313)
                  ·
                    rfl

theorem cell21_1901220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 3, 4].length) (baseStart_1901220 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1901220 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1901220 prefixEnd_1901220 := by exact prefixLift 1901220
  have htrace : WordTrace (prefixWord ++ tailWord_1901220) baseStart_1901220 baseEnd_1901220 := by
    simpa [prefixWord, tailWord_1901220, baseEnd_1901220] using wordTrace_append hprefix tailTrace_1901220
  have hstable : (prefixWord ++ tailWord_1901220).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1901220).length < 2 ^ (prefixWord ++ tailWord_1901220).sum := by decide
  have hdescent : baseEnd_1901220 < baseStart_1901220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1901220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1901268 : List Nat := [2, 4, 1, 3, 2, 2, 1, 6]
def baseStart_1901268 : Nat := 118140960795 + 1901268 * 2 ^ 59
def prefixEnd_1901268 : Nat := 4983230072969 + 3 ^ 40 * 1901268 * 2
def baseEnd_1901268 : Nat := 144631753631492224282405

theorem tailTrace_1901268 : CollatzResearch.WordTrace tailWord_1901268 prefixEnd_1901268 144631753631492224282405 := by
  unfold tailWord_1901268
  simp only [CollatzResearch.WordTrace]
  refine ⟨34672470438019110783984229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46229960584025481045312305 34672470438019110783984229)
  ·
    refine ⟨6501088207128583271997043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34672470438019110783984229 6501088207128583271997043)
    ·
      refine ⟨9751632310692874907995565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6501088207128583271997043 9751632310692874907995565)
      ·
        refine ⟨3656862116509828090498337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9751632310692874907995565 3656862116509828090498337)
        ·
          refine ⟨2742646587382371067873753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3656862116509828090498337 2742646587382371067873753)
          ·
            refine ⟨2056984940536778300905315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2742646587382371067873753 2056984940536778300905315)
            ·
              refine ⟨3085477410805167451357973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2056984940536778300905315 3085477410805167451357973)
              ·
                refine ⟨144631753631492224282405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3085477410805167451357973 144631753631492224282405)
                ·
                  rfl

theorem cell21_1901268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 1, 6].length) (baseStart_1901268 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1901268 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1901268 prefixEnd_1901268 := by exact prefixLift 1901268
  have htrace : WordTrace (prefixWord ++ tailWord_1901268) baseStart_1901268 baseEnd_1901268 := by
    simpa [prefixWord, tailWord_1901268, baseEnd_1901268] using wordTrace_append hprefix tailTrace_1901268
  have hstable : (prefixWord ++ tailWord_1901268).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1901268).length < 2 ^ (prefixWord ++ tailWord_1901268).sum := by decide
  have hdescent : baseEnd_1901268 < baseStart_1901268 := by decide
  rcases family_descends (prefixWord ++ tailWord_1901268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1901375 : List Nat := [1, 1, 2, 2, 5, 2, 3, 2, 3]
def baseStart_1901375 : Nat := 118140960795 + 1901375 * 2 ^ 59
def prefixEnd_1901375 : Nat := 4983230072969 + 3 ^ 40 * 1901375 * 2
def baseEnd_1901375 : Nat := 433919679752268264563663

theorem tailTrace_1901375 : CollatzResearch.WordTrace tailWord_1901375 prefixEnd_1901375 433919679752268264563663 := by
  unfold tailWord_1901375
  simp only [CollatzResearch.WordTrace]
  refine ⟨69348843486650578842113579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46232562324433719228075719 69348843486650578842113579)
  ·
    refine ⟨104023265229975868263170369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69348843486650578842113579 104023265229975868263170369)
    ·
      refine ⟨78017448922481901197377777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104023265229975868263170369 78017448922481901197377777)
      ·
        refine ⟨58513086691861425898033333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78017448922481901197377777 58513086691861425898033333)
        ·
          refine ⟨5485601877362008677940625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58513086691861425898033333 5485601877362008677940625)
          ·
            refine ⟨4114201408021506508455469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5485601877362008677940625 4114201408021506508455469)
            ·
              refine ⟨1542825528008064940670801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4114201408021506508455469 1542825528008064940670801)
              ·
                refine ⟨1157119146006048705503101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1542825528008064940670801 1157119146006048705503101)
                ·
                  refine ⟨433919679752268264563663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1157119146006048705503101 433919679752268264563663)
                  ·
                    rfl

theorem cell21_1901375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 3, 2, 3].length) (baseStart_1901375 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1901375 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1901375 prefixEnd_1901375 := by exact prefixLift 1901375
  have htrace : WordTrace (prefixWord ++ tailWord_1901375) baseStart_1901375 baseEnd_1901375 := by
    simpa [prefixWord, tailWord_1901375, baseEnd_1901375] using wordTrace_append hprefix tailTrace_1901375
  have hstable : (prefixWord ++ tailWord_1901375).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1901375).length < 2 ^ (prefixWord ++ tailWord_1901375).sum := by decide
  have hdescent : baseEnd_1901375 < baseStart_1901375 := by decide
  rcases family_descends (prefixWord ++ tailWord_1901375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1901400 : List Nat := [2, 1, 2, 2, 1, 1, 1, 6, 5]
def baseStart_1901400 : Nat := 118140960795 + 1901400 * 2 ^ 59
def prefixEnd_1901400 : Nat := 4983230072969 + 3 ^ 40 * 1901400 * 2
def baseEnd_1901400 : Nat := 433925385092873776646945

theorem tailTrace_1901400 : CollatzResearch.WordTrace tailWord_1901400 prefixEnd_1901400 433925385092873776646945 := by
  unfold tailWord_1901400
  simp only [CollatzResearch.WordTrace]
  refine ⟨34674877655780004055886827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46233170207706672074515769 34674877655780004055886827)
  ·
    refine ⟨52012316483670006083830241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34674877655780004055886827 52012316483670006083830241)
    ·
      refine ⟨39009237362752504562872681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52012316483670006083830241 39009237362752504562872681)
      ·
        refine ⟨29256928022064378422154511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39009237362752504562872681 29256928022064378422154511)
        ·
          refine ⟨43885392033096567633231767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29256928022064378422154511 43885392033096567633231767)
          ·
            refine ⟨65828088049644851449847651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43885392033096567633231767 65828088049644851449847651)
            ·
              refine ⟨98742132074467277174771477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65828088049644851449847651 98742132074467277174771477)
              ·
                refine ⟨4628537440990653617567413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 98742132074467277174771477 4628537440990653617567413)
                ·
                  refine ⟨433925385092873776646945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4628537440990653617567413 433925385092873776646945)
                  ·
                    rfl

theorem cell21_1901400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 6, 5].length) (baseStart_1901400 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1901400 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1901400 prefixEnd_1901400 := by exact prefixLift 1901400
  have htrace : WordTrace (prefixWord ++ tailWord_1901400) baseStart_1901400 baseEnd_1901400 := by
    simpa [prefixWord, tailWord_1901400, baseEnd_1901400] using wordTrace_append hprefix tailTrace_1901400
  have hstable : (prefixWord ++ tailWord_1901400).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1901400).length < 2 ^ (prefixWord ++ tailWord_1901400).sum := by decide
  have hdescent : baseEnd_1901400 < baseStart_1901400 := by decide
  rcases family_descends (prefixWord ++ tailWord_1901400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1901448 : List Nat := [2, 1, 3, 3, 2, 1, 2, 3, 4]
def baseStart_1901448 : Nat := 118140960795 + 1901448 * 2 ^ 59
def prefixEnd_1901448 : Nat := 4983230072969 + 3 ^ 40 * 1901448 * 2
def baseEnd_1901448 : Nat := 433936339346836359846847

theorem tailTrace_1901448 : CollatzResearch.WordTrace tailWord_1901448 prefixEnd_1901448 433936339346836359846847 := by
  unfold tailWord_1901448
  simp only [CollatzResearch.WordTrace]
  refine ⟨34675753007693056154760499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46234337343590741539680665 34675753007693056154760499)
  ·
    refine ⟨52013629511539584232140749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34675753007693056154760499 52013629511539584232140749)
    ·
      refine ⟨19505111066827344087052781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52013629511539584232140749 19505111066827344087052781)
      ·
        refine ⟨7314416650060254032644793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19505111066827344087052781 7314416650060254032644793)
        ·
          refine ⟨5485812487545190524483595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7314416650060254032644793 5485812487545190524483595)
          ·
            refine ⟨8228718731317785786725393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5485812487545190524483595 8228718731317785786725393)
            ·
              refine ⟨6171539048488339340044045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8228718731317785786725393 6171539048488339340044045)
              ·
                refine ⟨2314327143183127252516517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6171539048488339340044045 2314327143183127252516517)
                ·
                  refine ⟨433936339346836359846847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2314327143183127252516517 433936339346836359846847)
                  ·
                    rfl

theorem cell21_1901448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 3, 4].length) (baseStart_1901448 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1901448 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1901448 prefixEnd_1901448 := by exact prefixLift 1901448
  have htrace : WordTrace (prefixWord ++ tailWord_1901448) baseStart_1901448 baseEnd_1901448 := by
    simpa [prefixWord, tailWord_1901448, baseEnd_1901448] using wordTrace_append hprefix tailTrace_1901448
  have hstable : (prefixWord ++ tailWord_1901448).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1901448).length < 2 ^ (prefixWord ++ tailWord_1901448).sum := by decide
  have hdescent : baseEnd_1901448 < baseStart_1901448 := by decide
  rcases family_descends (prefixWord ++ tailWord_1901448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1901476 : List Nat := [2, 3, 1, 2, 1, 2, 1, 2, 7]
def baseStart_1901476 : Nat := 118140960795 + 1901476 * 2 ^ 59
def prefixEnd_1901476 : Nat := 4983230072969 + 3 ^ 40 * 1901476 * 2
def baseEnd_1901476 : Nat := 433942729328314533380123

theorem tailTrace_1901476 : CollatzResearch.WordTrace tailWord_1901476 prefixEnd_1901476 433942729328314533380123 := by
  unfold tailWord_1901476
  simp only [CollatzResearch.WordTrace]
  refine ⟨34676263629642336545770141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46235018172856448727693521 34676263629642336545770141)
  ·
    refine ⟨13003598861115876204663803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34676263629642336545770141 13003598861115876204663803)
    ·
      refine ⟨19505398291673814306995705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13003598861115876204663803 19505398291673814306995705)
      ·
        refine ⟨14629048718755360730246779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19505398291673814306995705 14629048718755360730246779)
        ·
          refine ⟨21943573078133041095370169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14629048718755360730246779 21943573078133041095370169)
          ·
            refine ⟨16457679808599780821527627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21943573078133041095370169 16457679808599780821527627)
            ·
              refine ⟨24686519712899671232291441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16457679808599780821527627 24686519712899671232291441)
              ·
                refine ⟨18514889784674753424218581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24686519712899671232291441 18514889784674753424218581)
                ·
                  refine ⟨433942729328314533380123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18514889784674753424218581 433942729328314533380123)
                  ·
                    rfl

theorem cell21_1901476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 2, 7].length) (baseStart_1901476 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1901476 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1901476 prefixEnd_1901476 := by exact prefixLift 1901476
  have htrace : WordTrace (prefixWord ++ tailWord_1901476) baseStart_1901476 baseEnd_1901476 := by
    simpa [prefixWord, tailWord_1901476, baseEnd_1901476] using wordTrace_append hprefix tailTrace_1901476
  have hstable : (prefixWord ++ tailWord_1901476).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1901476).length < 2 ^ (prefixWord ++ tailWord_1901476).sum := by decide
  have hdescent : baseEnd_1901476 < baseStart_1901476 := by decide
  rcases family_descends (prefixWord ++ tailWord_1901476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1901493 : List Nat := [1, 3, 3, 2, 1, 1, 4, 1, 5]
def baseStart_1901493 : Nat := 118140960795 + 1901493 * 2 ^ 59
def prefixEnd_1901493 : Nat := 4983230072969 + 3 ^ 40 * 1901493 * 2
def baseEnd_1901493 : Nat := 433946608959926281596755

theorem tailTrace_1901493 : CollatzResearch.WordTrace tailWord_1901493 prefixEnd_1901493 433946608959926281596755 := by
  unfold tailWord_1901493
  simp only [CollatzResearch.WordTrace]
  refine ⟨69353147300223084994909133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46235431533482056663272755 69353147300223084994909133)
  ·
    refine ⟨26007430237583656873090925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69353147300223084994909133 26007430237583656873090925)
    ·
      refine ⟨9752786339093871327409097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26007430237583656873090925 9752786339093871327409097)
      ·
        refine ⟨7314589754320403495556823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9752786339093871327409097 7314589754320403495556823)
        ·
          refine ⟨10971884631480605243335235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7314589754320403495556823 10971884631480605243335235)
          ·
            refine ⟨16457826947220907865002853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10971884631480605243335235 16457826947220907865002853)
            ·
              refine ⟨3085842552603920224688035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16457826947220907865002853 3085842552603920224688035)
              ·
                refine ⟨4628763828905880337032053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3085842552603920224688035 4628763828905880337032053)
                ·
                  refine ⟨433946608959926281596755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4628763828905880337032053 433946608959926281596755)
                  ·
                    rfl

theorem cell21_1901493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 4, 1, 5].length) (baseStart_1901493 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1901493 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1901493 prefixEnd_1901493 := by exact prefixLift 1901493
  have htrace : WordTrace (prefixWord ++ tailWord_1901493) baseStart_1901493 baseEnd_1901493 := by
    simpa [prefixWord, tailWord_1901493, baseEnd_1901493] using wordTrace_append hprefix tailTrace_1901493
  have hstable : (prefixWord ++ tailWord_1901493).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1901493).length < 2 ^ (prefixWord ++ tailWord_1901493).sum := by decide
  have hdescent : baseEnd_1901493 < baseStart_1901493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1901493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1901521 : List Nat := [1, 2, 2, 1, 2, 1, 5, 7]
def baseStart_1901521 : Nat := 118140960795 + 1901521 * 2 ^ 59
def prefixEnd_1901521 : Nat := 4983230072969 + 3 ^ 40 * 1901521 * 2
def baseEnd_1901521 : Nat := 144650999647134818376677

theorem tailTrace_1901521 : CollatzResearch.WordTrace tailWord_1901521 prefixEnd_1901521 144650999647134818376677 := by
  unfold tailWord_1901521
  simp only [CollatzResearch.WordTrace]
  refine ⟨69354168544121645776928417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46236112362747763851285611 69354168544121645776928417)
  ·
    refine ⟨52015626408091234332696313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69354168544121645776928417 52015626408091234332696313)
    ·
      refine ⟨39011719806068425749522235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52015626408091234332696313 39011719806068425749522235)
      ·
        refine ⟨58517579709102638624283353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39011719806068425749522235 58517579709102638624283353)
        ·
          refine ⟨43888184781826978968212515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58517579709102638624283353 43888184781826978968212515)
          ·
            refine ⟨65832277172740468452318773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43888184781826978968212515 65832277172740468452318773)
            ·
              refine ⟨6171775984944418917404885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65832277172740468452318773 6171775984944418917404885)
              ·
                refine ⟨144650999647134818376677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6171775984944418917404885 144650999647134818376677)
                ·
                  rfl

theorem cell21_1901521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 7].length) (baseStart_1901521 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1901521 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1901521 prefixEnd_1901521 := by exact prefixLift 1901521
  have htrace : WordTrace (prefixWord ++ tailWord_1901521) baseStart_1901521 baseEnd_1901521 := by
    simpa [prefixWord, tailWord_1901521, baseEnd_1901521] using wordTrace_append hprefix tailTrace_1901521
  have hstable : (prefixWord ++ tailWord_1901521).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1901521).length < 2 ^ (prefixWord ++ tailWord_1901521).sum := by decide
  have hdescent : baseEnd_1901521 < baseStart_1901521 := by decide
  rcases family_descends (prefixWord ++ tailWord_1901521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1901558 : List Nat := [5, 1, 1, 1, 3, 3, 2, 1, 4]
def baseStart_1901558 : Nat := 118140960795 + 1901558 * 2 ^ 59
def prefixEnd_1901558 : Nat := 4983230072969 + 3 ^ 40 * 1901558 * 2
def baseEnd_1901558 : Nat := 433961442845500613013289

theorem tailTrace_1901558 : CollatzResearch.WordTrace tailWord_1901558 prefixEnd_1901558 433961442845500613013289 := by
  unfold tailWord_1901558
  simp only [CollatzResearch.WordTrace]
  refine ⟨4334719877811725068501583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46237012029991734064016885 4334719877811725068501583)
  ·
    refine ⟨6502079816717587602752375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4334719877811725068501583 6502079816717587602752375)
    ·
      refine ⟨9753119725076381404128563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6502079816717587602752375 9753119725076381404128563)
      ·
        refine ⟨14629679587614572106192845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9753119725076381404128563 14629679587614572106192845)
        ·
          refine ⟨5486129845355464539822317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14629679587614572106192845 5486129845355464539822317)
          ·
            refine ⟨2057298692008299202433369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5486129845355464539822317 2057298692008299202433369)
            ·
              refine ⟨1542974019006224401825027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2057298692008299202433369 1542974019006224401825027)
              ·
                refine ⟨2314461028509336602737541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1542974019006224401825027 2314461028509336602737541)
                ·
                  refine ⟨433961442845500613013289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2314461028509336602737541 433961442845500613013289)
                  ·
                    rfl

theorem cell21_1901558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 2, 1, 4].length) (baseStart_1901558 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1901558 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1901558 prefixEnd_1901558 := by exact prefixLift 1901558
  have htrace : WordTrace (prefixWord ++ tailWord_1901558) baseStart_1901558 baseEnd_1901558 := by
    simpa [prefixWord, tailWord_1901558, baseEnd_1901558] using wordTrace_append hprefix tailTrace_1901558
  have hstable : (prefixWord ++ tailWord_1901558).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1901558).length < 2 ^ (prefixWord ++ tailWord_1901558).sum := by decide
  have hdescent : baseEnd_1901558 < baseStart_1901558 := by decide
  rcases family_descends (prefixWord ++ tailWord_1901558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1901597 : List Nat := [1, 4, 2, 2, 12]
def baseStart_1901597 : Nat := 118140960795 + 1901597 * 2 ^ 59
def prefixEnd_1901597 : Nat := 4983230072969 + 3 ^ 40 * 1901597 * 2
def baseEnd_1901597 : Nat := 5357658557738829776089

theorem tailTrace_1901597 : CollatzResearch.WordTrace tailWord_1901597 prefixEnd_1901597 5357658557738829776089 := by
  unfold tailWord_1901597
  simp only [CollatzResearch.WordTrace]
  refine ⟨69356940491846310756695045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46237960327897540504463363 69356940491846310756695045)
  ·
    refine ⟨13004426342221183266880321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69356940491846310756695045 13004426342221183266880321)
    ·
      refine ⟨9753319756665887450160241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13004426342221183266880321 9753319756665887450160241)
      ·
        refine ⟨7314989817499415587620181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9753319756665887450160241 7314989817499415587620181)
        ·
          refine ⟨5357658557738829776089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 7314989817499415587620181 5357658557738829776089)
          ·
            rfl

theorem cell21_1901597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 12].length) (baseStart_1901597 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1901597 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1901597 prefixEnd_1901597 := by exact prefixLift 1901597
  have htrace : WordTrace (prefixWord ++ tailWord_1901597) baseStart_1901597 baseEnd_1901597 := by
    simpa [prefixWord, tailWord_1901597, baseEnd_1901597] using wordTrace_append hprefix tailTrace_1901597
  have hstable : (prefixWord ++ tailWord_1901597).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1901597).length < 2 ^ (prefixWord ++ tailWord_1901597).sum := by decide
  have hdescent : baseEnd_1901597 < baseStart_1901597 := by decide
  rcases family_descends (prefixWord ++ tailWord_1901597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1901603 : List Nat := [1, 1, 1, 4, 3, 4, 2, 2, 3]
def baseStart_1901603 : Nat := 118140960795 + 1901603 * 2 ^ 59
def prefixEnd_1901603 : Nat := 4983230072969 + 3 ^ 40 * 1901603 * 2
def baseEnd_1901603 : Nat := 433971712458590534763197

theorem tailTrace_1901603 : CollatzResearch.WordTrace tailWord_1901603 prefixEnd_1901603 433971712458590534763197 := by
  unfold tailWord_1901603
  simp only [CollatzResearch.WordTrace]
  refine ⟨69357159329824573781413463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46238106219883049187608975 69357159329824573781413463)
  ·
    refine ⟨104035738994736860672120195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69357159329824573781413463 104035738994736860672120195)
    ·
      refine ⟨156053608492105291008180293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104035738994736860672120195 156053608492105291008180293)
      ·
        refine ⟨29260051592269742064033805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 156053608492105291008180293 29260051592269742064033805)
        ·
          refine ⟨10972519347101153274012677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29260051592269742064033805 10972519347101153274012677)
          ·
            refine ⟨2057347377581466238877377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10972519347101153274012677 2057347377581466238877377)
            ·
              refine ⟨1543010533186099679158033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2057347377581466238877377 1543010533186099679158033)
              ·
                refine ⟨1157257899889574759368525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1543010533186099679158033 1157257899889574759368525)
                ·
                  refine ⟨433971712458590534763197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1157257899889574759368525 433971712458590534763197)
                  ·
                    rfl

theorem cell21_1901603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 2, 2, 3].length) (baseStart_1901603 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1901603 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1901603 prefixEnd_1901603 := by exact prefixLift 1901603
  have htrace : WordTrace (prefixWord ++ tailWord_1901603) baseStart_1901603 baseEnd_1901603 := by
    simpa [prefixWord, tailWord_1901603, baseEnd_1901603] using wordTrace_append hprefix tailTrace_1901603
  have hstable : (prefixWord ++ tailWord_1901603).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1901603).length < 2 ^ (prefixWord ++ tailWord_1901603).sum := by decide
  have hdescent : baseEnd_1901603 < baseStart_1901603 := by decide
  rcases family_descends (prefixWord ++ tailWord_1901603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1901628 : List Nat := [2, 2, 2, 2, 2, 2, 1, 1, 7]
def baseStart_1901628 : Nat := 118140960795 + 1901628 * 2 ^ 59
def prefixEnd_1901628 : Nat := 4983230072969 + 3 ^ 40 * 1901628 * 2
def baseEnd_1901628 : Nat := 433977417799196046846479

theorem tailTrace_1901628 : CollatzResearch.WordTrace tailWord_1901628 prefixEnd_1901628 433977417799196046846479 := by
  unfold tailWord_1901628
  simp only [CollatzResearch.WordTrace]
  refine ⟨34679035577367001525536769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46238714103156002034049025 34679035577367001525536769)
  ·
    refine ⟨26009276683025251144152577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34679035577367001525536769 26009276683025251144152577)
    ·
      refine ⟨19506957512268938358114433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26009276683025251144152577 19506957512268938358114433)
      ·
        refine ⟨14630218134201703768585825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19506957512268938358114433 14630218134201703768585825)
        ·
          refine ⟨10972663600651277826439369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14630218134201703768585825 10972663600651277826439369)
          ·
            refine ⟨8229497700488458369829527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10972663600651277826439369 8229497700488458369829527)
            ·
              refine ⟨12344246550732687554744291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8229497700488458369829527 12344246550732687554744291)
              ·
                refine ⟨18516369826099031332116437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12344246550732687554744291 18516369826099031332116437)
                ·
                  refine ⟨433977417799196046846479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18516369826099031332116437 433977417799196046846479)
                  ·
                    rfl

theorem cell21_1901628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 1, 7].length) (baseStart_1901628 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1901628 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1901628 prefixEnd_1901628 := by exact prefixLift 1901628
  have htrace : WordTrace (prefixWord ++ tailWord_1901628) baseStart_1901628 baseEnd_1901628 := by
    simpa [prefixWord, tailWord_1901628, baseEnd_1901628] using wordTrace_append hprefix tailTrace_1901628
  have hstable : (prefixWord ++ tailWord_1901628).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1901628).length < 2 ^ (prefixWord ++ tailWord_1901628).sum := by decide
  have hdescent : baseEnd_1901628 < baseStart_1901628 := by decide
  rcases family_descends (prefixWord ++ tailWord_1901628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1901676 : List Nat := [2, 2, 1, 1, 3, 2, 5, 1, 4]
def baseStart_1901676 : Nat := 118140960795 + 1901676 * 2 ^ 59
def prefixEnd_1901676 : Nat := 4983230072969 + 3 ^ 40 * 1901676 * 2
def baseEnd_1901676 : Nat := 433988372053158630046381

theorem tailTrace_1901676 : CollatzResearch.WordTrace tailWord_1901676 prefixEnd_1901676 433988372053158630046381 := by
  unfold tailWord_1901676
  simp only [CollatzResearch.WordTrace]
  refine ⟨34679910929280053624410441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46239881239040071499213921 34679910929280053624410441)
  ·
    refine ⟨26009933196960040218307831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34679910929280053624410441 26009933196960040218307831)
    ·
      refine ⟨39014899795440060327461747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26009933196960040218307831 39014899795440060327461747)
      ·
        refine ⟨58522349693160090491192621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39014899795440060327461747 58522349693160090491192621)
        ·
          refine ⟨21945881134935033934197233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58522349693160090491192621 21945881134935033934197233)
          ·
            refine ⟨16459410851201275450647925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21945881134935033934197233 16459410851201275450647925)
            ·
              refine ⟨1543069767300119573498243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16459410851201275450647925 1543069767300119573498243)
              ·
                refine ⟨2314604650950179360247365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1543069767300119573498243 2314604650950179360247365)
                ·
                  refine ⟨433988372053158630046381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2314604650950179360247365 433988372053158630046381)
                  ·
                    rfl

theorem cell21_1901676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 4].length) (baseStart_1901676 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1901676 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1901676 prefixEnd_1901676 := by exact prefixLift 1901676
  have htrace : WordTrace (prefixWord ++ tailWord_1901676) baseStart_1901676 baseEnd_1901676 := by
    simpa [prefixWord, tailWord_1901676, baseEnd_1901676] using wordTrace_append hprefix tailTrace_1901676
  have hstable : (prefixWord ++ tailWord_1901676).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1901676).length < 2 ^ (prefixWord ++ tailWord_1901676).sum := by decide
  have hdescent : baseEnd_1901676 < baseStart_1901676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1901676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1901763 : List Nat := [1, 1, 1, 3, 1, 1, 1, 3, 9]
def baseStart_1901763 : Nat := 118140960795 + 1901763 * 2 ^ 59
def prefixEnd_1901763 : Nat := 4983230072969 + 3 ^ 40 * 1901763 * 2
def baseEnd_1901763 : Nat := 434008226638465812096203

theorem tailTrace_1901763 : CollatzResearch.WordTrace tailWord_1901763 prefixEnd_1901763 434008226638465812096203 := by
  unfold tailWord_1901763
  simp only [CollatzResearch.WordTrace]
  refine ⟨69362995009244921107237943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46241996672829947404825295 69362995009244921107237943)
  ·
    refine ⟨104044492513867381660856915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69362995009244921107237943 104044492513867381660856915)
    ·
      refine ⟨156066738770801072491285373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104044492513867381660856915 156066738770801072491285373)
      ·
        refine ⟨58525027039050402184232015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156066738770801072491285373 58525027039050402184232015)
        ·
          refine ⟨87787540558575603276348023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58525027039050402184232015 87787540558575603276348023)
          ·
            refine ⟨131681310837863404914522035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87787540558575603276348023 131681310837863404914522035)
            ·
              refine ⟨197521966256795107371783053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131681310837863404914522035 197521966256795107371783053)
              ·
                refine ⟨74070737346298165264418645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 197521966256795107371783053 74070737346298165264418645)
                ·
                  refine ⟨434008226638465812096203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 74070737346298165264418645 434008226638465812096203)
                  ·
                    rfl

theorem cell21_1901763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 9].length) (baseStart_1901763 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1901763 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1901763 prefixEnd_1901763 := by exact prefixLift 1901763
  have htrace : WordTrace (prefixWord ++ tailWord_1901763) baseStart_1901763 baseEnd_1901763 := by
    simpa [prefixWord, tailWord_1901763, baseEnd_1901763] using wordTrace_append hprefix tailTrace_1901763
  have hstable : (prefixWord ++ tailWord_1901763).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1901763).length < 2 ^ (prefixWord ++ tailWord_1901763).sum := by decide
  have hdescent : baseEnd_1901763 < baseStart_1901763 := by decide
  rcases family_descends (prefixWord ++ tailWord_1901763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1901797 : List Nat := [1, 3, 1, 4, 3, 1, 1, 2, 5]
def baseStart_1901797 : Nat := 118140960795 + 1901797 * 2 ^ 59
def prefixEnd_1901797 : Nat := 4983230072969 + 3 ^ 40 * 1901797 * 2
def baseEnd_1901797 : Nat := 434015985901689308529467

theorem tailTrace_1901797 : CollatzResearch.WordTrace tailWord_1901797 prefixEnd_1901797 434015985901689308529467 := by
  unfold tailWord_1901797
  simp only [CollatzResearch.WordTrace]
  refine ⟨69364235091121744913975645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46242823394081163275983763 69364235091121744913975645)
  ·
    refine ⟨26011588159170654342740867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69364235091121744913975645 26011588159170654342740867)
    ·
      refine ⟨39017382238755981514111301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26011588159170654342740867 39017382238755981514111301)
      ·
        refine ⟨7315759169766746533895869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39017382238755981514111301 7315759169766746533895869)
        ·
          refine ⟨2743409688662529950210951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7315759169766746533895869 2743409688662529950210951)
          ·
            refine ⟨4115114532993794925316427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2743409688662529950210951 4115114532993794925316427)
            ·
              refine ⟨6172671799490692387974641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4115114532993794925316427 6172671799490692387974641)
              ·
                refine ⟨4629503849618019290980981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6172671799490692387974641 4629503849618019290980981)
                ·
                  refine ⟨434015985901689308529467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4629503849618019290980981 434015985901689308529467)
                  ·
                    rfl

theorem cell21_1901797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 2, 5].length) (baseStart_1901797 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1901797 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1901797 prefixEnd_1901797 := by exact prefixLift 1901797
  have htrace : WordTrace (prefixWord ++ tailWord_1901797) baseStart_1901797 baseEnd_1901797 := by
    simpa [prefixWord, tailWord_1901797, baseEnd_1901797] using wordTrace_append hprefix tailTrace_1901797
  have hstable : (prefixWord ++ tailWord_1901797).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1901797).length < 2 ^ (prefixWord ++ tailWord_1901797).sum := by decide
  have hdescent : baseEnd_1901797 < baseStart_1901797 := by decide
  rcases family_descends (prefixWord ++ tailWord_1901797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
