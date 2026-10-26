import V185TrunkScan23Chunk1096

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6494929 : List Nat := [1, 2, 2, 1, 2, 3, 4, 1, 7]
def baseStart_6494929 : Nat := 118140960795 + 6494929 * 2 ^ 59
def prefixEnd_6494929 : Nat := 4983230072969 + 3 ^ 40 * 6494929 * 2
def baseEnd_6494929 : Nat := 370557821536191588235319

theorem tailTrace_6494929 : CollatzResearch.WordTrace tailWord_6494929 prefixEnd_6494929 370557821536191588235319 := by
  unfold tailWord_6494929
  simp only [CollatzResearch.WordTrace]
  refine ⟨236889521886988953406759841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157926347924659302271173227 236889521886988953406759841)
  ·
    refine ⟨177667141415241715055069881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236889521886988953406759841 177667141415241715055069881)
    ·
      refine ⟨133250356061431286291302411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177667141415241715055069881 133250356061431286291302411)
      ·
        refine ⟨199875534092146929436953617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133250356061431286291302411 199875534092146929436953617)
        ·
          refine ⟨149906650569110197077715213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 199875534092146929436953617 149906650569110197077715213)
          ·
            refine ⟨56214993963416323904143205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 149906650569110197077715213 56214993963416323904143205)
            ·
              refine ⟨10540311368140560732026851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56214993963416323904143205 10540311368140560732026851)
              ·
                refine ⟨15810467052210841098040277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10540311368140560732026851 15810467052210841098040277)
                ·
                  refine ⟨370557821536191588235319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15810467052210841098040277 370557821536191588235319)
                  ·
                    rfl

theorem cell23_6494929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 4, 1, 7].length) (baseStart_6494929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6494929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6494929 prefixEnd_6494929 := by exact prefixLift 6494929
  have htrace : WordTrace (prefixWord ++ tailWord_6494929) baseStart_6494929 baseEnd_6494929 := by
    simpa [prefixWord, tailWord_6494929, baseEnd_6494929] using wordTrace_append hprefix tailTrace_6494929
  have hstable : (prefixWord ++ tailWord_6494929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6494929).length < 2 ^ (prefixWord ++ tailWord_6494929).sum := by decide
  have hdescent : baseEnd_6494929 < baseStart_6494929 := by decide
  rcases family_descends (prefixWord ++ tailWord_6494929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6494940 : List Nat := [2, 2, 5, 1, 1, 1, 3, 1, 1, 4, 2]
def baseStart_6494940 : Nat := 118140960795 + 6494940 * 2 ^ 59
def prefixEnd_6494940 : Nat := 4983230072969 + 3 ^ 40 * 6494940 * 2
def baseEnd_6494940 : Nat := 3335026042112923751080321

theorem tailTrace_6494940 : CollatzResearch.WordTrace tailWord_6494940 prefixEnd_6494940 3335026042112923751080321 := by
  unfold tailWord_6494940
  simp only [CollatzResearch.WordTrace]
  refine ⟨118444961544974551142705137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157926615393299401523606849 118444961544974551142705137)
  ·
    refine ⟨88833721158730913357028853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118444961544974551142705137 88833721158730913357028853)
    ·
      refine ⟨8328161358631023127221455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 88833721158730913357028853 8328161358631023127221455)
      ·
        refine ⟨12492242037946534690832183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8328161358631023127221455 12492242037946534690832183)
        ·
          refine ⟨18738363056919802036248275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12492242037946534690832183 18738363056919802036248275)
          ·
            refine ⟨28107544585379703054372413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18738363056919802036248275 28107544585379703054372413)
            ·
              refine ⟨10540329219517388645389655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28107544585379703054372413 10540329219517388645389655)
              ·
                refine ⟨15810493829276082968084483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10540329219517388645389655 15810493829276082968084483)
                ·
                  refine ⟨23715740743914124452126725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15810493829276082968084483 23715740743914124452126725)
                  ·
                    refine ⟨4446701389483898334773761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23715740743914124452126725 4446701389483898334773761)
                    ·
                      refine ⟨3335026042112923751080321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4446701389483898334773761 3335026042112923751080321)
                      ·
                        rfl

theorem cell23_6494940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 3, 1, 1, 4, 2].length) (baseStart_6494940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6494940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6494940 prefixEnd_6494940 := by exact prefixLift 6494940
  have htrace : WordTrace (prefixWord ++ tailWord_6494940) baseStart_6494940 baseEnd_6494940 := by
    simpa [prefixWord, tailWord_6494940, baseEnd_6494940] using wordTrace_append hprefix tailTrace_6494940
  have hstable : (prefixWord ++ tailWord_6494940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6494940).length < 2 ^ (prefixWord ++ tailWord_6494940).sum := by decide
  have hdescent : baseEnd_6494940 < baseStart_6494940 := by decide
  rcases family_descends (prefixWord ++ tailWord_6494940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6494959 : List Nat := [1, 1, 2, 1, 5, 2, 2, 1, 1, 7]
def baseStart_6494959 : Nat := 118140960795 + 6494959 * 2 ^ 59
def prefixEnd_6494959 : Nat := 4983230072969 + 3 ^ 40 * 6494959 * 2
def baseEnd_6494959 : Nat := 1111678599415119725580911

theorem tailTrace_6494959 : CollatzResearch.WordTrace tailWord_6494959 prefixEnd_6494959 1111678599415119725580911 := by
  unfold tailWord_6494959
  simp only [CollatzResearch.WordTrace]
  refine ⟨236890616076880268530351931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157927077384586845686901287 236890616076880268530351931)
  ·
    refine ⟨355335924115320402795527897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236890616076880268530351931 355335924115320402795527897)
    ·
      refine ⟨266501943086490302096645923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 355335924115320402795527897 266501943086490302096645923)
      ·
        refine ⟨399752914629735453144968885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266501943086490302096645923 399752914629735453144968885)
        ·
          refine ⟨37476835746537698732340833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 399752914629735453144968885 37476835746537698732340833)
          ·
            refine ⟨28107626809903274049255625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37476835746537698732340833 28107626809903274049255625)
            ·
              refine ⟨21080720107427455536941719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28107626809903274049255625 21080720107427455536941719)
              ·
                refine ⟨31621080161141183305412579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21080720107427455536941719 31621080161141183305412579)
                ·
                  refine ⟨47431620241711774958118869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31621080161141183305412579 47431620241711774958118869)
                  ·
                    refine ⟨1111678599415119725580911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47431620241711774958118869 1111678599415119725580911)
                    ·
                      rfl

theorem cell23_6494959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 1, 1, 7].length) (baseStart_6494959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6494959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6494959 prefixEnd_6494959 := by exact prefixLift 6494959
  have htrace : WordTrace (prefixWord ++ tailWord_6494959) baseStart_6494959 baseEnd_6494959 := by
    simpa [prefixWord, tailWord_6494959, baseEnd_6494959] using wordTrace_append hprefix tailTrace_6494959
  have hstable : (prefixWord ++ tailWord_6494959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6494959).length < 2 ^ (prefixWord ++ tailWord_6494959).sum := by decide
  have hdescent : baseEnd_6494959 < baseStart_6494959 := by decide
  rcases family_descends (prefixWord ++ tailWord_6494959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6495063 : List Nat := [1, 1, 3, 2, 4, 1, 1, 1, 5, 1, 3]
def baseStart_6495063 : Nat := 118140960795 + 6495063 * 2 ^ 59
def prefixEnd_6495063 : Nat := 4983230072969 + 3 ^ 40 * 6495063 * 2
def baseEnd_6495063 : Nat := 3335089200233426769842255

theorem tailTrace_6495063 : CollatzResearch.WordTrace tailWord_6495063 prefixEnd_6495063 3335089200233426769842255 := by
  unfold tailWord_6495063
  simp only [CollatzResearch.WordTrace]
  refine ⟨236894409268503494292137843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157929606179002329528091895 236894409268503494292137843)
  ·
    refine ⟨355341613902755241438206765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236894409268503494292137843 355341613902755241438206765)
    ·
      refine ⟨133253105213533215539327537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 355341613902755241438206765 133253105213533215539327537)
      ·
        refine ⟨99939828910149911654495653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133253105213533215539327537 99939828910149911654495653)
        ·
          refine ⟨18738717920653108435217935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 99939828910149911654495653 18738717920653108435217935)
          ·
            refine ⟨28108076880979662652826903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18738717920653108435217935 28108076880979662652826903)
            ·
              refine ⟨42162115321469493979240355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28108076880979662652826903 42162115321469493979240355)
              ·
                refine ⟨63243172982204240968860533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42162115321469493979240355 63243172982204240968860533)
                ·
                  refine ⟨5929047467081647590830675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 63243172982204240968860533 5929047467081647590830675)
                  ·
                    refine ⟨8893571200622471386246013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5929047467081647590830675 8893571200622471386246013)
                    ·
                      refine ⟨3335089200233426769842255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8893571200622471386246013 3335089200233426769842255)
                      ·
                        rfl

theorem cell23_6495063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 1, 5, 1, 3].length) (baseStart_6495063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6495063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6495063 prefixEnd_6495063 := by exact prefixLift 6495063
  have htrace : WordTrace (prefixWord ++ tailWord_6495063) baseStart_6495063 baseEnd_6495063 := by
    simpa [prefixWord, tailWord_6495063, baseEnd_6495063] using wordTrace_append hprefix tailTrace_6495063
  have hstable : (prefixWord ++ tailWord_6495063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6495063).length < 2 ^ (prefixWord ++ tailWord_6495063).sum := by decide
  have hdescent : baseEnd_6495063 < baseStart_6495063 := by decide
  rcases family_descends (prefixWord ++ tailWord_6495063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6495066 : List Nat := [3, 1, 1, 2, 1, 4, 2, 1, 3, 5]
def baseStart_6495066 : Nat := 118140960795 + 6495066 * 2 ^ 59
def prefixEnd_6495066 : Nat := 4983230072969 + 3 ^ 40 * 6495066 * 2
def baseEnd_6495066 : Nat := 1111696913558463419368247

theorem tailTrace_6495066 : CollatzResearch.WordTrace tailWord_6495066 prefixEnd_6495066 1111696913558463419368247 := by
  unfold tailWord_6495066
  simp only [CollatzResearch.WordTrace]
  refine ⟨59223629671873156451124263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157929679124995083869664701 59223629671873156451124263)
  ·
    refine ⟨88835444507809734676686395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59223629671873156451124263 88835444507809734676686395)
    ·
      refine ⟨133253166761714602015029593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88835444507809734676686395 133253166761714602015029593)
      ·
        refine ⟨99939875071285951511272195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133253166761714602015029593 99939875071285951511272195)
        ·
          refine ⟨149909812606928927266908293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99939875071285951511272195 149909812606928927266908293)
          ·
            refine ⟨28108089863799173862545305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 149909812606928927266908293 28108089863799173862545305)
            ·
              refine ⟨21081067397849380396908979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28108089863799173862545305 21081067397849380396908979)
              ·
                refine ⟨31621601096774070595363469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21081067397849380396908979 31621601096774070595363469)
                ·
                  refine ⟨11858100411290276473261301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31621601096774070595363469 11858100411290276473261301)
                  ·
                    refine ⟨1111696913558463419368247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11858100411290276473261301 1111696913558463419368247)
                    ·
                      rfl

theorem cell23_6495066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 1, 3, 5].length) (baseStart_6495066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6495066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6495066 prefixEnd_6495066 := by exact prefixLift 6495066
  have htrace : WordTrace (prefixWord ++ tailWord_6495066) baseStart_6495066 baseEnd_6495066 := by
    simpa [prefixWord, tailWord_6495066, baseEnd_6495066] using wordTrace_append hprefix tailTrace_6495066
  have hstable : (prefixWord ++ tailWord_6495066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6495066).length < 2 ^ (prefixWord ++ tailWord_6495066).sum := by decide
  have hdescent : baseEnd_6495066 < baseStart_6495066 := by decide
  rcases family_descends (prefixWord ++ tailWord_6495066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6495073 : List Nat := [1, 2, 3, 1, 1, 1, 2, 5, 2, 3, 2]
def baseStart_6495073 : Nat := 118140960795 + 6495073 * 2 ^ 59
def prefixEnd_6495073 : Nat := 4983230072969 + 3 ^ 40 * 6495073 * 2
def baseEnd_6495073 : Nat := 3335094335039971730717209

theorem tailTrace_6495073 : CollatzResearch.WordTrace tailWord_6495073 prefixEnd_6495073 3335094335039971730717209 := by
  unfold tailWord_6495073
  simp only [CollatzResearch.WordTrace]
  refine ⟨236894773998467266000001873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157929849332311510666667915 236894773998467266000001873)
  ·
    refine ⟨177671080498850449500001405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236894773998467266000001873 177671080498850449500001405)
    ·
      refine ⟨66626655187068918562500527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177671080498850449500001405 66626655187068918562500527)
      ·
        refine ⟨99939982780603377843750791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66626655187068918562500527 99939982780603377843750791)
        ·
          refine ⟨149909974170905066765626187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99939982780603377843750791 149909974170905066765626187)
          ·
            refine ⟨224864961256357600148439281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149909974170905066765626187 224864961256357600148439281)
            ·
              refine ⟨168648720942268200111329461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 224864961256357600148439281 168648720942268200111329461)
              ·
                refine ⟨15810817588337643760437137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 168648720942268200111329461 15810817588337643760437137)
                ·
                  refine ⟨11858113191253232820327853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15810817588337643760437137 11858113191253232820327853)
                  ·
                    refine ⟨4446792446719962307622945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11858113191253232820327853 4446792446719962307622945)
                    ·
                      refine ⟨3335094335039971730717209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4446792446719962307622945 3335094335039971730717209)
                      ·
                        rfl

theorem cell23_6495073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 5, 2, 3, 2].length) (baseStart_6495073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6495073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6495073 prefixEnd_6495073 := by exact prefixLift 6495073
  have htrace : WordTrace (prefixWord ++ tailWord_6495073) baseStart_6495073 baseEnd_6495073 := by
    simpa [prefixWord, tailWord_6495073, baseEnd_6495073] using wordTrace_append hprefix tailTrace_6495073
  have hstable : (prefixWord ++ tailWord_6495073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6495073).length < 2 ^ (prefixWord ++ tailWord_6495073).sum := by decide
  have hdescent : baseEnd_6495073 < baseStart_6495073 := by decide
  rcases family_descends (prefixWord ++ tailWord_6495073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6495083 : List Nat := [1, 1, 1, 1, 2, 2, 8, 1, 1, 5]
def baseStart_6495083 : Nat := 118140960795 + 6495083 * 2 ^ 59
def prefixEnd_6495083 : Nat := 4983230072969 + 3 ^ 40 * 6495083 * 2
def baseEnd_6495083 : Nat := 1111699823282172230530721

theorem tailTrace_6495083 : CollatzResearch.WordTrace tailWord_6495083 prefixEnd_6495083 1111699823282172230530721 := by
  unfold tailWord_6495083
  simp only [CollatzResearch.WordTrace]
  refine ⟨236895138728431037707865903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157930092485620691805243935 236895138728431037707865903)
  ·
    refine ⟨355342708092646556561798855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236895138728431037707865903 355342708092646556561798855)
    ·
      refine ⟨533014062138969834842698283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 355342708092646556561798855 533014062138969834842698283)
      ·
        refine ⟨799521093208454752264047425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 533014062138969834842698283 799521093208454752264047425)
        ·
          refine ⟨599640819906341064198035569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 799521093208454752264047425 599640819906341064198035569)
          ·
            refine ⟨449730614929755798148526677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 599640819906341064198035569 449730614929755798148526677)
            ·
              refine ⟨5270280643708075759553047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 449730614929755798148526677 5270280643708075759553047)
              ·
                refine ⟨7905420965562113639329571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5270280643708075759553047 7905420965562113639329571)
                ·
                  refine ⟨11858131448343170458994357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7905420965562113639329571 11858131448343170458994357)
                  ·
                    refine ⟨1111699823282172230530721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11858131448343170458994357 1111699823282172230530721)
                    ·
                      rfl

theorem cell23_6495083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 8, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 8, 1, 1, 5].length) (baseStart_6495083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6495083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6495083 prefixEnd_6495083 := by exact prefixLift 6495083
  have htrace : WordTrace (prefixWord ++ tailWord_6495083) baseStart_6495083 baseEnd_6495083 := by
    simpa [prefixWord, tailWord_6495083, baseEnd_6495083] using wordTrace_append hprefix tailTrace_6495083
  have hstable : (prefixWord ++ tailWord_6495083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6495083).length < 2 ^ (prefixWord ++ tailWord_6495083).sum := by decide
  have hdescent : baseEnd_6495083 < baseStart_6495083 := by decide
  rcases family_descends (prefixWord ++ tailWord_6495083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6495113 : List Nat := [1, 2, 1, 1, 5, 4, 1, 1, 1, 6]
def baseStart_6495113 : Nat := 118140960795 + 6495113 * 2 ^ 59
def prefixEnd_6495113 : Nat := 4983230072969 + 3 ^ 40 * 6495113 * 2
def baseEnd_6495113 : Nat := 1111704958088717191405675

theorem tailTrace_6495113 : CollatzResearch.WordTrace tailWord_6495113 prefixEnd_6495113 1111704958088717191405675 := by
  unfold tailWord_6495113
  simp only [CollatzResearch.WordTrace]
  refine ⟨236896232918322352831457993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157930821945548235220971995 236896232918322352831457993)
  ·
    refine ⟨177672174688741764623593495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236896232918322352831457993 177672174688741764623593495)
    ·
      refine ⟨266508262033112646935390243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177672174688741764623593495 266508262033112646935390243)
      ·
        refine ⟨399762393049668970403085365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266508262033112646935390243 399762393049668970403085365)
        ·
          refine ⟨37477724348406465975289253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 399762393049668970403085365 37477724348406465975289253)
          ·
            refine ⟨7027073315326212370366735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37477724348406465975289253 7027073315326212370366735)
            ·
              refine ⟨10540609972989318555550103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7027073315326212370366735 10540609972989318555550103)
              ·
                refine ⟨15810914959483977833325155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10540609972989318555550103 15810914959483977833325155)
                ·
                  refine ⟨23716372439225966749987733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15810914959483977833325155 23716372439225966749987733)
                  ·
                    refine ⟨1111704958088717191405675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23716372439225966749987733 1111704958088717191405675)
                    ·
                      rfl

theorem cell23_6495113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 1, 1, 1, 6].length) (baseStart_6495113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6495113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6495113 prefixEnd_6495113 := by exact prefixLift 6495113
  have htrace : WordTrace (prefixWord ++ tailWord_6495113) baseStart_6495113 baseEnd_6495113 := by
    simpa [prefixWord, tailWord_6495113, baseEnd_6495113] using wordTrace_append hprefix tailTrace_6495113
  have hstable : (prefixWord ++ tailWord_6495113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6495113).length < 2 ^ (prefixWord ++ tailWord_6495113).sum := by decide
  have hdescent : baseEnd_6495113 < baseStart_6495113 := by decide
  rcases family_descends (prefixWord ++ tailWord_6495113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6495119 : List Nat := [1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 9]
def baseStart_6495119 : Nat := 118140960795 + 6495119 * 2 ^ 59
def prefixEnd_6495119 : Nat := 4983230072969 + 3 ^ 40 * 6495119 * 2
def baseEnd_6495119 : Nat := 3335117955150078550741997

theorem tailTrace_6495119 : CollatzResearch.WordTrace tailWord_6495119 prefixEnd_6495119 3335117955150078550741997 := by
  unfold tailWord_6495119
  simp only [CollatzResearch.WordTrace]
  refine ⟨236896451756300615856176411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157930967837533743904117607 236896451756300615856176411)
  ·
    refine ⟨355344677634450923784264617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236896451756300615856176411 355344677634450923784264617)
    ·
      refine ⟨266508508225838192838198463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 355344677634450923784264617 266508508225838192838198463)
      ·
        refine ⟨399762762338757289257297695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266508508225838192838198463 399762762338757289257297695)
        ·
          refine ⟨599644143508135933885946543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 399762762338757289257297695 599644143508135933885946543)
          ·
            refine ⟨899466215262203900828919815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 599644143508135933885946543 899466215262203900828919815)
            ·
              refine ⟨1349199322893305851243379723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 899466215262203900828919815 1349199322893305851243379723)
              ·
                refine ⟨2023798984339958776865069585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1349199322893305851243379723 2023798984339958776865069585)
                ·
                  refine ⟨1517849238254969082648802189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2023798984339958776865069585 1517849238254969082648802189)
                  ·
                    refine ⟨569193464345613405993300821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1517849238254969082648802189 569193464345613405993300821)
                    ·
                      refine ⟨3335117955150078550741997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 569193464345613405993300821 3335117955150078550741997)
                      ·
                        rfl

theorem cell23_6495119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 9].length) (baseStart_6495119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6495119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6495119 prefixEnd_6495119 := by exact prefixLift 6495119
  have htrace : WordTrace (prefixWord ++ tailWord_6495119) baseStart_6495119 baseEnd_6495119 := by
    simpa [prefixWord, tailWord_6495119, baseEnd_6495119] using wordTrace_append hprefix tailTrace_6495119
  have hstable : (prefixWord ++ tailWord_6495119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6495119).length < 2 ^ (prefixWord ++ tailWord_6495119).sum := by decide
  have hdescent : baseEnd_6495119 < baseStart_6495119 := by decide
  rcases family_descends (prefixWord ++ tailWord_6495119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6495143 : List Nat := [1, 1, 6, 1, 3, 2, 9]
def baseStart_6495143 : Nat := 118140960795 + 6495143 * 2 ^ 59
def prefixEnd_6495143 : Nat := 4983230072969 + 3 ^ 40 * 6495143 * 2
def baseEnd_6495143 : Nat := 41174447885009709343727

theorem tailTrace_6495143 : CollatzResearch.WordTrace tailWord_6495143 prefixEnd_6495143 41174447885009709343727 := by
  unfold tailWord_6495143
  simp only [CollatzResearch.WordTrace]
  refine ⟨236897327108213667955050083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157931551405475778636700055 236897327108213667955050083)
  ·
    refine ⟨355345990662320501932575125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236897327108213667955050083 355345990662320501932575125)
    ·
      refine ⟨16656843312296273528089459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 355345990662320501932575125 16656843312296273528089459)
      ·
        refine ⟨24985264968444410292134189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16656843312296273528089459 24985264968444410292134189)
        ·
          refine ⟨9369474363166653859550321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24985264968444410292134189 9369474363166653859550321)
          ·
            refine ⟨7027105772374990394662741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9369474363166653859550321 7027105772374990394662741)
            ·
              refine ⟨41174447885009709343727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7027105772374990394662741 41174447885009709343727)
              ·
                rfl

theorem cell23_6495143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 9].length) (baseStart_6495143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6495143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6495143 prefixEnd_6495143 := by exact prefixLift 6495143
  have htrace : WordTrace (prefixWord ++ tailWord_6495143) baseStart_6495143 baseEnd_6495143 := by
    simpa [prefixWord, tailWord_6495143, baseEnd_6495143] using wordTrace_append hprefix tailTrace_6495143
  have hstable : (prefixWord ++ tailWord_6495143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6495143).length < 2 ^ (prefixWord ++ tailWord_6495143).sum := by decide
  have hdescent : baseEnd_6495143 < baseStart_6495143 := by decide
  rcases family_descends (prefixWord ++ tailWord_6495143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6495180 : List Nat := [2, 2, 1, 4, 1, 1, 3, 1, 3, 3, 2]
def baseStart_6495180 : Nat := 118140960795 + 6495180 * 2 ^ 59
def prefixEnd_6495180 : Nat := 4983230072969 + 3 ^ 40 * 6495180 * 2
def baseEnd_6495180 : Nat := 3335149277470002812079217

theorem tailTrace_6495180 : CollatzResearch.WordTrace tailWord_6495180 prefixEnd_6495180 3335149277470002812079217 := by
  unfold tailWord_6495180
  simp only [CollatzResearch.WordTrace]
  refine ⟨118449338304539811637073497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157932451072719748849431329 118449338304539811637073497)
  ·
    refine ⟨88837003728404858727805123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118449338304539811637073497 88837003728404858727805123)
    ·
      refine ⟨133255505592607288091707685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88837003728404858727805123 133255505592607288091707685)
      ·
        refine ⟨24985407298613866517195191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 133255505592607288091707685 24985407298613866517195191)
        ·
          refine ⟨37478110947920799775792787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24985407298613866517195191 37478110947920799775792787)
          ·
            refine ⟨56217166421881199663689181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37478110947920799775792787 56217166421881199663689181)
            ·
              refine ⟨21081437408205449873883443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56217166421881199663689181 21081437408205449873883443)
              ·
                refine ⟨31622156112308174810825165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21081437408205449873883443 31622156112308174810825165)
                ·
                  refine ⟨11858308542115565554059437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31622156112308174810825165 11858308542115565554059437)
                  ·
                    refine ⟨4446865703293337082772289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11858308542115565554059437 4446865703293337082772289)
                    ·
                      refine ⟨3335149277470002812079217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4446865703293337082772289 3335149277470002812079217)
                      ·
                        rfl

theorem cell23_6495180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 1, 3, 3, 2].length) (baseStart_6495180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6495180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6495180 prefixEnd_6495180 := by exact prefixLift 6495180
  have htrace : WordTrace (prefixWord ++ tailWord_6495180) baseStart_6495180 baseEnd_6495180 := by
    simpa [prefixWord, tailWord_6495180, baseEnd_6495180] using wordTrace_append hprefix tailTrace_6495180
  have hstable : (prefixWord ++ tailWord_6495180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6495180).length < 2 ^ (prefixWord ++ tailWord_6495180).sum := by decide
  have hdescent : baseEnd_6495180 < baseStart_6495180 := by decide
  rcases family_descends (prefixWord ++ tailWord_6495180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6495205 : List Nat := [1, 3, 1, 6, 2, 1, 2, 2, 1, 2, 2]
def baseStart_6495205 : Nat := 118140960795 + 6495205 * 2 ^ 59
def prefixEnd_6495205 : Nat := 4983230072969 + 3 ^ 40 * 6495205 * 2
def baseEnd_6495205 : Nat := 3335162114486365214266603

theorem tailTrace_6495205 : CollatzResearch.WordTrace tailWord_6495205 prefixEnd_6495205 3335162114486365214266603 := by
  unfold tailWord_6495205
  simp only [CollatzResearch.WordTrace]
  refine ⟨236899588433989052543807069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157933058955992701695871379 236899588433989052543807069)
  ·
    refine ⟨88837345662745894703927651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 236899588433989052543807069 88837345662745894703927651)
    ·
      refine ⟨133256018494118842055891477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88837345662745894703927651 133256018494118842055891477)
      ·
        refine ⟨6246375866911820721369913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 133256018494118842055891477 6246375866911820721369913)
        ·
          refine ⟨4684781900183865541027435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6246375866911820721369913 4684781900183865541027435)
          ·
            refine ⟨7027172850275798311541153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4684781900183865541027435 7027172850275798311541153)
            ·
              refine ⟨5270379637706848733655865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7027172850275798311541153 5270379637706848733655865)
              ·
                refine ⟨3952784728280136550241899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5270379637706848733655865 3952784728280136550241899)
                ·
                  refine ⟨5929177092420204825362849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3952784728280136550241899 5929177092420204825362849)
                  ·
                    refine ⟨4446882819315153619022137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5929177092420204825362849 4446882819315153619022137)
                    ·
                      refine ⟨3335162114486365214266603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4446882819315153619022137 3335162114486365214266603)
                      ·
                        rfl

theorem cell23_6495205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 2, 2, 1, 2, 2].length) (baseStart_6495205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6495205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6495205 prefixEnd_6495205 := by exact prefixLift 6495205
  have htrace : WordTrace (prefixWord ++ tailWord_6495205) baseStart_6495205 baseEnd_6495205 := by
    simpa [prefixWord, tailWord_6495205, baseEnd_6495205] using wordTrace_append hprefix tailTrace_6495205
  have hstable : (prefixWord ++ tailWord_6495205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6495205).length < 2 ^ (prefixWord ++ tailWord_6495205).sum := by decide
  have hdescent : baseEnd_6495205 < baseStart_6495205 := by decide
  rcases family_descends (prefixWord ++ tailWord_6495205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6495216 : List Nat := [2, 1, 1, 1, 3, 2, 1, 5, 7]
def baseStart_6495216 : Nat := 118140960795 + 6495216 * 2 ^ 59
def prefixEnd_6495216 : Nat := 4983230072969 + 3 ^ 40 * 6495216 * 2
def baseEnd_6495216 : Nat := 370574195863729407914339

theorem tailTrace_6495216 : CollatzResearch.WordTrace tailWord_6495216 prefixEnd_6495216 370574195863729407914339 := by
  unfold tailWord_6495216
  simp only [CollatzResearch.WordTrace]
  refine ⟨118449994818474600711228751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157933326424632800948305001 118449994818474600711228751)
  ·
    refine ⟨177674992227711901066843127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118449994818474600711228751 177674992227711901066843127)
    ·
      refine ⟨266512488341567851600264691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177674992227711901066843127 266512488341567851600264691)
      ·
        refine ⟨399768732512351777400397037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266512488341567851600264691 399768732512351777400397037)
        ·
          refine ⟨149913274692131916525148889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 399768732512351777400397037 149913274692131916525148889)
          ·
            refine ⟨112434956019098937393861667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149913274692131916525148889 112434956019098937393861667)
            ·
              refine ⟨168652434028648406090792501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112434956019098937393861667 168652434028648406090792501)
              ·
                refine ⟨15811165690185788071011797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 168652434028648406090792501 15811165690185788071011797)
                ·
                  refine ⟨370574195863729407914339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15811165690185788071011797 370574195863729407914339)
                  ·
                    rfl

theorem cell23_6495216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 5, 7].length) (baseStart_6495216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6495216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6495216 prefixEnd_6495216 := by exact prefixLift 6495216
  have htrace : WordTrace (prefixWord ++ tailWord_6495216) baseStart_6495216 baseEnd_6495216 := by
    simpa [prefixWord, tailWord_6495216, baseEnd_6495216] using wordTrace_append hprefix tailTrace_6495216
  have hstable : (prefixWord ++ tailWord_6495216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6495216).length < 2 ^ (prefixWord ++ tailWord_6495216).sum := by decide
  have hdescent : baseEnd_6495216 < baseStart_6495216 := by decide
  rcases family_descends (prefixWord ++ tailWord_6495216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6495233 : List Nat := [1, 2, 4, 1, 2, 3, 1, 2, 7]
def baseStart_6495233 : Nat := 118140960795 + 6495233 * 2 ^ 59
def prefixEnd_6495233 : Nat := 4983230072969 + 3 ^ 40 * 6495233 * 2
def baseEnd_6495233 : Nat := 370575165771632344968497

theorem tailTrace_6495233 : CollatzResearch.WordTrace tailWord_6495233 prefixEnd_6495233 370575165771632344968497 := by
  unfold tailWord_6495233
  simp only [CollatzResearch.WordTrace]
  refine ⟨236900609677887613325826353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157933739785258408883884235 236900609677887613325826353)
  ·
    refine ⟨177675457258415709994369765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236900609677887613325826353 177675457258415709994369765)
    ·
      refine ⟨33314148235952945623944331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 177675457258415709994369765 33314148235952945623944331)
      ·
        refine ⟨49971222353929418435916497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33314148235952945623944331 49971222353929418435916497)
        ·
          refine ⟨37478416765447063826937373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49971222353929418435916497 37478416765447063826937373)
          ·
            refine ⟨14054406287042648935101515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37478416765447063826937373 14054406287042648935101515)
            ·
              refine ⟨21081609430563973402652273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14054406287042648935101515 21081609430563973402652273)
              ·
                refine ⟨15811207072922980051989205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21081609430563973402652273 15811207072922980051989205)
                ·
                  refine ⟨370575165771632344968497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15811207072922980051989205 370575165771632344968497)
                  ·
                    rfl

theorem cell23_6495233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 2, 7].length) (baseStart_6495233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6495233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6495233 prefixEnd_6495233 := by exact prefixLift 6495233
  have htrace : WordTrace (prefixWord ++ tailWord_6495233) baseStart_6495233 baseEnd_6495233 := by
    simpa [prefixWord, tailWord_6495233, baseEnd_6495233] using wordTrace_append hprefix tailTrace_6495233
  have hstable : (prefixWord ++ tailWord_6495233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6495233).length < 2 ^ (prefixWord ++ tailWord_6495233).sum := by decide
  have hdescent : baseEnd_6495233 < baseStart_6495233 := by decide
  rcases family_descends (prefixWord ++ tailWord_6495233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6495261 : List Nat := [1, 4, 2, 2, 3, 2, 1, 2, 2, 2, 2]
def baseStart_6495261 : Nat := 118140960795 + 6495261 * 2 ^ 59
def prefixEnd_6495261 : Nat := 4983230072969 + 3 ^ 40 * 6495261 * 2
def baseEnd_6495261 : Nat := 3335190869403016995166345

theorem tailTrace_6495261 : CollatzResearch.WordTrace tailWord_6495261 prefixEnd_6495261 3335190869403016995166345 := by
  unfold tailWord_6495261
  simp only [CollatzResearch.WordTrace]
  refine ⟨236901630921786174107845637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157934420614524116071897091 236901630921786174107845637)
  ·
    refine ⟨44419055797834907645221057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 236901630921786174107845637 44419055797834907645221057)
    ·
      refine ⟨33314291848376180733915793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44419055797834907645221057 33314291848376180733915793)
      ·
        refine ⟨24985718886282135550436845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33314291848376180733915793 24985718886282135550436845)
        ·
          refine ⟨9369644582355800831413817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24985718886282135550436845 9369644582355800831413817)
          ·
            refine ⟨7027233436766850623560363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9369644582355800831413817 7027233436766850623560363)
            ·
              refine ⟨10540850155150275935340545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7027233436766850623560363 10540850155150275935340545)
              ·
                refine ⟨7905637616362706951505409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10540850155150275935340545 7905637616362706951505409)
                ·
                  refine ⟨5929228212272030213629057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7905637616362706951505409 5929228212272030213629057)
                  ·
                    refine ⟨4446921159204022660221793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5929228212272030213629057 4446921159204022660221793)
                    ·
                      refine ⟨3335190869403016995166345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4446921159204022660221793 3335190869403016995166345)
                      ·
                        rfl

theorem cell23_6495261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 1, 2, 2, 2, 2].length) (baseStart_6495261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6495261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6495261 prefixEnd_6495261 := by exact prefixLift 6495261
  have htrace : WordTrace (prefixWord ++ tailWord_6495261) baseStart_6495261 baseEnd_6495261 := by
    simpa [prefixWord, tailWord_6495261, baseEnd_6495261] using wordTrace_append hprefix tailTrace_6495261
  have hstable : (prefixWord ++ tailWord_6495261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6495261).length < 2 ^ (prefixWord ++ tailWord_6495261).sum := by decide
  have hdescent : baseEnd_6495261 < baseStart_6495261 := by decide
  rcases family_descends (prefixWord ++ tailWord_6495261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6495320 : List Nat := [2, 1, 2, 2, 1, 3, 3, 2, 2, 2, 3]
def baseStart_6495320 : Nat := 118140960795 + 6495320 * 2 ^ 59
def prefixEnd_6495320 : Nat := 4983230072969 + 3 ^ 40 * 6495320 * 2
def baseEnd_6495320 : Nat := 3335221164761632264328573

theorem tailTrace_6495320 : CollatzResearch.WordTrace tailWord_6495320 prefixEnd_6495320 3335221164761632264328573 := by
  unfold tailWord_6495320
  simp only [CollatzResearch.WordTrace]
  refine ⟨118451891414286213592121707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157935855219048284789495609 118451891414286213592121707)
  ·
    refine ⟨177677837121429320388182561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118451891414286213592121707 177677837121429320388182561)
    ·
      refine ⟨133258377841071990291136921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177677837121429320388182561 133258377841071990291136921)
      ·
        refine ⟨99943783380803992718352691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133258377841071990291136921 99943783380803992718352691)
        ·
          refine ⟨149915675071205989077529037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99943783380803992718352691 149915675071205989077529037)
          ·
            refine ⟨56218378151702245904073389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 149915675071205989077529037 56218378151702245904073389)
            ·
              refine ⟨21081891806888342214027521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56218378151702245904073389 21081891806888342214027521)
              ·
                refine ⟨15811418855166256660520641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21081891806888342214027521 15811418855166256660520641)
                ·
                  refine ⟨11858564141374692495390481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15811418855166256660520641 11858564141374692495390481)
                  ·
                    refine ⟨8893923106031019371542861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11858564141374692495390481 8893923106031019371542861)
                    ·
                      refine ⟨3335221164761632264328573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8893923106031019371542861 3335221164761632264328573)
                      ·
                        rfl

theorem cell23_6495320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 2, 2, 2, 3].length) (baseStart_6495320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6495320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6495320 prefixEnd_6495320 := by exact prefixLift 6495320
  have htrace : WordTrace (prefixWord ++ tailWord_6495320) baseStart_6495320 baseEnd_6495320 := by
    simpa [prefixWord, tailWord_6495320, baseEnd_6495320] using wordTrace_append hprefix tailTrace_6495320
  have hstable : (prefixWord ++ tailWord_6495320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6495320).length < 2 ^ (prefixWord ++ tailWord_6495320).sum := by decide
  have hdescent : baseEnd_6495320 < baseStart_6495320 := by decide
  rcases family_descends (prefixWord ++ tailWord_6495320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6495360 : List Nat := [2, 1, 1, 2, 1, 3, 2, 3, 1, 5, 2]
def baseStart_6495360 : Nat := 118140960795 + 6495360 * 2 ^ 59
def prefixEnd_6495360 : Nat := 4983230072969 + 3 ^ 40 * 6495360 * 2
def baseEnd_6495360 : Nat := 3335241703987812107828389

theorem tailTrace_6495360 : CollatzResearch.WordTrace tailWord_6495360 prefixEnd_6495360 3335241703987812107828389 := by
  unfold tailWord_6495360
  simp only [CollatzResearch.WordTrace]
  refine ⟨118452620874213757007849767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157936827832285009343799689 118452620874213757007849767)
  ·
    refine ⟨177678931311320635511774651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118452620874213757007849767 177678931311320635511774651)
    ·
      refine ⟨266518396966980953267661977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177678931311320635511774651 266518396966980953267661977)
      ·
        refine ⟨199888797725235714950746483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 266518396966980953267661977 199888797725235714950746483)
        ·
          refine ⟨299833196587853572426119725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199888797725235714950746483 299833196587853572426119725)
          ·
            refine ⟨112437448720445089659794897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 299833196587853572426119725 112437448720445089659794897)
            ·
              refine ⟨84328086540333817244846173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112437448720445089659794897 84328086540333817244846173)
              ·
                refine ⟨31623032452625181466817315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84328086540333817244846173 31623032452625181466817315)
                ·
                  refine ⟨47434548678937772200225973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31623032452625181466817315 47434548678937772200225973)
                  ·
                    refine ⟨4446988938650416143771185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47434548678937772200225973 4446988938650416143771185)
                    ·
                      refine ⟨3335241703987812107828389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4446988938650416143771185 3335241703987812107828389)
                      ·
                        rfl

theorem cell23_6495360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 3, 1, 5, 2].length) (baseStart_6495360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6495360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6495360 prefixEnd_6495360 := by exact prefixLift 6495360
  have htrace : WordTrace (prefixWord ++ tailWord_6495360) baseStart_6495360 baseEnd_6495360 := by
    simpa [prefixWord, tailWord_6495360, baseEnd_6495360] using wordTrace_append hprefix tailTrace_6495360
  have hstable : (prefixWord ++ tailWord_6495360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6495360).length < 2 ^ (prefixWord ++ tailWord_6495360).sum := by decide
  have hdescent : baseEnd_6495360 < baseStart_6495360 := by decide
  rcases family_descends (prefixWord ++ tailWord_6495360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6495407 : List Nat := [1, 1, 2, 1, 2, 3, 3, 1, 5, 2, 2]
def baseStart_6495407 : Nat := 118140960795 + 6495407 * 2 ^ 59
def prefixEnd_6495407 : Nat := 4983230072969 + 3 ^ 40 * 6495407 * 2
def baseEnd_6495407 : Nat := 3335265837578573423940673

theorem tailTrace_6495407 : CollatzResearch.WordTrace tailWord_6495407 prefixEnd_6495407 3335265837578573423940673 := by
  unfold tailWord_6495407
  simp only [CollatzResearch.WordTrace]
  refine ⟨236906955979257241042660475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157937970652838160695106983 236906955979257241042660475)
  ·
    refine ⟨355360433968885861563990713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236906955979257241042660475 355360433968885861563990713)
    ·
      refine ⟨266520325476664396172993035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 355360433968885861563990713 266520325476664396172993035)
      ·
        refine ⟨399780488214996594259489553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266520325476664396172993035 399780488214996594259489553)
        ·
          refine ⟨299835366161247445694617165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 399780488214996594259489553 299835366161247445694617165)
          ·
            refine ⟨112438262310467792135481437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 299835366161247445694617165 112438262310467792135481437)
            ·
              refine ⟨42164348366425422050805539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112438262310467792135481437 42164348366425422050805539)
              ·
                refine ⟨63246522549638133076208309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42164348366425422050805539 63246522549638133076208309)
                ·
                  refine ⟨5929361489028574975894529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 63246522549638133076208309 5929361489028574975894529)
                  ·
                    refine ⟨4447021116771431231920897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5929361489028574975894529 4447021116771431231920897)
                    ·
                      refine ⟨3335265837578573423940673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4447021116771431231920897 3335265837578573423940673)
                      ·
                        rfl

theorem cell23_6495407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 1, 5, 2, 2].length) (baseStart_6495407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6495407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6495407 prefixEnd_6495407 := by exact prefixLift 6495407
  have htrace : WordTrace (prefixWord ++ tailWord_6495407) baseStart_6495407 baseEnd_6495407 := by
    simpa [prefixWord, tailWord_6495407, baseEnd_6495407] using wordTrace_append hprefix tailTrace_6495407
  have hstable : (prefixWord ++ tailWord_6495407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6495407).length < 2 ^ (prefixWord ++ tailWord_6495407).sum := by decide
  have hdescent : baseEnd_6495407 < baseStart_6495407 := by decide
  rcases family_descends (prefixWord ++ tailWord_6495407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6495434 : List Nat := [3, 1, 2, 1, 3, 4, 1, 2, 2, 4]
def baseStart_6495434 : Nat := 118140960795 + 6495434 * 2 ^ 59
def prefixEnd_6495434 : Nat := 4983230072969 + 3 ^ 40 * 6495434 * 2
def baseEnd_6495434 : Nat := 1111759900518748272767683

theorem tailTrace_6495434 : CollatzResearch.WordTrace tailWord_6495434 prefixEnd_6495434 1111759900518748272767683 := by
  unfold tailWord_6495434
  simp only [CollatzResearch.WordTrace]
  refine ⟨59226985187539856163473339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157938627166772949769262237 59226985187539856163473339)
  ·
    refine ⟨88840477781309784245210009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59226985187539856163473339 88840477781309784245210009)
    ·
      refine ⟨66630358335982338183907507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88840477781309784245210009 66630358335982338183907507)
      ·
        refine ⟨99945537503973507275861261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66630358335982338183907507 99945537503973507275861261)
        ·
          refine ⟨37479576563990065228447973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99945537503973507275861261 37479576563990065228447973)
          ·
            refine ⟨7027420605748137230333995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37479576563990065228447973 7027420605748137230333995)
            ·
              refine ⟨10541130908622205845500993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7027420605748137230333995 10541130908622205845500993)
              ·
                refine ⟨7905848181466654384125745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10541130908622205845500993 7905848181466654384125745)
                ·
                  refine ⟨5929386136099990788094309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7905848181466654384125745 5929386136099990788094309)
                  ·
                    refine ⟨1111759900518748272767683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5929386136099990788094309 1111759900518748272767683)
                    ·
                      rfl

theorem cell23_6495434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 1, 2, 2, 4].length) (baseStart_6495434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6495434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6495434 prefixEnd_6495434 := by exact prefixLift 6495434
  have htrace : WordTrace (prefixWord ++ tailWord_6495434) baseStart_6495434 baseEnd_6495434 := by
    simpa [prefixWord, tailWord_6495434, baseEnd_6495434] using wordTrace_append hprefix tailTrace_6495434
  have hstable : (prefixWord ++ tailWord_6495434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6495434).length < 2 ^ (prefixWord ++ tailWord_6495434).sum := by decide
  have hdescent : baseEnd_6495434 < baseStart_6495434 := by decide
  rcases family_descends (prefixWord ++ tailWord_6495434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6495444 : List Nat := [2, 4, 1, 4, 1, 1, 1, 2, 1, 1, 5]
def baseStart_6495444 : Nat := 118140960795 + 6495444 * 2 ^ 59
def prefixEnd_6495444 : Nat := 4983230072969 + 3 ^ 40 * 6495444 * 2
def baseEnd_6495444 : Nat := 3335284836362789779178003

theorem tailTrace_6495444 : CollatzResearch.WordTrace tailWord_6495444 prefixEnd_6495444 3335284836362789779178003 := by
  unfold tailWord_6495444
  simp only [CollatzResearch.WordTrace]
  refine ⟨118454152740061598180878693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157938870320082130907838257 118454152740061598180878693)
  ·
    refine ⟨22210153638761549658914755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 118454152740061598180878693 22210153638761549658914755)
    ·
      refine ⟨33315230458142324488372133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22210153638761549658914755 33315230458142324488372133)
      ·
        refine ⟨6246605710901685841569775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33315230458142324488372133 6246605710901685841569775)
        ·
          refine ⟨9369908566352528762354663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6246605710901685841569775 9369908566352528762354663)
          ·
            refine ⟨14054862849528793143531995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9369908566352528762354663 14054862849528793143531995)
            ·
              refine ⟨21082294274293189715297993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14054862849528793143531995 21082294274293189715297993)
              ·
                refine ⟨15811720705719892286473495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21082294274293189715297993 15811720705719892286473495)
                ·
                  refine ⟨23717581058579838429710243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15811720705719892286473495 23717581058579838429710243)
                  ·
                    refine ⟨35576371587869757644565365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23717581058579838429710243 35576371587869757644565365)
                    ·
                      refine ⟨3335284836362789779178003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35576371587869757644565365 3335284836362789779178003)
                      ·
                        rfl

theorem cell23_6495444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_6495444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6495444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6495444 prefixEnd_6495444 := by exact prefixLift 6495444
  have htrace : WordTrace (prefixWord ++ tailWord_6495444) baseStart_6495444 baseEnd_6495444 := by
    simpa [prefixWord, tailWord_6495444, baseEnd_6495444] using wordTrace_append hprefix tailTrace_6495444
  have hstable : (prefixWord ++ tailWord_6495444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6495444).length < 2 ^ (prefixWord ++ tailWord_6495444).sum := by decide
  have hdescent : baseEnd_6495444 < baseStart_6495444 := by decide
  rcases family_descends (prefixWord ++ tailWord_6495444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6495457 : List Nat := [1, 2, 3, 1, 3, 2, 3, 1, 1, 3, 3]
def baseStart_6495457 : Nat := 118140960795 + 6495457 * 2 ^ 59
def prefixEnd_6495457 : Nat := 4983230072969 + 3 ^ 40 * 6495457 * 2
def baseEnd_6495457 : Nat := 3335291511611298228315443

theorem tailTrace_6495457 : CollatzResearch.WordTrace tailWord_6495457 prefixEnd_6495457 3335291511611298228315443 := by
  unfold tailWord_6495457
  simp only [CollatzResearch.WordTrace]
  refine ⟨236908779629076099581980625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157939186419384066387987083 236908779629076099581980625)
  ·
    refine ⟨177681584721807074686485469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236908779629076099581980625 177681584721807074686485469)
    ·
      refine ⟨66630594270677653007432051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177681584721807074686485469 66630594270677653007432051)
      ·
        refine ⟨99945891406016479511148077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66630594270677653007432051 99945891406016479511148077)
        ·
          refine ⟨37479709277256179816680529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99945891406016479511148077 37479709277256179816680529)
          ·
            refine ⟨28109781957942134862510397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37479709277256179816680529 28109781957942134862510397)
            ·
              refine ⟨10541168234228300573441399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28109781957942134862510397 10541168234228300573441399)
              ·
                refine ⟨15811752351342450860162099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10541168234228300573441399 15811752351342450860162099)
                ·
                  refine ⟨23717628527013676290243149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15811752351342450860162099 23717628527013676290243149)
                  ·
                    refine ⟨8894110697630128608841181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23717628527013676290243149 8894110697630128608841181)
                    ·
                      refine ⟨3335291511611298228315443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8894110697630128608841181 3335291511611298228315443)
                      ·
                        rfl

theorem cell23_6495457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 3, 1, 1, 3, 3].length) (baseStart_6495457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6495457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6495457 prefixEnd_6495457 := by exact prefixLift 6495457
  have htrace : WordTrace (prefixWord ++ tailWord_6495457) baseStart_6495457 baseEnd_6495457 := by
    simpa [prefixWord, tailWord_6495457, baseEnd_6495457] using wordTrace_append hprefix tailTrace_6495457
  have hstable : (prefixWord ++ tailWord_6495457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6495457).length < 2 ^ (prefixWord ++ tailWord_6495457).sum := by decide
  have hdescent : baseEnd_6495457 < baseStart_6495457 := by decide
  rcases family_descends (prefixWord ++ tailWord_6495457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6495470 : List Nat := [4, 1, 2, 1, 1, 1, 3, 1, 2, 2, 5]
def baseStart_6495470 : Nat := 118140960795 + 6495470 * 2 ^ 59
def prefixEnd_6495470 : Nat := 4983230072969 + 3 ^ 40 * 6495470 * 2
def baseEnd_6495470 : Nat := 3335298186859806677452883

theorem tailTrace_6495470 : CollatzResearch.WordTrace tailWord_6495470 prefixEnd_6495470 3335298186859806677452883 := by
  unfold tailWord_6495470
  simp only [CollatzResearch.WordTrace]
  refine ⟨29613656722253625350275483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157939502518686001868135909 29613656722253625350275483)
  ·
    refine ⟨44420485083380438025413225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29613656722253625350275483 44420485083380438025413225)
    ·
      refine ⟨33315363812535328519059919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44420485083380438025413225 33315363812535328519059919)
      ·
        refine ⟨49973045718802992778589879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33315363812535328519059919 49973045718802992778589879)
        ·
          refine ⟨74959568578204489167884819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49973045718802992778589879 74959568578204489167884819)
          ·
            refine ⟨112439352867306733751827229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74959568578204489167884819 112439352867306733751827229)
            ·
              refine ⟨42164757325240025156935211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112439352867306733751827229 42164757325240025156935211)
              ·
                refine ⟨63247135987860037735402817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42164757325240025156935211 63247135987860037735402817)
                ·
                  refine ⟨47435351990895028301552113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63247135987860037735402817 47435351990895028301552113)
                  ·
                    refine ⟨35576513993171271226164085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47435351990895028301552113 35576513993171271226164085)
                    ·
                      refine ⟨3335298186859806677452883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35576513993171271226164085 3335298186859806677452883)
                      ·
                        rfl

theorem cell23_6495470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 1, 2, 2, 5].length) (baseStart_6495470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6495470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6495470 prefixEnd_6495470 := by exact prefixLift 6495470
  have htrace : WordTrace (prefixWord ++ tailWord_6495470) baseStart_6495470 baseEnd_6495470 := by
    simpa [prefixWord, tailWord_6495470, baseEnd_6495470] using wordTrace_append hprefix tailTrace_6495470
  have hstable : (prefixWord ++ tailWord_6495470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6495470).length < 2 ^ (prefixWord ++ tailWord_6495470).sum := by decide
  have hdescent : baseEnd_6495470 < baseStart_6495470 := by decide
  rcases family_descends (prefixWord ++ tailWord_6495470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6495517 : List Nat := [1, 4, 2, 3, 1, 1, 1, 2, 2, 1, 5]
def baseStart_6495517 : Nat := 118140960795 + 6495517 * 2 ^ 59
def prefixEnd_6495517 : Nat := 4983230072969 + 3 ^ 40 * 6495517 * 2
def baseEnd_6495517 : Nat := 3335322320450567993565167

theorem tailTrace_6495517 : CollatzResearch.WordTrace tailWord_6495517 prefixEnd_6495517 3335322320450567993565167 := by
  unfold tailWord_6495517
  simp only [CollatzResearch.WordTrace]
  refine ⟨236910968008858729829164805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157940645339239153219443203 236910968008858729829164805)
  ·
    refine ⟨44420806501661011842968401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 236910968008858729829164805 44420806501661011842968401)
    ·
      refine ⟨33315604876245758882226301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44420806501661011842968401 33315604876245758882226301)
      ·
        refine ⟨12493351828592159580834863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33315604876245758882226301 12493351828592159580834863)
        ·
          refine ⟨18740027742888239371252295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12493351828592159580834863 18740027742888239371252295)
          ·
            refine ⟨28110041614332359056878443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18740027742888239371252295 28110041614332359056878443)
            ·
              refine ⟨42165062421498538585317665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28110041614332359056878443 42165062421498538585317665)
              ·
                refine ⟨31623796816123903938988249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42165062421498538585317665 31623796816123903938988249)
                ·
                  refine ⟨23717847612092927954241187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31623796816123903938988249 23717847612092927954241187)
                  ·
                    refine ⟨35576771418139391931361781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23717847612092927954241187 35576771418139391931361781)
                    ·
                      refine ⟨3335322320450567993565167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35576771418139391931361781 3335322320450567993565167)
                      ·
                        rfl

theorem cell23_6495517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_6495517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6495517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6495517 prefixEnd_6495517 := by exact prefixLift 6495517
  have htrace : WordTrace (prefixWord ++ tailWord_6495517) baseStart_6495517 baseEnd_6495517 := by
    simpa [prefixWord, tailWord_6495517, baseEnd_6495517] using wordTrace_append hprefix tailTrace_6495517
  have hstable : (prefixWord ++ tailWord_6495517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6495517).length < 2 ^ (prefixWord ++ tailWord_6495517).sum := by decide
  have hdescent : baseEnd_6495517 < baseStart_6495517 := by decide
  rcases family_descends (prefixWord ++ tailWord_6495517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6495518 : List Nat := [4, 3, 2, 1, 2, 1, 1, 1, 3, 3, 2]
def baseStart_6495518 : Nat := 118140960795 + 6495518 * 2 ^ 59
def prefixEnd_6495518 : Nat := 4983230072969 + 3 ^ 40 * 6495518 * 2
def baseEnd_6495518 : Nat := 3335322833931222489652663

theorem tailTrace_6495518 : CollatzResearch.WordTrace tailWord_6495518 prefixEnd_6495518 3335322833931222489652663 := by
  unfold tailWord_6495518
  simp only [CollatzResearch.WordTrace]
  refine ⟨29613875560231888374993901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157940669654570071333300805 29613875560231888374993901)
  ·
    refine ⟨11105203335086958140622713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29613875560231888374993901 11105203335086958140622713)
    ·
      refine ⟨8328902501315218605467035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11105203335086958140622713 8328902501315218605467035)
      ·
        refine ⟨12493353751972827908200553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8328902501315218605467035 12493353751972827908200553)
        ·
          refine ⟨9370015313979620931150415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12493353751972827908200553 9370015313979620931150415)
          ·
            refine ⟨14055022970969431396725623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9370015313979620931150415 14055022970969431396725623)
            ·
              refine ⟨21082534456454147095088435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14055022970969431396725623 21082534456454147095088435)
              ·
                refine ⟨31623801684681220642632653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21082534456454147095088435 31623801684681220642632653)
                ·
                  refine ⟨11858925631755457740987245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31623801684681220642632653 11858925631755457740987245)
                  ·
                    refine ⟨4447097111908296652870217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11858925631755457740987245 4447097111908296652870217)
                    ·
                      refine ⟨3335322833931222489652663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4447097111908296652870217 3335322833931222489652663)
                      ·
                        rfl

theorem cell23_6495518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 1, 3, 3, 2].length) (baseStart_6495518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6495518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6495518 prefixEnd_6495518 := by exact prefixLift 6495518
  have htrace : WordTrace (prefixWord ++ tailWord_6495518) baseStart_6495518 baseEnd_6495518 := by
    simpa [prefixWord, tailWord_6495518, baseEnd_6495518] using wordTrace_append hprefix tailTrace_6495518
  have hstable : (prefixWord ++ tailWord_6495518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6495518).length < 2 ^ (prefixWord ++ tailWord_6495518).sum := by decide
  have hdescent : baseEnd_6495518 < baseStart_6495518 := by decide
  rcases family_descends (prefixWord ++ tailWord_6495518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6495584 : List Nat := [2, 1, 1, 3, 4, 3, 1, 1, 2, 5]
def baseStart_6495584 : Nat := 118140960795 + 6495584 * 2 ^ 59
def prefixEnd_6495584 : Nat := 4983230072969 + 3 ^ 40 * 6495584 * 2
def baseEnd_6495584 : Nat := 1111785574551473077142453

theorem tailTrace_6495584 : CollatzResearch.WordTrace tailWord_6495584 prefixEnd_6495584 1111785574551473077142453 := by
  unfold tailWord_6495584
  simp only [CollatzResearch.WordTrace]
  refine ⟨118456705849808000135926903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157942274466410666847902537 118456705849808000135926903)
  ·
    refine ⟨177685058774712000203890355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118456705849808000135926903 177685058774712000203890355)
    ·
      refine ⟨266527588162068000305835533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177685058774712000203890355 266527588162068000305835533)
      ·
        refine ⟨99947845560775500114688325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 266527588162068000305835533 99947845560775500114688325)
        ·
          refine ⟨18740221042645406271504061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 99947845560775500114688325 18740221042645406271504061)
          ·
            refine ⟨7027582890992027351814023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18740221042645406271504061 7027582890992027351814023)
            ·
              refine ⟨10541374336488041027721035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7027582890992027351814023 10541374336488041027721035)
              ·
                refine ⟨15812061504732061541581553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10541374336488041027721035 15812061504732061541581553)
                ·
                  refine ⟨11859046128549046156186165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15812061504732061541581553 11859046128549046156186165)
                  ·
                    refine ⟨1111785574551473077142453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11859046128549046156186165 1111785574551473077142453)
                    ·
                      rfl

theorem cell23_6495584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 1, 1, 2, 5].length) (baseStart_6495584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6495584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6495584 prefixEnd_6495584 := by exact prefixLift 6495584
  have htrace : WordTrace (prefixWord ++ tailWord_6495584) baseStart_6495584 baseEnd_6495584 := by
    simpa [prefixWord, tailWord_6495584, baseEnd_6495584] using wordTrace_append hprefix tailTrace_6495584
  have hstable : (prefixWord ++ tailWord_6495584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6495584).length < 2 ^ (prefixWord ++ tailWord_6495584).sum := by decide
  have hdescent : baseEnd_6495584 < baseStart_6495584 := by decide
  rcases family_descends (prefixWord ++ tailWord_6495584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6495587 : List Nat := [1, 1, 1, 5, 2, 3, 1, 1, 1, 3, 4]
def baseStart_6495587 : Nat := 118140960795 + 6495587 * 2 ^ 59
def prefixEnd_6495587 : Nat := 4983230072969 + 3 ^ 40 * 6495587 * 2
def baseEnd_6495587 : Nat := 3335358264096382719689845

theorem tailTrace_6495587 : CollatzResearch.WordTrace tailWord_6495587 prefixEnd_6495587 3335358264096382719689845 := by
  unfold tailWord_6495587
  simp only [CollatzResearch.WordTrace]
  refine ⟨236913521118605131784213015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157942347412403421189475343 236913521118605131784213015)
  ·
    refine ⟨355370281677907697676319523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236913521118605131784213015 355370281677907697676319523)
    ·
      refine ⟨533055422516861546514479285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 355370281677907697676319523 533055422516861546514479285)
      ·
        refine ⟨49973945860955769985732433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 533055422516861546514479285 49973945860955769985732433)
        ·
          refine ⟨37480459395716827489299325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49973945860955769985732433 37480459395716827489299325)
          ·
            refine ⟨14055172273393810308487247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37480459395716827489299325 14055172273393810308487247)
            ·
              refine ⟨21082758410090715462730871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14055172273393810308487247 21082758410090715462730871)
              ·
                refine ⟨31624137615136073194096307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21082758410090715462730871 31624137615136073194096307)
                ·
                  refine ⟨47436206422704109791144461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31624137615136073194096307 47436206422704109791144461)
                  ·
                    refine ⟨17788577408514041171679173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47436206422704109791144461 17788577408514041171679173)
                    ·
                      refine ⟨3335358264096382719689845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17788577408514041171679173 3335358264096382719689845)
                      ·
                        rfl

theorem cell23_6495587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 1, 1, 3, 4].length) (baseStart_6495587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6495587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6495587 prefixEnd_6495587 := by exact prefixLift 6495587
  have htrace : WordTrace (prefixWord ++ tailWord_6495587) baseStart_6495587 baseEnd_6495587 := by
    simpa [prefixWord, tailWord_6495587, baseEnd_6495587] using wordTrace_append hprefix tailTrace_6495587
  have hstable : (prefixWord ++ tailWord_6495587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6495587).length < 2 ^ (prefixWord ++ tailWord_6495587).sum := by decide
  have hdescent : baseEnd_6495587 < baseStart_6495587 := by decide
  rcases family_descends (prefixWord ++ tailWord_6495587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6495600 : List Nat := [2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 6]
def baseStart_6495600 : Nat := 118140960795 + 6495600 * 2 ^ 59
def prefixEnd_6495600 : Nat := 4983230072969 + 3 ^ 40 * 6495600 * 2
def baseEnd_6495600 : Nat := 3335364939344891168827285

theorem tailTrace_6495600 : CollatzResearch.WordTrace tailWord_6495600 prefixEnd_6495600 3335364939344891168827285 := by
  unfold tailWord_6495600
  simp only [CollatzResearch.WordTrace]
  refine ⟨118456997633779017502218127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157942663511705356669624169 118456997633779017502218127)
  ·
    refine ⟨177685496450668526253327191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118456997633779017502218127 177685496450668526253327191)
    ·
      refine ⟨266528244676002789379990787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177685496450668526253327191 266528244676002789379990787)
      ·
        refine ⟨399792367014004184069986181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266528244676002789379990787 399792367014004184069986181)
        ·
          refine ⟨74961068815125784513122409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 399792367014004184069986181 74961068815125784513122409)
          ·
            refine ⟨56220801611344338384841807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74961068815125784513122409 56220801611344338384841807)
            ·
              refine ⟨84331202417016507577262711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56220801611344338384841807 84331202417016507577262711)
              ·
                refine ⟨126496803625524761365894067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84331202417016507577262711 126496803625524761365894067)
                ·
                  refine ⟨189745205438287142048841101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 126496803625524761365894067 189745205438287142048841101)
                  ·
                    refine ⟨71154452039357678268315413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 189745205438287142048841101 71154452039357678268315413)
                    ·
                      refine ⟨3335364939344891168827285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71154452039357678268315413 3335364939344891168827285)
                      ·
                        rfl

theorem cell23_6495600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 6].length) (baseStart_6495600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6495600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6495600 prefixEnd_6495600 := by exact prefixLift 6495600
  have htrace : WordTrace (prefixWord ++ tailWord_6495600) baseStart_6495600 baseEnd_6495600 := by
    simpa [prefixWord, tailWord_6495600, baseEnd_6495600] using wordTrace_append hprefix tailTrace_6495600
  have hstable : (prefixWord ++ tailWord_6495600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6495600).length < 2 ^ (prefixWord ++ tailWord_6495600).sum := by decide
  have hdescent : baseEnd_6495600 < baseStart_6495600 := by decide
  rcases family_descends (prefixWord ++ tailWord_6495600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6495607 : List Nat := [1, 1, 3, 1, 1, 2, 4, 1, 4, 2, 3]
def baseStart_6495607 : Nat := 118140960795 + 6495607 * 2 ^ 59
def prefixEnd_6495607 : Nat := 4983230072969 + 3 ^ 40 * 6495607 * 2
def baseEnd_6495607 : Nat := 3335368533709472641439753

theorem tailTrace_6495607 : CollatzResearch.WordTrace tailWord_6495607 prefixEnd_6495607 3335368533709472641439753 := by
  unfold tailWord_6495607
  simp only [CollatzResearch.WordTrace]
  refine ⟨236914250578532675199941075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157942833719021783466627383 236914250578532675199941075)
  ·
    refine ⟨355371375867799012799911613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236914250578532675199941075 355371375867799012799911613)
    ·
      refine ⟨133264265950424629799966855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 355371375867799012799911613 133264265950424629799966855)
      ·
        refine ⟨199896398925636944699950283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133264265950424629799966855 199896398925636944699950283)
        ·
          refine ⟨299844598388455417049925425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199896398925636944699950283 299844598388455417049925425)
          ·
            refine ⟨224883448791341562787444069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 299844598388455417049925425 224883448791341562787444069)
            ·
              refine ⟨42165646648376543022645763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 224883448791341562787444069 42165646648376543022645763)
              ·
                refine ⟨63248469972564814533968645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42165646648376543022645763 63248469972564814533968645)
                ·
                  refine ⟨11859088119855902725119121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63248469972564814533968645 11859088119855902725119121)
                  ·
                    refine ⟨8894316089891927043839341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11859088119855902725119121 8894316089891927043839341)
                    ·
                      refine ⟨3335368533709472641439753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8894316089891927043839341 3335368533709472641439753)
                      ·
                        rfl

theorem cell23_6495607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 1, 4, 2, 3].length) (baseStart_6495607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6495607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6495607 prefixEnd_6495607 := by exact prefixLift 6495607
  have htrace : WordTrace (prefixWord ++ tailWord_6495607) baseStart_6495607 baseEnd_6495607 := by
    simpa [prefixWord, tailWord_6495607, baseEnd_6495607] using wordTrace_append hprefix tailTrace_6495607
  have hstable : (prefixWord ++ tailWord_6495607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6495607).length < 2 ^ (prefixWord ++ tailWord_6495607).sum := by decide
  have hdescent : baseEnd_6495607 < baseStart_6495607 := by decide
  rcases family_descends (prefixWord ++ tailWord_6495607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6495610 : List Nat := [3, 1, 1, 1, 1, 1, 2, 5, 8]
def baseStart_6495610 : Nat := 118140960795 + 6495610 * 2 ^ 59
def prefixEnd_6495610 : Nat := 4983230072969 + 3 ^ 40 * 6495610 * 2
def baseEnd_6495610 : Nat := 370596674905715125522471

theorem tailTrace_6495610 : CollatzResearch.WordTrace tailWord_6495610 prefixEnd_6495610 370596674905715125522471 := by
  unfold tailWord_6495610
  simp only [CollatzResearch.WordTrace]
  refine ⟨59228589999380451678075071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157942906665014537808200189 59228589999380451678075071)
  ·
    refine ⟨88842884999070677517112607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59228589999380451678075071 88842884999070677517112607)
    ·
      refine ⟨133264327498606016275668911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88842884999070677517112607 133264327498606016275668911)
      ·
        refine ⟨199896491247909024413503367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133264327498606016275668911 199896491247909024413503367)
        ·
          refine ⟨299844736871863536620255051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199896491247909024413503367 299844736871863536620255051)
          ·
            refine ⟨449767105307795304930382577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 299844736871863536620255051 449767105307795304930382577)
            ·
              refine ⟨337325328980846478697786933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 449767105307795304930382577 337325328980846478697786933)
              ·
                refine ⟨31624249591954357377917525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 337325328980846478697786933 31624249591954357377917525)
                ·
                  refine ⟨370596674905715125522471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31624249591954357377917525 370596674905715125522471)
                  ·
                    rfl

theorem cell23_6495610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 5, 8].length) (baseStart_6495610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6495610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6495610 prefixEnd_6495610 := by exact prefixLift 6495610
  have htrace : WordTrace (prefixWord ++ tailWord_6495610) baseStart_6495610 baseEnd_6495610 := by
    simpa [prefixWord, tailWord_6495610, baseEnd_6495610] using wordTrace_append hprefix tailTrace_6495610
  have hstable : (prefixWord ++ tailWord_6495610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6495610).length < 2 ^ (prefixWord ++ tailWord_6495610).sum := by decide
  have hdescent : baseEnd_6495610 < baseStart_6495610 := by decide
  rcases family_descends (prefixWord ++ tailWord_6495610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6495687 : List Nat := [1, 1, 4, 1, 1, 3, 2, 3, 1, 6]
def baseStart_6495687 : Nat := 118140960795 + 6495687 * 2 ^ 59
def prefixEnd_6495687 : Nat := 4983230072969 + 3 ^ 40 * 6495687 * 2
def baseEnd_6495687 : Nat := 1111803204053944109479795

theorem tailTrace_6495687 : CollatzResearch.WordTrace tailWord_6495687 prefixEnd_6495687 1111803204053944109479795 := by
  unfold tailWord_6495687
  simp only [CollatzResearch.WordTrace]
  refine ⟨236917168418242848862853315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157944778945495232575235543 236917168418242848862853315)
  ·
    refine ⟨355375752627364273294279973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236917168418242848862853315 355375752627364273294279973)
    ·
      refine ⟨66632953617630801242677495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 355375752627364273294279973 66632953617630801242677495)
      ·
        refine ⟨99949430426446201864016243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66632953617630801242677495 99949430426446201864016243)
        ·
          refine ⟨149924145639669302796024365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99949430426446201864016243 149924145639669302796024365)
          ·
            refine ⟨56221554614875988548509137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 149924145639669302796024365 56221554614875988548509137)
            ·
              refine ⟨42166165961156991411381853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56221554614875988548509137 42166165961156991411381853)
              ·
                refine ⟨15812312235433871779268195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42166165961156991411381853 15812312235433871779268195)
                ·
                  refine ⟨23718468353150807668902293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15812312235433871779268195 23718468353150807668902293)
                  ·
                    refine ⟨1111803204053944109479795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23718468353150807668902293 1111803204053944109479795)
                    ·
                      rfl

theorem cell23_6495687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 3, 1, 6].length) (baseStart_6495687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6495687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6495687 prefixEnd_6495687 := by exact prefixLift 6495687
  have htrace : WordTrace (prefixWord ++ tailWord_6495687) baseStart_6495687 baseEnd_6495687 := by
    simpa [prefixWord, tailWord_6495687, baseEnd_6495687] using wordTrace_append hprefix tailTrace_6495687
  have hstable : (prefixWord ++ tailWord_6495687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6495687).length < 2 ^ (prefixWord ++ tailWord_6495687).sum := by decide
  have hdescent : baseEnd_6495687 < baseStart_6495687 := by decide
  rcases family_descends (prefixWord ++ tailWord_6495687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6495694 : List Nat := [4, 1, 1, 1, 2, 1, 2, 1, 2, 6, 2]
def baseStart_6495694 : Nat := 118140960795 + 6495694 * 2 ^ 59
def prefixEnd_6495694 : Nat := 4983230072969 + 3 ^ 40 * 6495694 * 2
def baseEnd_6495694 : Nat := 3335413206526413801051853

theorem tailTrace_6495694 : CollatzResearch.WordTrace tailWord_6495694 prefixEnd_6495694 3335413206526413801051853 := by
  unfold tailWord_6495694
  simp only [CollatzResearch.WordTrace]
  refine ⟨29614677966152186132294767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157944949152811659372238757 29614677966152186132294767)
  ·
    refine ⟨44422016949228279198442151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29614677966152186132294767 44422016949228279198442151)
    ·
      refine ⟨66633025423842418797663227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44422016949228279198442151 66633025423842418797663227)
      ·
        refine ⟨99949538135763628196494841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66633025423842418797663227 99949538135763628196494841)
        ·
          refine ⟨74962153601822721147371131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99949538135763628196494841 74962153601822721147371131)
          ·
            refine ⟨112443230402734081721056697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74962153601822721147371131 112443230402734081721056697)
            ·
              refine ⟨84332422802050561290792523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112443230402734081721056697 84332422802050561290792523)
              ·
                refine ⟨126498634203075841936188785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84332422802050561290792523 126498634203075841936188785)
                ·
                  refine ⟨94873975652306881452141589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 126498634203075841936188785 94873975652306881452141589)
                  ·
                    refine ⟨4447217608701885068069137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 94873975652306881452141589 4447217608701885068069137)
                    ·
                      refine ⟨3335413206526413801051853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4447217608701885068069137 3335413206526413801051853)
                      ·
                        rfl

theorem cell23_6495694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 1, 2, 6, 2].length) (baseStart_6495694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6495694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6495694 prefixEnd_6495694 := by exact prefixLift 6495694
  have htrace : WordTrace (prefixWord ++ tailWord_6495694) baseStart_6495694 baseEnd_6495694 := by
    simpa [prefixWord, tailWord_6495694, baseEnd_6495694] using wordTrace_append hprefix tailTrace_6495694
  have hstable : (prefixWord ++ tailWord_6495694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6495694).length < 2 ^ (prefixWord ++ tailWord_6495694).sum := by decide
  have hdescent : baseEnd_6495694 < baseStart_6495694 := by decide
  rcases family_descends (prefixWord ++ tailWord_6495694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6495711 : List Nat := [1, 1, 2, 3, 3, 1, 5, 1, 1, 1, 4]
def baseStart_6495711 : Nat := 118140960795 + 6495711 * 2 ^ 59
def prefixEnd_6495711 : Nat := 4983230072969 + 3 ^ 40 * 6495711 * 2
def baseEnd_6495711 : Nat := 3335421935697540234539275

theorem tailTrace_6495711 : CollatzResearch.WordTrace tailWord_6495711 prefixEnd_6495711 3335421935697540234539275 := by
  unfold tailWord_6495711
  simp only [CollatzResearch.WordTrace]
  refine ⟨236918043770155900961726987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157945362513437267307817991 236918043770155900961726987)
  ·
    refine ⟨355377065655233851442590481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236918043770155900961726987 355377065655233851442590481)
    ·
      refine ⟨266532799241425388581942861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 355377065655233851442590481 266532799241425388581942861)
      ·
        refine ⟨99949799715534520718228573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 266532799241425388581942861 99949799715534520718228573)
        ·
          refine ⟨37481174893325445269335715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99949799715534520718228573 37481174893325445269335715)
          ·
            refine ⟨56221762339988167904003573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37481174893325445269335715 56221762339988167904003573)
            ·
              refine ⟨5270790219373890741000335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56221762339988167904003573 5270790219373890741000335)
              ·
                refine ⟨7906185329060836111500503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5270790219373890741000335 7906185329060836111500503)
                ·
                  refine ⟨11859277993591254167250755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7906185329060836111500503 11859277993591254167250755)
                  ·
                    refine ⟨17788916990386881250876133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11859277993591254167250755 17788916990386881250876133)
                    ·
                      refine ⟨3335421935697540234539275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17788916990386881250876133 3335421935697540234539275)
                      ·
                        rfl

theorem cell23_6495711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 5, 1, 1, 1, 4].length) (baseStart_6495711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6495711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6495711 prefixEnd_6495711 := by exact prefixLift 6495711
  have htrace : WordTrace (prefixWord ++ tailWord_6495711) baseStart_6495711 baseEnd_6495711 := by
    simpa [prefixWord, tailWord_6495711, baseEnd_6495711] using wordTrace_append hprefix tailTrace_6495711
  have hstable : (prefixWord ++ tailWord_6495711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6495711).length < 2 ^ (prefixWord ++ tailWord_6495711).sum := by decide
  have hdescent : baseEnd_6495711 < baseStart_6495711 := by decide
  rcases family_descends (prefixWord ++ tailWord_6495711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6495717 : List Nat := [1, 3, 1, 5, 1, 12]
def baseStart_6495717 : Nat := 118140960795 + 6495717 * 2 ^ 59
def prefixEnd_6495717 : Nat := 4983230072969 + 3 ^ 40 * 6495717 * 2
def baseEnd_6495717 : Nat := 13726028874820852720429

theorem tailTrace_6495717 : CollatzResearch.WordTrace tailWord_6495717 prefixEnd_6495717 13726028874820852720429 := by
  unfold tailWord_6495717
  simp only [CollatzResearch.WordTrace]
  refine ⟨236918262608134163986445405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157945508405422775990963603 236918262608134163986445405)
  ·
    refine ⟨88844348478050311494917027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 236918262608134163986445405 88844348478050311494917027)
    ·
      refine ⟨133266522717075467242375541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88844348478050311494917027 133266522717075467242375541)
      ·
        refine ⟨12493736504725825053972707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 133266522717075467242375541 12493736504725825053972707)
        ·
          refine ⟨18740604757088737580959061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12493736504725825053972707 18740604757088737580959061)
          ·
            refine ⟨13726028874820852720429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 18740604757088737580959061 13726028874820852720429)
            ·
              rfl

theorem cell23_6495717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 12].length) (baseStart_6495717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6495717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6495717 prefixEnd_6495717 := by exact prefixLift 6495717
  have htrace : WordTrace (prefixWord ++ tailWord_6495717) baseStart_6495717 baseEnd_6495717 := by
    simpa [prefixWord, tailWord_6495717, baseEnd_6495717] using wordTrace_append hprefix tailTrace_6495717
  have hstable : (prefixWord ++ tailWord_6495717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6495717).length < 2 ^ (prefixWord ++ tailWord_6495717).sum := by decide
  have hdescent : baseEnd_6495717 < baseStart_6495717 := by decide
  rcases family_descends (prefixWord ++ tailWord_6495717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6495722 : List Nat := [3, 1, 3, 1, 4, 2, 2, 2, 1, 1, 3]
def baseStart_6495722 : Nat := 118140960795 + 6495722 * 2 ^ 59
def prefixEnd_6495722 : Nat := 4983230072969 + 3 ^ 40 * 6495722 * 2
def baseEnd_6495722 : Nat := 3335427583984739691501725

theorem tailTrace_6495722 : CollatzResearch.WordTrace tailWord_6495722 prefixEnd_6495722 3335427583984739691501725 := by
  unfold tailWord_6495722
  simp only [CollatzResearch.WordTrace]
  refine ⟨59229611243279012460094355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157945629982077366560251613 59229611243279012460094355)
  ·
    refine ⟨88844416864918518690141533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59229611243279012460094355 88844416864918518690141533)
    ·
      refine ⟨33316656324344444508803075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88844416864918518690141533 33316656324344444508803075)
      ·
        refine ⟨49974984486516666763204613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33316656324344444508803075 49974984486516666763204613)
        ·
          refine ⟨9370309591221875018100865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49974984486516666763204613 9370309591221875018100865)
          ·
            refine ⟨7027732193416406263575649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9370309591221875018100865 7027732193416406263575649)
            ·
              refine ⟨5270799145062304697681737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7027732193416406263575649 5270799145062304697681737)
              ·
                refine ⟨3953099358796728523261303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5270799145062304697681737 3953099358796728523261303)
                ·
                  refine ⟨5929649038195092784891955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3953099358796728523261303 5929649038195092784891955)
                  ·
                    refine ⟨8894473557292639177337933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5929649038195092784891955 8894473557292639177337933)
                    ·
                      refine ⟨3335427583984739691501725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8894473557292639177337933 3335427583984739691501725)
                      ·
                        rfl

theorem cell23_6495722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 2, 2, 1, 1, 3].length) (baseStart_6495722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6495722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6495722 prefixEnd_6495722 := by exact prefixLift 6495722
  have htrace : WordTrace (prefixWord ++ tailWord_6495722) baseStart_6495722 baseEnd_6495722 := by
    simpa [prefixWord, tailWord_6495722, baseEnd_6495722] using wordTrace_append hprefix tailTrace_6495722
  have hstable : (prefixWord ++ tailWord_6495722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6495722).length < 2 ^ (prefixWord ++ tailWord_6495722).sum := by decide
  have hdescent : baseEnd_6495722 < baseStart_6495722 := by decide
  rcases family_descends (prefixWord ++ tailWord_6495722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6495734 : List Nat := [5, 1, 1, 1, 2, 2, 3, 8]
def baseStart_6495734 : Nat := 118140960795 + 6495734 * 2 ^ 59
def prefixEnd_6495734 : Nat := 4983230072969 + 3 ^ 40 * 6495734 * 2
def baseEnd_6495734 : Nat := 123534583176021986835247

theorem tailTrace_6495734 : CollatzResearch.WordTrace tailWord_6495734 prefixEnd_6495734 123534583176021986835247 := by
  unfold tailWord_6495734
  simp only [CollatzResearch.WordTrace]
  refine ⟨14807430165567035993113391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 157945921766048383926542837 14807430165567035993113391)
  ·
    refine ⟨22211145248350553989670087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14807430165567035993113391 22211145248350553989670087)
    ·
      refine ⟨33316717872525830984505131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22211145248350553989670087 33316717872525830984505131)
      ·
        refine ⟨49975076808788746476757697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33316717872525830984505131 49975076808788746476757697)
        ·
          refine ⟨37481307606591559857568273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49975076808788746476757697 37481307606591559857568273)
          ·
            refine ⟨28110980704943669893176205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37481307606591559857568273 28110980704943669893176205)
            ·
              refine ⟨10541617764353876209941077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28110980704943669893176205 10541617764353876209941077)
              ·
                refine ⟨123534583176021986835247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10541617764353876209941077 123534583176021986835247)
                ·
                  rfl

theorem cell23_6495734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 3, 8].length) (baseStart_6495734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6495734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6495734 prefixEnd_6495734 := by exact prefixLift 6495734
  have htrace : WordTrace (prefixWord ++ tailWord_6495734) baseStart_6495734 baseEnd_6495734 := by
    simpa [prefixWord, tailWord_6495734, baseEnd_6495734] using wordTrace_append hprefix tailTrace_6495734
  have hstable : (prefixWord ++ tailWord_6495734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6495734).length < 2 ^ (prefixWord ++ tailWord_6495734).sum := by decide
  have hdescent : baseEnd_6495734 < baseStart_6495734 := by decide
  rcases family_descends (prefixWord ++ tailWord_6495734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6495778 : List Nat := [3, 3, 1, 1, 1, 1, 5, 2, 2, 1, 3]
def baseStart_6495778 : Nat := 118140960795 + 6495778 * 2 ^ 59
def prefixEnd_6495778 : Nat := 4983230072969 + 3 ^ 40 * 6495778 * 2
def baseEnd_6495778 : Nat := 3335456338901391472401467

theorem tailTrace_6495778 : CollatzResearch.WordTrace tailWord_6495778 prefixEnd_6495778 3335456338901391472401467 := by
  unfold tailWord_6495778
  simp only [CollatzResearch.WordTrace]
  refine ⟨59230121865228292851103997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157946991640608780936277325 59230121865228292851103997)
  ·
    refine ⟨22211295699460609819163999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59230121865228292851103997 22211295699460609819163999)
    ·
      refine ⟨33316943549190914728745999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22211295699460609819163999 33316943549190914728745999)
      ·
        refine ⟨49975415323786372093118999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33316943549190914728745999 49975415323786372093118999)
        ·
          refine ⟨74963122985679558139678499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49975415323786372093118999 74963122985679558139678499)
          ·
            refine ⟨112444684478519337209517749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74963122985679558139678499 112444684478519337209517749)
            ·
              refine ⟨10541689169861187863392289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 112444684478519337209517749 10541689169861187863392289)
              ·
                refine ⟨7906266877395890897544217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10541689169861187863392289 7906266877395890897544217)
                ·
                  refine ⟨5929700158046918173158163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7906266877395890897544217 5929700158046918173158163)
                  ·
                    refine ⟨8894550237070377259737245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5929700158046918173158163 8894550237070377259737245)
                    ·
                      refine ⟨3335456338901391472401467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8894550237070377259737245 3335456338901391472401467)
                      ·
                        rfl

theorem cell23_6495778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 5, 2, 2, 1, 3].length) (baseStart_6495778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6495778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6495778 prefixEnd_6495778 := by exact prefixLift 6495778
  have htrace : WordTrace (prefixWord ++ tailWord_6495778) baseStart_6495778 baseEnd_6495778 := by
    simpa [prefixWord, tailWord_6495778, baseEnd_6495778] using wordTrace_append hprefix tailTrace_6495778
  have hstable : (prefixWord ++ tailWord_6495778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6495778).length < 2 ^ (prefixWord ++ tailWord_6495778).sum := by decide
  have hdescent : baseEnd_6495778 < baseStart_6495778 := by decide
  rcases family_descends (prefixWord ++ tailWord_6495778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6495787 : List Nat := [1, 1, 1, 1, 2, 1, 3, 1, 6, 1, 5]
def baseStart_6495787 : Nat := 118140960795 + 6495787 * 2 ^ 59
def prefixEnd_6495787 : Nat := 4983230072969 + 3 ^ 40 * 6495787 * 2
def baseEnd_6495787 : Nat := 3335460960227281937188925

theorem tailTrace_6495787 : CollatzResearch.WordTrace tailWord_6495787 prefixEnd_6495787 3335460960227281937188925 := by
  unfold tailWord_6495787
  simp only [CollatzResearch.WordTrace]
  refine ⟨236920815717880565941493615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157947210478587043960995743 236920815717880565941493615)
  ·
    refine ⟨355381223576820848912240423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236920815717880565941493615 355381223576820848912240423)
    ·
      refine ⟨533071835365231273368360635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 355381223576820848912240423 533071835365231273368360635)
      ·
        refine ⟨799607753047846910052540953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 533071835365231273368360635 799607753047846910052540953)
        ·
          refine ⟨599705814785885182539405715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 799607753047846910052540953 599705814785885182539405715)
          ·
            refine ⟨899558722178827773809108573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 599705814785885182539405715 899558722178827773809108573)
            ·
              refine ⟨337334520817060415178415715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 899558722178827773809108573 337334520817060415178415715)
              ·
                refine ⟨506001781225590622767623573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 337334520817060415178415715 506001781225590622767623573)
                ·
                  refine ⟨23718833494949560442232355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 506001781225590622767623573 23718833494949560442232355)
                  ·
                    refine ⟨35578250242424340663348533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23718833494949560442232355 35578250242424340663348533)
                    ·
                      refine ⟨3335460960227281937188925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35578250242424340663348533 3335460960227281937188925)
                      ·
                        rfl

theorem cell23_6495787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 6, 1, 5].length) (baseStart_6495787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6495787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6495787 prefixEnd_6495787 := by exact prefixLift 6495787
  have htrace : WordTrace (prefixWord ++ tailWord_6495787) baseStart_6495787 baseEnd_6495787 := by
    simpa [prefixWord, tailWord_6495787, baseEnd_6495787] using wordTrace_append hprefix tailTrace_6495787
  have hstable : (prefixWord ++ tailWord_6495787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6495787).length < 2 ^ (prefixWord ++ tailWord_6495787).sum := by decide
  have hdescent : baseEnd_6495787 < baseStart_6495787 := by decide
  rcases family_descends (prefixWord ++ tailWord_6495787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6495805 : List Nat := [1, 4, 1, 3, 3, 1, 2, 2, 1, 3, 2]
def baseStart_6495805 : Nat := 118140960795 + 6495805 * 2 ^ 59
def prefixEnd_6495805 : Nat := 4983230072969 + 3 ^ 40 * 6495805 * 2
def baseEnd_6495805 : Nat := 3335470202879062866763843

theorem tailTrace_6495805 : CollatzResearch.WordTrace tailWord_6495805 prefixEnd_6495805 3335470202879062866763843 := by
  unfold tailWord_6495805
  simp only [CollatzResearch.WordTrace]
  refine ⟨236921472231815355015648869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157947648154543570010432579 236921472231815355015648869)
  ·
    refine ⟨44422776043465379065434163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 236921472231815355015648869 44422776043465379065434163)
    ·
      refine ⟨66634164065198068598151245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44422776043465379065434163 66634164065198068598151245)
      ·
        refine ⟨24987811524449275724306717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66634164065198068598151245 24987811524449275724306717)
        ·
          refine ⟨9370429321668478396615019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24987811524449275724306717 9370429321668478396615019)
          ·
            refine ⟨14055643982502717594922529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9370429321668478396615019 14055643982502717594922529)
            ·
              refine ⟨10541732986877038196191897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14055643982502717594922529 10541732986877038196191897)
              ·
                refine ⟨7906299740157778647143923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10541732986877038196191897 7906299740157778647143923)
                ·
                  refine ⟨11859449610236667970715885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7906299740157778647143923 11859449610236667970715885)
                  ·
                    refine ⟨4447293603838750489018457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11859449610236667970715885 4447293603838750489018457)
                    ·
                      refine ⟨3335470202879062866763843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4447293603838750489018457 3335470202879062866763843)
                      ·
                        rfl

theorem cell23_6495805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 2, 2, 1, 3, 2].length) (baseStart_6495805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6495805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6495805 prefixEnd_6495805 := by exact prefixLift 6495805
  have htrace : WordTrace (prefixWord ++ tailWord_6495805) baseStart_6495805 baseEnd_6495805 := by
    simpa [prefixWord, tailWord_6495805, baseEnd_6495805] using wordTrace_append hprefix tailTrace_6495805
  have hstable : (prefixWord ++ tailWord_6495805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6495805).length < 2 ^ (prefixWord ++ tailWord_6495805).sum := by decide
  have hdescent : baseEnd_6495805 < baseStart_6495805 := by decide
  rcases family_descends (prefixWord ++ tailWord_6495805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6495834 : List Nat := [3, 1, 1, 2, 1, 1, 1, 3, 4, 3, 3]
def baseStart_6495834 : Nat := 118140960795 + 6495834 * 2 ^ 59
def prefixEnd_6495834 : Nat := 4983230072969 + 3 ^ 40 * 6495834 * 2
def baseEnd_6495834 : Nat := 3335485093818043253301209

theorem tailTrace_6495834 : CollatzResearch.WordTrace tailWord_6495834 prefixEnd_6495834 3335485093818043253301209 := by
  unfold tailWord_6495834
  simp only [CollatzResearch.WordTrace]
  refine ⟨59230632487177573242113639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157948353299140195312303037 59230632487177573242113639)
  ·
    refine ⟨88845948730766359863170459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59230632487177573242113639 88845948730766359863170459)
    ·
      refine ⟨133268923096149539794755689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88845948730766359863170459 133268923096149539794755689)
      ·
        refine ⟨99951692322112154846066767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133268923096149539794755689 99951692322112154846066767)
        ·
          refine ⟨149927538483168232269100151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99951692322112154846066767 149927538483168232269100151)
          ·
            refine ⟨224891307724752348403650227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149927538483168232269100151 224891307724752348403650227)
            ·
              refine ⟨337336961587128522605475341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 224891307724752348403650227 337336961587128522605475341)
              ·
                refine ⟨126501360595173195977053253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 337336961587128522605475341 126501360595173195977053253)
                ·
                  refine ⟨23719005111594974245697485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 126501360595173195977053253 23719005111594974245697485)
                  ·
                    refine ⟨8894626916848115342136557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23719005111594974245697485 8894626916848115342136557)
                    ·
                      refine ⟨3335485093818043253301209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8894626916848115342136557 3335485093818043253301209)
                      ·
                        rfl

theorem cell23_6495834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 3, 4, 3, 3].length) (baseStart_6495834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6495834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6495834 prefixEnd_6495834 := by exact prefixLift 6495834
  have htrace : WordTrace (prefixWord ++ tailWord_6495834) baseStart_6495834 baseEnd_6495834 := by
    simpa [prefixWord, tailWord_6495834, baseEnd_6495834] using wordTrace_append hprefix tailTrace_6495834
  have hstable : (prefixWord ++ tailWord_6495834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6495834).length < 2 ^ (prefixWord ++ tailWord_6495834).sum := by decide
  have hdescent : baseEnd_6495834 < baseStart_6495834 := by decide
  rcases family_descends (prefixWord ++ tailWord_6495834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6495892 : List Nat := [2, 4, 2, 2, 2, 2, 2, 2, 5]
def baseStart_6495892 : Nat := 118140960795 + 6495892 * 2 ^ 59
def prefixEnd_6495892 : Nat := 4983230072969 + 3 ^ 40 * 6495892 * 2
def baseEnd_6495892 : Nat := 370612763966222669597327

theorem tailTrace_6495892 : CollatzResearch.WordTrace tailWord_6495892 prefixEnd_6495892 370612763966222669597327 := by
  unfold tailWord_6495892
  simp only [CollatzResearch.WordTrace]
  refine ⟨118462322691250084437032965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157949763588333445916043953 118462322691250084437032965)
  ·
    refine ⟨22211685504609390831943681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 118462322691250084437032965 22211685504609390831943681)
    ·
      refine ⟨16658764128457043123957761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22211685504609390831943681 16658764128457043123957761)
      ·
        refine ⟨12494073096342782342968321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16658764128457043123957761 12494073096342782342968321)
        ·
          refine ⟨9370554822257086757226241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12494073096342782342968321 9370554822257086757226241)
          ·
            refine ⟨7027916116692815067919681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9370554822257086757226241 7027916116692815067919681)
            ·
              refine ⟨5270937087519611300939761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7027916116692815067919681 5270937087519611300939761)
              ·
                refine ⟨3953202815639708475704821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5270937087519611300939761 3953202815639708475704821)
                ·
                  refine ⟨370612763966222669597327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3953202815639708475704821 370612763966222669597327)
                  ·
                    rfl

theorem cell23_6495892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 2, 2, 5].length) (baseStart_6495892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6495892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6495892 prefixEnd_6495892 := by exact prefixLift 6495892
  have htrace : WordTrace (prefixWord ++ tailWord_6495892) baseStart_6495892 baseEnd_6495892 := by
    simpa [prefixWord, tailWord_6495892, baseEnd_6495892] using wordTrace_append hprefix tailTrace_6495892
  have hstable : (prefixWord ++ tailWord_6495892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6495892).length < 2 ^ (prefixWord ++ tailWord_6495892).sum := by decide
  have hdescent : baseEnd_6495892 < baseStart_6495892 := by decide
  rcases family_descends (prefixWord ++ tailWord_6495892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6495901 : List Nat := [1, 4, 2, 1, 1, 1, 1, 5, 3, 4]
def baseStart_6495901 : Nat := 118140960795 + 6495901 * 2 ^ 59
def prefixEnd_6495901 : Nat := 4983230072969 + 3 ^ 40 * 6495901 * 2
def baseEnd_6495901 : Nat := 1111839832340631497054467

theorem tailTrace_6495901 : CollatzResearch.WordTrace tailWord_6495901 prefixEnd_6495901 1111839832340631497054467 := by
  unfold tailWord_6495901
  simp only [CollatzResearch.WordTrace]
  refine ⟨236924973639467563411143557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157949982426311708940762371 236924973639467563411143557)
  ·
    refine ⟨44423432557400168139589417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 236924973639467563411143557 44423432557400168139589417)
    ·
      refine ⟨33317574418050126104692063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44423432557400168139589417 33317574418050126104692063)
      ·
        refine ⟨49976361627075189157038095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33317574418050126104692063 49976361627075189157038095)
        ·
          refine ⟨74964542440612783735557143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49976361627075189157038095 74964542440612783735557143)
          ·
            refine ⟨112446813660919175603335715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74964542440612783735557143 112446813660919175603335715)
            ·
              refine ⟨168670220491378763405003573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112446813660919175603335715 168670220491378763405003573)
              ·
                refine ⟨15812833171066759069219085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 168670220491378763405003573 15812833171066759069219085)
                ·
                  refine ⟨5929812439150034650957157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15812833171066759069219085 5929812439150034650957157)
                  ·
                    refine ⟨1111839832340631497054467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5929812439150034650957157 1111839832340631497054467)
                    ·
                      rfl

theorem cell23_6495901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 5, 3, 4].length) (baseStart_6495901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6495901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6495901 prefixEnd_6495901 := by exact prefixLift 6495901
  have htrace : WordTrace (prefixWord ++ tailWord_6495901) baseStart_6495901 baseEnd_6495901 := by
    simpa [prefixWord, tailWord_6495901, baseEnd_6495901] using wordTrace_append hprefix tailTrace_6495901
  have hstable : (prefixWord ++ tailWord_6495901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6495901).length < 2 ^ (prefixWord ++ tailWord_6495901).sum := by decide
  have hdescent : baseEnd_6495901 < baseStart_6495901 := by decide
  rcases family_descends (prefixWord ++ tailWord_6495901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6495908 : List Nat := [2, 3, 1, 2, 2, 3, 1, 1, 2, 4, 2]
def baseStart_6495908 : Nat := 118140960795 + 6495908 * 2 ^ 59
def prefixEnd_6495908 : Nat := 4983230072969 + 3 ^ 40 * 6495908 * 2
def baseEnd_6495908 : Nat := 3335523091386475963775869

theorem tailTrace_6495908 : CollatzResearch.WordTrace tailWord_6495908 prefixEnd_6495908 3335523091386475963775869 := by
  unfold tailWord_6495908
  simp only [CollatzResearch.WordTrace]
  refine ⟨118462614475221101803324189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157950152633628135737765585 118462614475221101803324189)
  ·
    refine ⟨44423480428207913176246571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118462614475221101803324189 44423480428207913176246571)
    ·
      refine ⟨66635220642311869764369857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44423480428207913176246571 66635220642311869764369857)
      ·
        refine ⟨49976415481733902323277393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66635220642311869764369857 49976415481733902323277393)
        ·
          refine ⟨37482311611300426742458045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49976415481733902323277393 37482311611300426742458045)
          ·
            refine ⟨14055866854237660028421767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37482311611300426742458045 14055866854237660028421767)
            ·
              refine ⟨21083800281356490042632651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14055866854237660028421767 21083800281356490042632651)
              ·
                refine ⟨31625700422034735063948977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21083800281356490042632651 31625700422034735063948977)
                ·
                  refine ⟨23719275316526051297961733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31625700422034735063948977 23719275316526051297961733)
                  ·
                    refine ⟨4447364121848634618367825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23719275316526051297961733 4447364121848634618367825)
                    ·
                      refine ⟨3335523091386475963775869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4447364121848634618367825 3335523091386475963775869)
                      ·
                        rfl

theorem cell23_6495908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 1, 2, 4, 2].length) (baseStart_6495908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6495908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6495908 prefixEnd_6495908 := by exact prefixLift 6495908
  have htrace : WordTrace (prefixWord ++ tailWord_6495908) baseStart_6495908 baseEnd_6495908 := by
    simpa [prefixWord, tailWord_6495908, baseEnd_6495908] using wordTrace_append hprefix tailTrace_6495908
  have hstable : (prefixWord ++ tailWord_6495908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6495908).length < 2 ^ (prefixWord ++ tailWord_6495908).sum := by decide
  have hdescent : baseEnd_6495908 < baseStart_6495908 := by decide
  rcases family_descends (prefixWord ++ tailWord_6495908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6495925 : List Nat := [1, 3, 3, 3, 2, 2, 1, 1, 2, 1, 4]
def baseStart_6495925 : Nat := 118140960795 + 6495925 * 2 ^ 59
def prefixEnd_6495925 : Nat := 4983230072969 + 3 ^ 40 * 6495925 * 2
def baseEnd_6495925 : Nat := 3335531820557602397263291

theorem tailTrace_6495925 : CollatzResearch.WordTrace tailWord_6495925 prefixEnd_6495925 3335531820557602397263291 := by
  unfold tailWord_6495925
  simp only [CollatzResearch.WordTrace]
  refine ⟨236925848991380615510017229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157950565994253743673344819 236925848991380615510017229)
  ·
    refine ⟨88847193371767730816256461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 236925848991380615510017229 88847193371767730816256461)
    ·
      refine ⟨33317697514412899056096173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88847193371767730816256461 33317697514412899056096173)
      ·
        refine ⟨12494136567904837146036065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33317697514412899056096173 12494136567904837146036065)
        ·
          refine ⟨9370602425928627859527049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12494136567904837146036065 9370602425928627859527049)
          ·
            refine ⟨7027951819446470894645287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9370602425928627859527049 7027951819446470894645287)
            ·
              refine ⟨10541927729169706341967931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7027951819446470894645287 10541927729169706341967931)
              ·
                refine ⟨15812891593754559512951897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10541927729169706341967931 15812891593754559512951897)
                ·
                  refine ⟨11859668695315919634713923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15812891593754559512951897 11859668695315919634713923)
                  ·
                    refine ⟨17789503042973879452070885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11859668695315919634713923 17789503042973879452070885)
                    ·
                      refine ⟨3335531820557602397263291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17789503042973879452070885 3335531820557602397263291)
                      ·
                        rfl

theorem cell23_6495925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_6495925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6495925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6495925 prefixEnd_6495925 := by exact prefixLift 6495925
  have htrace : WordTrace (prefixWord ++ tailWord_6495925) baseStart_6495925 baseEnd_6495925 := by
    simpa [prefixWord, tailWord_6495925, baseEnd_6495925] using wordTrace_append hprefix tailTrace_6495925
  have hstable : (prefixWord ++ tailWord_6495925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6495925).length < 2 ^ (prefixWord ++ tailWord_6495925).sum := by decide
  have hdescent : baseEnd_6495925 < baseStart_6495925 := by decide
  rcases family_descends (prefixWord ++ tailWord_6495925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6495942 : List Nat := [6, 1, 2, 1, 1, 1, 1, 2, 2, 4, 2]
def baseStart_6495942 : Nat := 118140960795 + 6495942 * 2 ^ 59
def prefixEnd_6495942 : Nat := 4983230072969 + 3 ^ 40 * 6495942 * 2
def baseEnd_6495942 : Nat := 3335540549728728830750713

theorem tailTrace_6495942 : CollatzResearch.WordTrace tailWord_6495942 prefixEnd_6495942 3335540549728728830750713 := by
  unfold tailWord_6495942
  simp only [CollatzResearch.WordTrace]
  refine ⟨7403952157259969606668315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 157950979354879351608924053 7403952157259969606668315)
  ·
    refine ⟨11105928235889954410002473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7403952157259969606668315 11105928235889954410002473)
    ·
      refine ⟨8329446176917465807501855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11105928235889954410002473 8329446176917465807501855)
      ·
        refine ⟨12494169265376198711252783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8329446176917465807501855 12494169265376198711252783)
        ·
          refine ⟨18741253898064298066879175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12494169265376198711252783 18741253898064298066879175)
          ·
            refine ⟨28111880847096447100318763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18741253898064298066879175 28111880847096447100318763)
            ·
              refine ⟨42167821270644670650478145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28111880847096447100318763 42167821270644670650478145)
              ·
                refine ⟨31625865952983502987858609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42167821270644670650478145 31625865952983502987858609)
                ·
                  refine ⟨23719399464737627240893957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31625865952983502987858609 23719399464737627240893957)
                  ·
                    refine ⟨4447387399638305107667617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23719399464737627240893957 4447387399638305107667617)
                    ·
                      refine ⟨3335540549728728830750713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4447387399638305107667617 3335540549728728830750713)
                      ·
                        rfl

theorem cell23_6495942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 2, 2, 4, 2].length) (baseStart_6495942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6495942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6495942 prefixEnd_6495942 := by exact prefixLift 6495942
  have htrace : WordTrace (prefixWord ++ tailWord_6495942) baseStart_6495942 baseEnd_6495942 := by
    simpa [prefixWord, tailWord_6495942, baseEnd_6495942] using wordTrace_append hprefix tailTrace_6495942
  have hstable : (prefixWord ++ tailWord_6495942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6495942).length < 2 ^ (prefixWord ++ tailWord_6495942).sum := by decide
  have hdescent : baseEnd_6495942 < baseStart_6495942 := by decide
  rcases family_descends (prefixWord ++ tailWord_6495942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6495991 : List Nat := [1, 1, 3, 1, 1, 1, 5, 2, 4, 4]
def baseStart_6495991 : Nat := 118140960795 + 6495991 * 2 ^ 59
def prefixEnd_6495991 : Nat := 4983230072969 + 3 ^ 40 * 6495991 * 2
def baseEnd_6495991 : Nat := 1111855236760266379679329

theorem tailTrace_6495991 : CollatzResearch.WordTrace tailWord_6495991 prefixEnd_6495991 1111855236760266379679329 := by
  unfold tailWord_6495991
  simp only [CollatzResearch.WordTrace]
  refine ⟨236928256209141508781919827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157952170806094339187946551 236928256209141508781919827)
  ·
    refine ⟨355392384313712263172879741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236928256209141508781919827 355392384313712263172879741)
    ·
      refine ⟨133272144117642098689829903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 355392384313712263172879741 133272144117642098689829903)
      ·
        refine ⟨199908216176463148034744855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133272144117642098689829903 199908216176463148034744855)
        ·
          refine ⟨299862324264694722052117283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199908216176463148034744855 299862324264694722052117283)
          ·
            refine ⟨449793486397042083078175925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 299862324264694722052117283 449793486397042083078175925)
            ·
              refine ⟨42168139349722695288578993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 449793486397042083078175925 42168139349722695288578993)
              ·
                refine ⟨31626104512292021466434245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42168139349722695288578993 31626104512292021466434245)
                ·
                  refine ⟨5929894596054754024956421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31626104512292021466434245 5929894596054754024956421)
                  ·
                    refine ⟨1111855236760266379679329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5929894596054754024956421 1111855236760266379679329)
                    ·
                      rfl

theorem cell23_6495991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 2, 4, 4].length) (baseStart_6495991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6495991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6495991 prefixEnd_6495991 := by exact prefixLift 6495991
  have htrace : WordTrace (prefixWord ++ tailWord_6495991) baseStart_6495991 baseEnd_6495991 := by
    simpa [prefixWord, tailWord_6495991, baseEnd_6495991] using wordTrace_append hprefix tailTrace_6495991
  have hstable : (prefixWord ++ tailWord_6495991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6495991).length < 2 ^ (prefixWord ++ tailWord_6495991).sum := by decide
  have hdescent : baseEnd_6495991 < baseStart_6495991 := by decide
  rcases family_descends (prefixWord ++ tailWord_6495991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6496001 : List Nat := [1, 2, 4, 1, 1, 1, 3, 3, 1, 1, 5]
def baseStart_6496001 : Nat := 118140960795 + 6496001 * 2 ^ 59
def prefixEnd_6496001 : Nat := 4983230072969 + 3 ^ 40 * 6496001 * 2
def baseEnd_6496001 : Nat := 3335570845087344099912941

theorem tailTrace_6496001 : CollatzResearch.WordTrace tailWord_6496001 prefixEnd_6496001 3335570845087344099912941 := by
  unfold tailWord_6496001
  simp only [CollatzResearch.WordTrace]
  refine ⟨236928620939105280489783857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157952413959403520326522571 236928620939105280489783857)
  ·
    refine ⟨177696465704328960367337893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236928620939105280489783857 177696465704328960367337893)
    ·
      refine ⟨33318087319561680068875855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 177696465704328960367337893 33318087319561680068875855)
      ·
        refine ⟨49977130979342520103313783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33318087319561680068875855 49977130979342520103313783)
        ·
          refine ⟨74965696469013780154970675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49977130979342520103313783 74965696469013780154970675)
          ·
            refine ⟨112448544703520670232456013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74965696469013780154970675 112448544703520670232456013)
            ·
              refine ⟨42168204263820251337171005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112448544703520670232456013 42168204263820251337171005)
              ·
                refine ⟨15813076598932594251439127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42168204263820251337171005 15813076598932594251439127)
                ·
                  refine ⟨23719614898398891377158691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15813076598932594251439127 23719614898398891377158691)
                  ·
                    refine ⟨35579422347598337065738037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23719614898398891377158691 35579422347598337065738037)
                    ·
                      refine ⟨3335570845087344099912941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35579422347598337065738037 3335570845087344099912941)
                      ·
                        rfl

theorem cell23_6496001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 3, 1, 1, 5].length) (baseStart_6496001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6496001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6496001 prefixEnd_6496001 := by exact prefixLift 6496001
  have htrace : WordTrace (prefixWord ++ tailWord_6496001) baseStart_6496001 baseEnd_6496001 := by
    simpa [prefixWord, tailWord_6496001, baseEnd_6496001] using wordTrace_append hprefix tailTrace_6496001
  have hstable : (prefixWord ++ tailWord_6496001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6496001).length < 2 ^ (prefixWord ++ tailWord_6496001).sum := by decide
  have hdescent : baseEnd_6496001 < baseStart_6496001 := by decide
  rcases family_descends (prefixWord ++ tailWord_6496001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6496008 : List Nat := [2, 1, 3, 2, 2, 1, 2, 4, 2, 4]
def baseStart_6496008 : Nat := 118140960795 + 6496008 * 2 ^ 59
def prefixEnd_6496008 : Nat := 4983230072969 + 3 ^ 40 * 6496008 * 2
def baseEnd_6496008 : Nat := 1111858146483975190841803

theorem tailTrace_6496008 : CollatzResearch.WordTrace tailWord_6496008 prefixEnd_6496008 1111858146483975190841803 := by
  unfold tailWord_6496008
  simp only [CollatzResearch.WordTrace]
  refine ⟨118464438125039960342644339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157952584166719947123525785 118464438125039960342644339)
  ·
    refine ⟨177696657187559940513966509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118464438125039960342644339 177696657187559940513966509)
    ·
      refine ⟨66636246445334977692737441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177696657187559940513966509 66636246445334977692737441)
      ·
        refine ⟨49977184834001233269553081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66636246445334977692737441 49977184834001233269553081)
        ·
          refine ⟨37482888625500924952164811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49977184834001233269553081 37482888625500924952164811)
          ·
            refine ⟨56224332938251387428247217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37482888625500924952164811 56224332938251387428247217)
            ·
              refine ⟨42168249703688540571185413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56224332938251387428247217 42168249703688540571185413)
              ·
                refine ⟨7906546819441601357097265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42168249703688540571185413 7906546819441601357097265)
                ·
                  refine ⟨5929910114581201017822949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7906546819441601357097265 5929910114581201017822949)
                  ·
                    refine ⟨1111858146483975190841803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5929910114581201017822949 1111858146483975190841803)
                    ·
                      rfl

theorem cell23_6496008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 4, 2, 4].length) (baseStart_6496008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6496008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6496008 prefixEnd_6496008 := by exact prefixLift 6496008
  have htrace : WordTrace (prefixWord ++ tailWord_6496008) baseStart_6496008 baseEnd_6496008 := by
    simpa [prefixWord, tailWord_6496008, baseEnd_6496008] using wordTrace_append hprefix tailTrace_6496008
  have hstable : (prefixWord ++ tailWord_6496008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6496008).length < 2 ^ (prefixWord ++ tailWord_6496008).sum := by decide
  have hdescent : baseEnd_6496008 < baseStart_6496008 := by decide
  rcases family_descends (prefixWord ++ tailWord_6496008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6496021 : List Nat := [1, 3, 2, 1, 2, 4, 2, 8]
def baseStart_6496021 : Nat := 118140960795 + 6496021 * 2 ^ 59
def prefixEnd_6496021 : Nat := 4983230072969 + 3 ^ 40 * 6496021 * 2
def baseEnd_6496021 : Nat := 123540041285201260061587

theorem tailTrace_6496021 : CollatzResearch.WordTrace tailWord_6496021 prefixEnd_6496021 123540041285201260061587 := by
  unfold tailWord_6496021
  simp only [CollatzResearch.WordTrace]
  refine ⟨236929350399032823905511917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157952900266021882603674611 236929350399032823905511917)
  ·
    refine ⟨88848506399637308964566969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 236929350399032823905511917 88848506399637308964566969)
    ·
      refine ⟨66636379799727981723425227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88848506399637308964566969 66636379799727981723425227)
      ·
        refine ⟨99954569699591972585137841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66636379799727981723425227 99954569699591972585137841)
        ·
          refine ⟨74965927274693979438853381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99954569699591972585137841 74965927274693979438853381)
          ·
            refine ⟨14056111364005121144785009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74965927274693979438853381 14056111364005121144785009)
            ·
              refine ⟨10542083523003840858588757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14056111364005121144785009 10542083523003840858588757)
              ·
                refine ⟨123540041285201260061587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10542083523003840858588757 123540041285201260061587)
                ·
                  rfl

theorem cell23_6496021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 2, 8].length) (baseStart_6496021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6496021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6496021 prefixEnd_6496021 := by exact prefixLift 6496021
  have htrace : WordTrace (prefixWord ++ tailWord_6496021) baseStart_6496021 baseEnd_6496021 := by
    simpa [prefixWord, tailWord_6496021, baseEnd_6496021] using wordTrace_append hprefix tailTrace_6496021
  have hstable : (prefixWord ++ tailWord_6496021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6496021).length < 2 ^ (prefixWord ++ tailWord_6496021).sum := by decide
  have hdescent : baseEnd_6496021 < baseStart_6496021 := by decide
  rcases family_descends (prefixWord ++ tailWord_6496021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6496071 : List Nat := [1, 1, 4, 1, 2, 1, 3, 1, 2, 3, 4]
def baseStart_6496071 : Nat := 118140960795 + 6496071 * 2 ^ 59
def prefixEnd_6496071 : Nat := 4983230072969 + 3 ^ 40 * 6496071 * 2
def baseEnd_6496071 : Nat := 3335606788733158826037619

theorem tailTrace_6496071 : CollatzResearch.WordTrace tailWord_6496071 prefixEnd_6496071 3335606788733158826037619 := by
  unfold tailWord_6496071
  simp only [CollatzResearch.WordTrace]
  refine ⟨236931174048851682444832067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157954116032567788296554711 236931174048851682444832067)
  ·
    refine ⟨355396761073277523667248101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236931174048851682444832067 355396761073277523667248101)
    ·
      refine ⟨66636892701239535687609019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 355396761073277523667248101 66636892701239535687609019)
      ·
        refine ⟨99955339051859303531413529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66636892701239535687609019 99955339051859303531413529)
        ·
          refine ⟨74966504288894477648560147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99955339051859303531413529 74966504288894477648560147)
          ·
            refine ⟨112449756433341716472840221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74966504288894477648560147 112449756433341716472840221)
            ·
              refine ⟨42168658662503143677315083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112449756433341716472840221 42168658662503143677315083)
              ·
                refine ⟨63252987993754715515972625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42168658662503143677315083 63252987993754715515972625)
                ·
                  refine ⟨47439740995316036636979469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63252987993754715515972625 47439740995316036636979469)
                  ·
                    refine ⟨17789902873243513738867301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47439740995316036636979469 17789902873243513738867301)
                    ·
                      refine ⟨3335606788733158826037619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17789902873243513738867301 3335606788733158826037619)
                      ·
                        rfl

theorem cell23_6496071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 1, 2, 3, 4].length) (baseStart_6496071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6496071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6496071 prefixEnd_6496071 := by exact prefixLift 6496071
  have htrace : WordTrace (prefixWord ++ tailWord_6496071) baseStart_6496071 baseEnd_6496071 := by
    simpa [prefixWord, tailWord_6496071, baseEnd_6496071] using wordTrace_append hprefix tailTrace_6496071
  have hstable : (prefixWord ++ tailWord_6496071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6496071).length < 2 ^ (prefixWord ++ tailWord_6496071).sum := by decide
  have hdescent : baseEnd_6496071 < baseStart_6496071 := by decide
  rcases family_descends (prefixWord ++ tailWord_6496071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6496081 : List Nat := [1, 2, 2, 1, 5, 1, 1, 1, 1, 8]
def baseStart_6496081 : Nat := 118140960795 + 6496081 * 2 ^ 59
def prefixEnd_6496081 : Nat := 4983230072969 + 3 ^ 40 * 6496081 * 2
def baseEnd_6496081 : Nat := 1111870641179901262304191

theorem tailTrace_6496081 : CollatzResearch.WordTrace tailWord_6496081 prefixEnd_6496081 1111870641179901262304191 := by
  unfold tailWord_6496081
  simp only [CollatzResearch.WordTrace]
  refine ⟨236931538778815454152696097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157954359185876969435130731 236931538778815454152696097)
  ·
    refine ⟨177698654084111590614522073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236931538778815454152696097 177698654084111590614522073)
    ·
      refine ⟨133273990563083692960891555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177698654084111590614522073 133273990563083692960891555)
      ·
        refine ⟨199910985844625539441337333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133273990563083692960891555 199910985844625539441337333)
        ·
          refine ⟨18741654922933644322625375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 199910985844625539441337333 18741654922933644322625375)
          ·
            refine ⟨28112482384400466483938063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18741654922933644322625375 28112482384400466483938063)
            ·
              refine ⟨42168723576600699725907095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28112482384400466483938063 42168723576600699725907095)
              ·
                refine ⟨63253085364901049588860643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42168723576600699725907095 63253085364901049588860643)
                ·
                  refine ⟨94879628047351574383290965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63253085364901049588860643 94879628047351574383290965)
                  ·
                    refine ⟨1111870641179901262304191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 94879628047351574383290965 1111870641179901262304191)
                    ·
                      rfl

theorem cell23_6496081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 1, 1, 8].length) (baseStart_6496081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6496081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6496081 prefixEnd_6496081 := by exact prefixLift 6496081
  have htrace : WordTrace (prefixWord ++ tailWord_6496081) baseStart_6496081 baseEnd_6496081 := by
    simpa [prefixWord, tailWord_6496081, baseEnd_6496081] using wordTrace_append hprefix tailTrace_6496081
  have hstable : (prefixWord ++ tailWord_6496081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6496081).length < 2 ^ (prefixWord ++ tailWord_6496081).sum := by decide
  have hdescent : baseEnd_6496081 < baseStart_6496081 := by decide
  rcases family_descends (prefixWord ++ tailWord_6496081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6496101 : List Nat := [1, 3, 1, 3, 1, 1, 1, 1, 3, 4, 4]
def baseStart_6496101 : Nat := 118140960795 + 6496101 * 2 ^ 59
def prefixEnd_6496101 : Nat := 4983230072969 + 3 ^ 40 * 6496101 * 2
def baseEnd_6496101 : Nat := 3335622193152793708662481

theorem tailTrace_6496101 : CollatzResearch.WordTrace tailWord_6496101 prefixEnd_6496101 3335622193152793708662481 := by
  unfold tailWord_6496101
  simp only [CollatzResearch.WordTrace]
  refine ⟨236932268238742997568424157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157954845492495331712282771 236932268238742997568424157)
  ·
    refine ⟨88849600589528624088159059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 236932268238742997568424157 88849600589528624088159059)
    ·
      refine ⟨133274400884292936132238589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88849600589528624088159059 133274400884292936132238589)
      ·
        refine ⟨49977900331609851049589471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133274400884292936132238589 49977900331609851049589471)
        ·
          refine ⟨74966850497414776574384207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49977900331609851049589471 74966850497414776574384207)
          ·
            refine ⟨112450275746122164861576311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74966850497414776574384207 112450275746122164861576311)
            ·
              refine ⟨168675413619183247292364467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112450275746122164861576311 168675413619183247292364467)
              ·
                refine ⟨253013120428774870938546701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 168675413619183247292364467 253013120428774870938546701)
                ·
                  refine ⟨94879920160790576601955013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 253013120428774870938546701 94879920160790576601955013)
                  ·
                    refine ⟨17789985030148233112866565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 94879920160790576601955013 17789985030148233112866565)
                    ·
                      refine ⟨3335622193152793708662481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17789985030148233112866565 3335622193152793708662481)
                      ·
                        rfl

theorem cell23_6496101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 3, 4, 4].length) (baseStart_6496101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6496101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6496101 prefixEnd_6496101 := by exact prefixLift 6496101
  have htrace : WordTrace (prefixWord ++ tailWord_6496101) baseStart_6496101 baseEnd_6496101 := by
    simpa [prefixWord, tailWord_6496101, baseEnd_6496101] using wordTrace_append hprefix tailTrace_6496101
  have hstable : (prefixWord ++ tailWord_6496101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6496101).length < 2 ^ (prefixWord ++ tailWord_6496101).sum := by decide
  have hdescent : baseEnd_6496101 < baseStart_6496101 := by decide
  rcases family_descends (prefixWord ++ tailWord_6496101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6496122 : List Nat := [3, 1, 1, 1, 1, 1, 7, 2, 2, 2, 2]
def baseStart_6496122 : Nat := 118140960795 + 6496122 * 2 ^ 59
def prefixEnd_6496122 : Nat := 4983230072969 + 3 ^ 40 * 6496122 * 2
def baseEnd_6496122 : Nat := 3335632976246538126499885

theorem tailTrace_6496122 : CollatzResearch.WordTrace tailWord_6496122 prefixEnd_6496122 3335632976246538126499885 := by
  unfold tailWord_6496122
  simp only [CollatzResearch.WordTrace]
  refine ⟨59233258542916729538734655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157955356114444612103292413 59233258542916729538734655)
  ·
    refine ⟨88849887814375094308101983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59233258542916729538734655 88849887814375094308101983)
    ·
      refine ⟨133274831721562641462152975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88849887814375094308101983 133274831721562641462152975)
      ·
        refine ⟨199912247582343962193229463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133274831721562641462152975 199912247582343962193229463)
        ·
          refine ⟨299868371373515943289844195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199912247582343962193229463 299868371373515943289844195)
          ·
            refine ⟨449802557060273914934766293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 299868371373515943289844195 449802557060273914934766293)
            ·
              refine ⟨10542247431100169881283585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 449802557060273914934766293 10542247431100169881283585)
              ·
                refine ⟨7906685573325127410962689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10542247431100169881283585 7906685573325127410962689)
                ·
                  refine ⟨5930014179993845558222017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7906685573325127410962689 5930014179993845558222017)
                  ·
                    refine ⟨4447510634995384168666513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5930014179993845558222017 4447510634995384168666513)
                    ·
                      refine ⟨3335632976246538126499885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4447510634995384168666513 3335632976246538126499885)
                      ·
                        rfl

theorem cell23_6496122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 7, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 7, 2, 2, 2, 2].length) (baseStart_6496122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6496122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6496122 prefixEnd_6496122 := by exact prefixLift 6496122
  have htrace : WordTrace (prefixWord ++ tailWord_6496122) baseStart_6496122 baseEnd_6496122 := by
    simpa [prefixWord, tailWord_6496122, baseEnd_6496122] using wordTrace_append hprefix tailTrace_6496122
  have hstable : (prefixWord ++ tailWord_6496122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6496122).length < 2 ^ (prefixWord ++ tailWord_6496122).sum := by decide
  have hdescent : baseEnd_6496122 < baseStart_6496122 := by decide
  rcases family_descends (prefixWord ++ tailWord_6496122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6496128 : List Nat := [2, 1, 1, 2, 1, 2, 3, 6, 5]
def baseStart_6496128 : Nat := 118140960795 + 6496128 * 2 ^ 59
def prefixEnd_6496128 : Nat := 4983230072969 + 3 ^ 40 * 6496128 * 2
def baseEnd_6496128 : Nat := 370626228570051678113873

theorem tailTrace_6496128 : CollatzResearch.WordTrace tailWord_6496128 prefixEnd_6496128 370626228570051678113873 := by
  unfold tailWord_6496128
  simp only [CollatzResearch.WordTrace]
  refine ⟨118466626504822590589828519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157955502006430120786438025 118466626504822590589828519)
  ·
    refine ⟨177699939757233885884742779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118466626504822590589828519 177699939757233885884742779)
    ·
      refine ⟨266549909635850828827114169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177699939757233885884742779 266549909635850828827114169)
      ·
        refine ⟨199912432226888121620335627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 266549909635850828827114169 199912432226888121620335627)
        ·
          refine ⟨299868648340332182430503441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199912432226888121620335627 299868648340332182430503441)
          ·
            refine ⟨224901486255249136822877581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 299868648340332182430503441 224901486255249136822877581)
            ·
              refine ⟨84338057345718426308579093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 224901486255249136822877581 84338057345718426308579093)
              ·
                refine ⟨3953346438080551233214645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 84338057345718426308579093 3953346438080551233214645)
                ·
                  refine ⟨370626228570051678113873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3953346438080551233214645 370626228570051678113873)
                  ·
                    rfl

theorem cell23_6496128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 6, 5].length) (baseStart_6496128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6496128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6496128 prefixEnd_6496128 := by exact prefixLift 6496128
  have htrace : WordTrace (prefixWord ++ tailWord_6496128) baseStart_6496128 baseEnd_6496128 := by
    simpa [prefixWord, tailWord_6496128, baseEnd_6496128] using wordTrace_append hprefix tailTrace_6496128
  have hstable : (prefixWord ++ tailWord_6496128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6496128).length < 2 ^ (prefixWord ++ tailWord_6496128).sum := by decide
  have hdescent : baseEnd_6496128 < baseStart_6496128 := by decide
  rcases family_descends (prefixWord ++ tailWord_6496128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6496215 : List Nat := [1, 1, 3, 2, 1, 1, 6, 1, 2, 2, 3]
def baseStart_6496215 : Nat := 118140960795 + 6496215 * 2 ^ 59
def prefixEnd_6496215 : Nat := 4983230072969 + 3 ^ 40 * 6496215 * 2
def baseEnd_6496215 : Nat := 3335680729947406262636957

theorem tailTrace_6496215 : CollatzResearch.WordTrace tailWord_6496215 prefixEnd_6496215 3335680729947406262636957 := by
  unfold tailWord_6496215
  simp only [CollatzResearch.WordTrace]
  refine ⟨236936426160329995038074099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157957617440219996692049399 236936426160329995038074099)
  ·
    refine ⟨355404639240494992557111149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236936426160329995038074099 355404639240494992557111149)
    ·
      refine ⟨133276739715185622208916681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 355404639240494992557111149 133276739715185622208916681)
      ·
        refine ⟨99957554786389216656687511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133276739715185622208916681 99957554786389216656687511)
        ·
          refine ⟨149936332179583824985031267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99957554786389216656687511 149936332179583824985031267)
          ·
            refine ⟨224904498269375737477546901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149936332179583824985031267 224904498269375737477546901)
            ·
              refine ⟨10542398356376987694260011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 224904498269375737477546901 10542398356376987694260011)
              ·
                refine ⟨15813597534565481541390017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10542398356376987694260011 15813597534565481541390017)
                ·
                  refine ⟨11860198150924111156042513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15813597534565481541390017 11860198150924111156042513)
                  ·
                    refine ⟨8895148613193083367031885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11860198150924111156042513 8895148613193083367031885)
                    ·
                      refine ⟨3335680729947406262636957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8895148613193083367031885 3335680729947406262636957)
                      ·
                        rfl

theorem cell23_6496215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 6, 1, 2, 2, 3].length) (baseStart_6496215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6496215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6496215 prefixEnd_6496215 := by exact prefixLift 6496215
  have htrace : WordTrace (prefixWord ++ tailWord_6496215) baseStart_6496215 baseEnd_6496215 := by
    simpa [prefixWord, tailWord_6496215, baseEnd_6496215] using wordTrace_append hprefix tailTrace_6496215
  have hstable : (prefixWord ++ tailWord_6496215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6496215).length < 2 ^ (prefixWord ++ tailWord_6496215).sum := by decide
  have hdescent : baseEnd_6496215 < baseStart_6496215 := by decide
  rcases family_descends (prefixWord ++ tailWord_6496215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6496248 : List Nat := [2, 1, 2, 1, 1, 3, 3, 2, 3, 5]
def baseStart_6496248 : Nat := 118140960795 + 6496248 * 2 ^ 59
def prefixEnd_6496248 : Nat := 4983230072969 + 3 ^ 40 * 6496248 * 2
def baseEnd_6496248 : Nat := 1111899224936334877841435

theorem tailTrace_6496248 : CollatzResearch.WordTrace tailWord_6496248 prefixEnd_6496248 1111899224936334877841435 := by
  unfold tailWord_6496248
  simp only [CollatzResearch.WordTrace]
  refine ⟨118468814884605220837012699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157958419846140294449350265 118468814884605220837012699)
  ·
    refine ⟨177703222326907831255519049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118468814884605220837012699 177703222326907831255519049)
    ·
      refine ⟨133277416745180873441639287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177703222326907831255519049 133277416745180873441639287)
      ·
        refine ⟨199916125117771310162458931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133277416745180873441639287 199916125117771310162458931)
        ·
          refine ⟨299874187676656965243688397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199916125117771310162458931 299874187676656965243688397)
          ·
            refine ⟨112452820378746361966383149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 299874187676656965243688397 112452820378746361966383149)
            ·
              refine ⟨42169807642029885737393681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112452820378746361966383149 42169807642029885737393681)
              ·
                refine ⟨31627355731522414303045261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42169807642029885737393681 31627355731522414303045261)
                ·
                  refine ⟨11860258399320905363641973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31627355731522414303045261 11860258399320905363641973)
                  ·
                    refine ⟨1111899224936334877841435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11860258399320905363641973 1111899224936334877841435)
                    ·
                      rfl

theorem cell23_6496248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 2, 3, 5].length) (baseStart_6496248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6496248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6496248 prefixEnd_6496248 := by exact prefixLift 6496248
  have htrace : WordTrace (prefixWord ++ tailWord_6496248) baseStart_6496248 baseEnd_6496248 := by
    simpa [prefixWord, tailWord_6496248, baseEnd_6496248] using wordTrace_append hprefix tailTrace_6496248
  have hstable : (prefixWord ++ tailWord_6496248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6496248).length < 2 ^ (prefixWord ++ tailWord_6496248).sum := by decide
  have hdescent : baseEnd_6496248 < baseStart_6496248 := by decide
  rcases family_descends (prefixWord ++ tailWord_6496248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6496255 : List Nat := [1, 1, 2, 2, 1, 2, 1, 4, 4, 3, 2]
def baseStart_6496255 : Nat := 118140960795 + 6496255 * 2 ^ 59
def prefixEnd_6496255 : Nat := 4983230072969 + 3 ^ 40 * 6496255 * 2
def baseEnd_6496255 : Nat := 3335701269173586106136773

theorem tailTrace_6496255 : CollatzResearch.WordTrace tailWord_6496255 prefixEnd_6496255 3335701269173586106136773 := by
  unfold tailWord_6496255
  simp only [CollatzResearch.WordTrace]
  refine ⟨236937885080185081869530219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157958590053456721246353479 236937885080185081869530219)
  ·
    refine ⟨355406827620277622804295329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236937885080185081869530219 355406827620277622804295329)
    ·
      refine ⟨266555120715208217103221497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 355406827620277622804295329 266555120715208217103221497)
      ·
        refine ⟨199916340536406162827416123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 266555120715208217103221497 199916340536406162827416123)
        ·
          refine ⟨299874510804609244241124185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199916340536406162827416123 299874510804609244241124185)
          ·
            refine ⟨224905883103456933180843139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 299874510804609244241124185 224905883103456933180843139)
            ·
              refine ⟨337358824655185399771264709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 224905883103456933180843139 337358824655185399771264709)
              ·
                refine ⟨63254779622847262457112133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 337358824655185399771264709 63254779622847262457112133)
                ·
                  refine ⟨11860271179283861710708525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63254779622847262457112133 11860271179283861710708525)
                  ·
                    refine ⟨4447601692231448141515697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11860271179283861710708525 4447601692231448141515697)
                    ·
                      refine ⟨3335701269173586106136773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4447601692231448141515697 3335701269173586106136773)
                      ·
                        rfl

theorem cell23_6496255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 4, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 4, 4, 3, 2].length) (baseStart_6496255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6496255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6496255 prefixEnd_6496255 := by exact prefixLift 6496255
  have htrace : WordTrace (prefixWord ++ tailWord_6496255) baseStart_6496255 baseEnd_6496255 := by
    simpa [prefixWord, tailWord_6496255, baseEnd_6496255] using wordTrace_append hprefix tailTrace_6496255
  have hstable : (prefixWord ++ tailWord_6496255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6496255).length < 2 ^ (prefixWord ++ tailWord_6496255).sum := by decide
  have hdescent : baseEnd_6496255 < baseStart_6496255 := by decide
  rcases family_descends (prefixWord ++ tailWord_6496255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6496282 : List Nat := [3, 1, 1, 3, 1, 3, 4, 1, 1, 5]
def baseStart_6496282 : Nat := 118140960795 + 6496282 * 2 ^ 59
def prefixEnd_6496282 : Nat := 4983230072969 + 3 ^ 40 * 6496282 * 2
def baseEnd_6496282 : Nat := 1111905044383752500166383

theorem tailTrace_6496282 : CollatzResearch.WordTrace tailWord_6496282 prefixEnd_6496282 1111905044383752500166383 := by
  unfold tailWord_6496282
  simp only [CollatzResearch.WordTrace]
  refine ⟨59234717462771816370190775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157959246567391510320508733 59234717462771816370190775)
  ·
    refine ⟨88852076194157724555286163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59234717462771816370190775 88852076194157724555286163)
    ·
      refine ⟨133278114291236586832929245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88852076194157724555286163 133278114291236586832929245)
      ·
        refine ⟨49979292859213720062348467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133278114291236586832929245 49979292859213720062348467)
        ·
          refine ⟨74968939288820580093522701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49979292859213720062348467 74968939288820580093522701)
          ·
            refine ⟨28113352233307717535071013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74968939288820580093522701 28113352233307717535071013)
            ·
              refine ⟨5271253543745197037825815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28113352233307717535071013 5271253543745197037825815)
              ·
                refine ⟨7906880315617795556738723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5271253543745197037825815 7906880315617795556738723)
                ·
                  refine ⟨11860320473426693335108085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7906880315617795556738723 11860320473426693335108085)
                  ·
                    refine ⟨1111905044383752500166383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11860320473426693335108085 1111905044383752500166383)
                    ·
                      rfl

theorem cell23_6496282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 4, 1, 1, 5].length) (baseStart_6496282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6496282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6496282 prefixEnd_6496282 := by exact prefixLift 6496282
  have htrace : WordTrace (prefixWord ++ tailWord_6496282) baseStart_6496282 baseEnd_6496282 := by
    simpa [prefixWord, tailWord_6496282, baseEnd_6496282] using wordTrace_append hprefix tailTrace_6496282
  have hstable : (prefixWord ++ tailWord_6496282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6496282).length < 2 ^ (prefixWord ++ tailWord_6496282).sum := by decide
  have hdescent : baseEnd_6496282 < baseStart_6496282 := by decide
  rcases family_descends (prefixWord ++ tailWord_6496282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6496296 : List Nat := [2, 1, 5, 3, 1, 1, 2, 1, 3, 1, 3]
def baseStart_6496296 : Nat := 118140960795 + 6496296 * 2 ^ 59
def prefixEnd_6496296 : Nat := 4983230072969 + 3 ^ 40 * 6496296 * 2
def baseEnd_6496296 : Nat := 3335722321880420445724085

theorem tailTrace_6496296 : CollatzResearch.WordTrace tailWord_6496296 prefixEnd_6496296 3335722321880420445724085 := by
  unfold tailWord_6496296
  simp only [CollatzResearch.WordTrace]
  refine ⟨118469690236518272935886371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157959586982024363914515161 118469690236518272935886371)
  ·
    refine ⟨177704535354777409403829557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118469690236518272935886371 177704535354777409403829557)
    ·
      refine ⟨16659800189510382131609021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 177704535354777409403829557 16659800189510382131609021)
      ·
        refine ⟨6247425071066393299353383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16659800189510382131609021 6247425071066393299353383)
        ·
          refine ⟨9371137606599589949030075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6247425071066393299353383 9371137606599589949030075)
          ·
            refine ⟨14056706409899384923545113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9371137606599589949030075 14056706409899384923545113)
            ·
              refine ⟨10542529807424538692658835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14056706409899384923545113 10542529807424538692658835)
              ·
                refine ⟨15813794711136808038988253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10542529807424538692658835 15813794711136808038988253)
                ·
                  refine ⟨5930173016676303014620595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15813794711136808038988253 5930173016676303014620595)
                  ·
                    refine ⟨8895259525014454521930893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5930173016676303014620595 8895259525014454521930893)
                    ·
                      refine ⟨3335722321880420445724085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8895259525014454521930893 3335722321880420445724085)
                      ·
                        rfl

theorem cell23_6496296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_6496296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6496296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6496296 prefixEnd_6496296 := by exact prefixLift 6496296
  have htrace : WordTrace (prefixWord ++ tailWord_6496296) baseStart_6496296 baseEnd_6496296 := by
    simpa [prefixWord, tailWord_6496296, baseEnd_6496296] using wordTrace_append hprefix tailTrace_6496296
  have hstable : (prefixWord ++ tailWord_6496296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6496296).length < 2 ^ (prefixWord ++ tailWord_6496296).sum := by decide
  have hdescent : baseEnd_6496296 < baseStart_6496296 := by decide
  rcases family_descends (prefixWord ++ tailWord_6496296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6496305 : List Nat := [1, 2, 2, 3, 1, 4, 1, 2, 1, 1, 5]
def baseStart_6496305 : Nat := 118140960795 + 6496305 * 2 ^ 59
def prefixEnd_6496305 : Nat := 4983230072969 + 3 ^ 40 * 6496305 * 2
def baseEnd_6496305 : Nat := 3335726943206310910511543

theorem tailTrace_6496305 : CollatzResearch.WordTrace tailWord_6496305 prefixEnd_6496305 3335726943206310910511543 := by
  unfold tailWord_6496305
  simp only [CollatzResearch.WordTrace]
  refine ⟨236939708730003940408850369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157959805820002626939233579 236939708730003940408850369)
  ·
    refine ⟨177704781547502955306637777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236939708730003940408850369 177704781547502955306637777)
    ·
      refine ⟨133278586160627216479978333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177704781547502955306637777 133278586160627216479978333)
      ·
        refine ⟨49979469810235206179991875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133278586160627216479978333 49979469810235206179991875)
        ·
          refine ⟨74969204715352809269987813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49979469810235206179991875 74969204715352809269987813)
          ·
            refine ⟨14056725884128651738122715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74969204715352809269987813 14056725884128651738122715)
            ·
              refine ⟨21085088826192977607184073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14056725884128651738122715 21085088826192977607184073)
              ·
                refine ⟨15813816619644733205388055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21085088826192977607184073 15813816619644733205388055)
                ·
                  refine ⟨23720724929467099808082083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15813816619644733205388055 23720724929467099808082083)
                  ·
                    refine ⟨35581087394200649712123125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23720724929467099808082083 35581087394200649712123125)
                    ·
                      refine ⟨3335726943206310910511543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35581087394200649712123125 3335726943206310910511543)
                      ·
                        rfl

theorem cell23_6496305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 2, 1, 1, 5].length) (baseStart_6496305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6496305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6496305 prefixEnd_6496305 := by exact prefixLift 6496305
  have htrace : WordTrace (prefixWord ++ tailWord_6496305) baseStart_6496305 baseEnd_6496305 := by
    simpa [prefixWord, tailWord_6496305, baseEnd_6496305] using wordTrace_append hprefix tailTrace_6496305
  have hstable : (prefixWord ++ tailWord_6496305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6496305).length < 2 ^ (prefixWord ++ tailWord_6496305).sum := by decide
  have hdescent : baseEnd_6496305 < baseStart_6496305 := by decide
  rcases family_descends (prefixWord ++ tailWord_6496305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6496312 : List Nat := [2, 1, 2, 1, 6, 2, 1, 1, 1, 6]
def baseStart_6496312 : Nat := 118140960795 + 6496312 * 2 ^ 59
def prefixEnd_6496312 : Nat := 4983230072969 + 3 ^ 40 * 6496312 * 2
def baseEnd_6496312 : Nat := 1111910179190297461041337

theorem tailTrace_6496312 : CollatzResearch.WordTrace tailWord_6496312 prefixEnd_6496312 1111910179190297461041337 := by
  unfold tailWord_6496312
  simp only [CollatzResearch.WordTrace]
  refine ⟨118469982020489290302177595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157959976027319053736236793 118469982020489290302177595)
  ·
    refine ⟨177704973030733935453266393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118469982020489290302177595 177704973030733935453266393)
    ·
      refine ⟨133278729773050451589949795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177704973030733935453266393 133278729773050451589949795)
      ·
        refine ⟨199918094659575677384924693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133278729773050451589949795 199918094659575677384924693)
        ·
          refine ⟨9371160687167609877418345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 199918094659575677384924693 9371160687167609877418345)
          ·
            refine ⟨7028370515375707408063759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9371160687167609877418345 7028370515375707408063759)
            ·
              refine ⟨10542555773063561112095639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7028370515375707408063759 10542555773063561112095639)
              ·
                refine ⟨15813833659595341668143459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10542555773063561112095639 15813833659595341668143459)
                ·
                  refine ⟨23720750489393012502215189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15813833659595341668143459 23720750489393012502215189)
                  ·
                    refine ⟨1111910179190297461041337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23720750489393012502215189 1111910179190297461041337)
                    ·
                      rfl

theorem cell23_6496312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 1, 1, 1, 6].length) (baseStart_6496312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6496312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6496312 prefixEnd_6496312 := by exact prefixLift 6496312
  have htrace : WordTrace (prefixWord ++ tailWord_6496312) baseStart_6496312 baseEnd_6496312 := by
    simpa [prefixWord, tailWord_6496312, baseEnd_6496312] using wordTrace_append hprefix tailTrace_6496312
  have hstable : (prefixWord ++ tailWord_6496312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6496312).length < 2 ^ (prefixWord ++ tailWord_6496312).sum := by decide
  have hdescent : baseEnd_6496312 < baseStart_6496312 := by decide
  rcases family_descends (prefixWord ++ tailWord_6496312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6496342 : List Nat := [5, 2, 2, 1, 1, 1, 11]
def baseStart_6496342 : Nat := 118140960795 + 6496342 * 2 ^ 59
def prefixEnd_6496342 : Nat := 4983230072969 + 3 ^ 40 * 6496342 * 2
def baseEnd_6496342 : Nat := 41182048666549719330233

theorem tailTrace_6496342 : CollatzResearch.WordTrace tailWord_6496342 prefixEnd_6496342 41182048666549719330233 := by
  unfold tailWord_6496342
  simp only [CollatzResearch.WordTrace]
  refine ⟨14808816139429368482996705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 157960705487246597151964853 14808816139429368482996705)
  ·
    refine ⟨11106612104572026362247529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14808816139429368482996705 11106612104572026362247529)
    ·
      refine ⟨8329959078429019771685647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11106612104572026362247529 8329959078429019771685647)
      ·
        refine ⟨12494938617643529657528471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8329959078429019771685647 12494938617643529657528471)
        ·
          refine ⟨18742407926465294486292707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12494938617643529657528471 18742407926465294486292707)
          ·
            refine ⟨28113611889697941729439061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18742407926465294486292707 28113611889697941729439061)
            ·
              refine ⟨41182048666549719330233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 28113611889697941729439061 41182048666549719330233)
              ·
                rfl

theorem cell23_6496342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 11].length) (baseStart_6496342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6496342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6496342 prefixEnd_6496342 := by exact prefixLift 6496342
  have htrace : WordTrace (prefixWord ++ tailWord_6496342) baseStart_6496342 baseEnd_6496342 := by
    simpa [prefixWord, tailWord_6496342, baseEnd_6496342] using wordTrace_append hprefix tailTrace_6496342
  have hstable : (prefixWord ++ tailWord_6496342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6496342).length < 2 ^ (prefixWord ++ tailWord_6496342).sum := by decide
  have hdescent : baseEnd_6496342 < baseStart_6496342 := by decide
  rcases family_descends (prefixWord ++ tailWord_6496342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6496352 : List Nat := [2, 1, 1, 3, 2, 3, 2, 1, 4, 1, 3]
def baseStart_6496352 : Nat := 118140960795 + 6496352 * 2 ^ 59
def prefixEnd_6496352 : Nat := 4983230072969 + 3 ^ 40 * 6496352 * 2
def baseEnd_6496352 : Nat := 3335751076797072226623827

theorem tailTrace_6496352 : CollatzResearch.WordTrace tailWord_6496352 prefixEnd_6496352 3335751076797072226623827 := by
  unfold tailWord_6496352
  simp only [CollatzResearch.WordTrace]
  refine ⟨118470711480416833717905655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157960948640555778290540873 118470711480416833717905655)
  ·
    refine ⟨177706067220625250576858483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118470711480416833717905655 177706067220625250576858483)
    ·
      refine ⟨266559100830937875865287725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177706067220625250576858483 266559100830937875865287725)
      ·
        refine ⟨99959662811601703449482897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 266559100830937875865287725 99959662811601703449482897)
        ·
          refine ⟨74969747108701277587112173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99959662811601703449482897 74969747108701277587112173)
          ·
            refine ⟨28113655165762979095167065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74969747108701277587112173 28113655165762979095167065)
            ·
              refine ⟨21085241374322234321375299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28113655165762979095167065 21085241374322234321375299)
              ·
                refine ⟨31627862061483351482062949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21085241374322234321375299 31627862061483351482062949)
                ·
                  refine ⟨5930224136528128402886803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31627862061483351482062949 5930224136528128402886803)
                  ·
                    refine ⟨8895336204792192604330205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5930224136528128402886803 8895336204792192604330205)
                    ·
                      refine ⟨3335751076797072226623827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8895336204792192604330205 3335751076797072226623827)
                      ·
                        rfl

theorem cell23_6496352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 1, 4, 1, 3].length) (baseStart_6496352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6496352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6496352 prefixEnd_6496352 := by exact prefixLift 6496352
  have htrace : WordTrace (prefixWord ++ tailWord_6496352) baseStart_6496352 baseEnd_6496352 := by
    simpa [prefixWord, tailWord_6496352, baseEnd_6496352] using wordTrace_append hprefix tailTrace_6496352
  have hstable : (prefixWord ++ tailWord_6496352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6496352).length < 2 ^ (prefixWord ++ tailWord_6496352).sum := by decide
  have hdescent : baseEnd_6496352 < baseStart_6496352 := by decide
  rcases family_descends (prefixWord ++ tailWord_6496352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6496378 : List Nat := [3, 1, 1, 1, 1, 1, 1, 1, 2, 2, 9]
def baseStart_6496378 : Nat := 118140960795 + 6496378 * 2 ^ 59
def prefixEnd_6496378 : Nat := 4983230072969 + 3 ^ 40 * 6496378 * 2
def baseEnd_6496378 : Nat := 3335764427294089124898707

theorem tailTrace_6496378 : CollatzResearch.WordTrace tailWord_6496378 prefixEnd_6496378 3335764427294089124898707 := by
  unfold tailWord_6496378
  simp only [CollatzResearch.WordTrace]
  refine ⟨59235592814684868469064447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157961580839159649250838525 59235592814684868469064447)
  ·
    refine ⟨88853389222027302703596671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59235592814684868469064447 88853389222027302703596671)
    ·
      refine ⟨133280083833040954055395007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88853389222027302703596671 133280083833040954055395007)
      ·
        refine ⟨199920125749561431083092511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133280083833040954055395007 199920125749561431083092511)
        ·
          refine ⟨299880188624342146624638767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199920125749561431083092511 299880188624342146624638767)
          ·
            refine ⟨449820282936513219936958151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 299880188624342146624638767 449820282936513219936958151)
            ·
              refine ⟨674730424404769829905437227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 449820282936513219936958151 674730424404769829905437227)
              ·
                refine ⟨1012095636607154744858155841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 674730424404769829905437227 1012095636607154744858155841)
                ·
                  refine ⟨759071727455366058643616881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1012095636607154744858155841 759071727455366058643616881)
                  ·
                    refine ⟨569303795591524543982712661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 759071727455366058643616881 569303795591524543982712661)
                    ·
                      refine ⟨3335764427294089124898707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 569303795591524543982712661 3335764427294089124898707)
                      ·
                        rfl

theorem cell23_6496378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 2, 2, 9].length) (baseStart_6496378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6496378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6496378 prefixEnd_6496378 := by exact prefixLift 6496378
  have htrace : WordTrace (prefixWord ++ tailWord_6496378) baseStart_6496378 baseEnd_6496378 := by
    simpa [prefixWord, tailWord_6496378, baseEnd_6496378] using wordTrace_append hprefix tailTrace_6496378
  have hstable : (prefixWord ++ tailWord_6496378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6496378).length < 2 ^ (prefixWord ++ tailWord_6496378).sum := by decide
  have hdescent : baseEnd_6496378 < baseStart_6496378 := by decide
  rcases family_descends (prefixWord ++ tailWord_6496378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6496404 : List Nat := [2, 4, 2, 3, 2, 1, 2, 2, 1, 2, 2]
def baseStart_6496404 : Nat := 118140960795 + 6496404 * 2 ^ 59
def prefixEnd_6496404 : Nat := 4983230072969 + 3 ^ 40 * 6496404 * 2
def baseEnd_6496404 : Nat := 3335777777791106023173589

theorem tailTrace_6496404 : CollatzResearch.WordTrace tailWord_6496404 prefixEnd_6496404 3335777777791106023173589 := by
  unfold tailWord_6496404
  simp only [CollatzResearch.WordTrace]
  refine ⟨118471659778322640158352133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157962213037763520211136177 118471659778322640158352133)
  ·
    refine ⟨22213436208435495029691025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 118471659778322640158352133 22213436208435495029691025)
    ·
      refine ⟨16660077156326621272268269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22213436208435495029691025 16660077156326621272268269)
      ·
        refine ⟨6247528933622482977100601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16660077156326621272268269 6247528933622482977100601)
        ·
          refine ⟨4685646700216862232825451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6247528933622482977100601 4685646700216862232825451)
          ·
            refine ⟨7028470050325293349238177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4685646700216862232825451 7028470050325293349238177)
            ·
              refine ⟨5271352537743970011928633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7028470050325293349238177 5271352537743970011928633)
              ·
                refine ⟨3953514403307977508946475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5271352537743970011928633 3953514403307977508946475)
                ·
                  refine ⟨5930271604961966263419713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3953514403307977508946475 5930271604961966263419713)
                  ·
                    refine ⟨4447703703721474697564785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5930271604961966263419713 4447703703721474697564785)
                    ·
                      refine ⟨3335777777791106023173589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4447703703721474697564785 3335777777791106023173589)
                      ·
                        rfl

theorem cell23_6496404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 2, 2, 1, 2, 2].length) (baseStart_6496404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6496404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6496404 prefixEnd_6496404 := by exact prefixLift 6496404
  have htrace : WordTrace (prefixWord ++ tailWord_6496404) baseStart_6496404 baseEnd_6496404 := by
    simpa [prefixWord, tailWord_6496404, baseEnd_6496404] using wordTrace_append hprefix tailTrace_6496404
  have hstable : (prefixWord ++ tailWord_6496404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6496404).length < 2 ^ (prefixWord ++ tailWord_6496404).sum := by decide
  have hdescent : baseEnd_6496404 < baseStart_6496404 := by decide
  rcases family_descends (prefixWord ++ tailWord_6496404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6496405 : List Nat := [1, 3, 2, 1, 1, 1, 4, 2, 2, 2, 4]
def baseStart_6496405 : Nat := 118140960795 + 6496405 * 2 ^ 59
def prefixEnd_6496405 : Nat := 4983230072969 + 3 ^ 40 * 6496405 * 2
def baseEnd_6496405 : Nat := 3335778291271760519261083

theorem tailTrace_6496405 : CollatzResearch.WordTrace tailWord_6496405 prefixEnd_6496405 3335778291271760519261083 := by
  unfold tailWord_6496405
  simp only [CollatzResearch.WordTrace]
  refine ⟨236943356029641657487490669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157962237353094438324993779 236943356029641657487490669)
  ·
    refine ⟨88853758511115621557809001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 236943356029641657487490669 88853758511115621557809001)
    ·
      refine ⟨66640318883336716168356751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88853758511115621557809001 66640318883336716168356751)
      ·
        refine ⟨99960478325005074252535127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66640318883336716168356751 99960478325005074252535127)
        ·
          refine ⟨149940717487507611378802691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99960478325005074252535127 149940717487507611378802691)
          ·
            refine ⟨224911076231261417068204037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149940717487507611378802691 224911076231261417068204037)
            ·
              refine ⟨42170826793361515700288257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 224911076231261417068204037 42170826793361515700288257)
              ·
                refine ⟨31628120095021136775216193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42170826793361515700288257 31628120095021136775216193)
                ·
                  refine ⟨23721090071265852581412145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31628120095021136775216193 23721090071265852581412145)
                  ·
                    refine ⟨17790817553449389436059109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23721090071265852581412145 17790817553449389436059109)
                    ·
                      refine ⟨3335778291271760519261083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17790817553449389436059109 3335778291271760519261083)
                      ·
                        rfl

theorem cell23_6496405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 2, 2, 2, 4].length) (baseStart_6496405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6496405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6496405 prefixEnd_6496405 := by exact prefixLift 6496405
  have htrace : WordTrace (prefixWord ++ tailWord_6496405) baseStart_6496405 baseEnd_6496405 := by
    simpa [prefixWord, tailWord_6496405, baseEnd_6496405] using wordTrace_append hprefix tailTrace_6496405
  have hstable : (prefixWord ++ tailWord_6496405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6496405).length < 2 ^ (prefixWord ++ tailWord_6496405).sum := by decide
  have hdescent : baseEnd_6496405 < baseStart_6496405 := by decide
  rcases family_descends (prefixWord ++ tailWord_6496405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6496460 : List Nat := [2, 2, 1, 6, 1, 2, 1, 2, 2, 2, 2]
def baseStart_6496460 : Nat := 118140960795 + 6496460 * 2 ^ 59
def prefixEnd_6496460 : Nat := 4983230072969 + 3 ^ 40 * 6496460 * 2
def baseEnd_6496460 : Nat := 3335806532707757804073331

theorem tailTrace_6496460 : CollatzResearch.WordTrace tailWord_6496460 prefixEnd_6496460 3335806532707757804073331 := by
  unfold tailWord_6496460
  simp only [CollatzResearch.WordTrace]
  refine ⟨118472681022221200940371417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157963574696294934587161889 118472681022221200940371417)
  ·
    refine ⟨88854510766665900705278563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118472681022221200940371417 88854510766665900705278563)
    ·
      refine ⟨133281766149998851057917845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88854510766665900705278563 133281766149998851057917845)
      ·
        refine ⟨6247582788281196143339899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 133281766149998851057917845 6247582788281196143339899)
        ·
          refine ⟨9371374182421794215009849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6247582788281196143339899 9371374182421794215009849)
          ·
            refine ⟨7028530636816345661257387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9371374182421794215009849 7028530636816345661257387)
            ·
              refine ⟨10542795955224518491886081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7028530636816345661257387 10542795955224518491886081)
              ·
                refine ⟨7907096966418388868914561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10542795955224518491886081 7907096966418388868914561)
                ·
                  refine ⟨5930322724813791651685921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7907096966418388868914561 5930322724813791651685921)
                  ·
                    refine ⟨4447742043610343738764441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5930322724813791651685921 4447742043610343738764441)
                    ·
                      refine ⟨3335806532707757804073331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4447742043610343738764441 3335806532707757804073331)
                      ·
                        rfl

theorem cell23_6496460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_6496460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6496460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6496460 prefixEnd_6496460 := by exact prefixLift 6496460
  have htrace : WordTrace (prefixWord ++ tailWord_6496460) baseStart_6496460 baseEnd_6496460 := by
    simpa [prefixWord, tailWord_6496460, baseEnd_6496460] using wordTrace_append hprefix tailTrace_6496460
  have hstable : (prefixWord ++ tailWord_6496460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6496460).length < 2 ^ (prefixWord ++ tailWord_6496460).sum := by decide
  have hdescent : baseEnd_6496460 < baseStart_6496460 := by decide
  rcases family_descends (prefixWord ++ tailWord_6496460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6496492 : List Nat := [2, 2, 1, 1, 2, 3, 1, 4, 3, 4]
def baseStart_6496492 : Nat := 118140960795 + 6496492 * 2 ^ 59
def prefixEnd_6496492 : Nat := 4983230072969 + 3 ^ 40 * 6496492 * 2
def baseEnd_6496492 : Nat := 1111940988029567226291061

theorem tailTrace_6496492 : CollatzResearch.WordTrace tailWord_6496492 prefixEnd_6496492 1111940988029567226291061 := by
  unfold tailWord_6496492
  simp only [CollatzResearch.WordTrace]
  refine ⟨118473264590163235672953865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157964352786884314230605153 118473264590163235672953865)
  ·
    refine ⟨88854948442622426754715399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118473264590163235672953865 88854948442622426754715399)
    ·
      refine ⟨133282422663933640132073099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88854948442622426754715399 133282422663933640132073099)
      ·
        refine ⟨199923633995900460198109649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133282422663933640132073099 199923633995900460198109649)
        ·
          refine ⟨149942725496925345148582237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 199923633995900460198109649 149942725496925345148582237)
          ·
            refine ⟨56228522061347004430718339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 149942725496925345148582237 56228522061347004430718339)
            ·
              refine ⟨84342783092020506646077509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56228522061347004430718339 84342783092020506646077509)
              ·
                refine ⟨15814271829753844996139533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 84342783092020506646077509 15814271829753844996139533)
                ·
                  refine ⟨5930351936157691873552325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15814271829753844996139533 5930351936157691873552325)
                  ·
                    refine ⟨1111940988029567226291061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5930351936157691873552325 1111940988029567226291061)
                    ·
                      rfl

theorem cell23_6496492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 4].length) (baseStart_6496492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6496492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6496492 prefixEnd_6496492 := by exact prefixLift 6496492
  have htrace : WordTrace (prefixWord ++ tailWord_6496492) baseStart_6496492 baseEnd_6496492 := by
    simpa [prefixWord, tailWord_6496492, baseEnd_6496492] using wordTrace_append hprefix tailTrace_6496492
  have hstable : (prefixWord ++ tailWord_6496492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6496492).length < 2 ^ (prefixWord ++ tailWord_6496492).sum := by decide
  have hdescent : baseEnd_6496492 < baseStart_6496492 := by decide
  rcases family_descends (prefixWord ++ tailWord_6496492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6496559 : List Nat := [1, 1, 2, 1, 2, 1, 5, 3, 2, 3, 2]
def baseStart_6496559 : Nat := 118140960795 + 6496559 * 2 ^ 59
def prefixEnd_6496559 : Nat := 4983230072969 + 3 ^ 40 * 6496559 * 2
def baseEnd_6496559 : Nat := 3335857367292552916735375

theorem tailTrace_6496559 : CollatzResearch.WordTrace tailWord_6496559 prefixEnd_6496559 3335857367292552916735375 := by
  unfold tailWord_6496559
  simp only [CollatzResearch.WordTrace]
  refine ⟨236948972871083741788596731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157965981914055827859064487 236948972871083741788596731)
  ·
    refine ⟨355423459306625612682895097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236948972871083741788596731 355423459306625612682895097)
    ·
      refine ⟨266567594479969209512171323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 355423459306625612682895097 266567594479969209512171323)
      ·
        refine ⟨399851391719953814268256985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266567594479969209512171323 399851391719953814268256985)
        ·
          refine ⟨299888543789965360701192739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 399851391719953814268256985 299888543789965360701192739)
          ·
            refine ⟨449832815684948041051789109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 299888543789965360701192739 449832815684948041051789109)
            ·
              refine ⟨42171826470463878848605229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 449832815684948041051789109 42171826470463878848605229)
              ·
                refine ⟨15814434926423954568226961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42171826470463878848605229 15814434926423954568226961)
                ·
                  refine ⟨11860826194817965926170221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15814434926423954568226961 11860826194817965926170221)
                  ·
                    refine ⟨4447809823056737222313833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11860826194817965926170221 4447809823056737222313833)
                    ·
                      refine ⟨3335857367292552916735375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4447809823056737222313833 3335857367292552916735375)
                      ·
                        rfl

theorem cell23_6496559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 3, 2, 3, 2].length) (baseStart_6496559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6496559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6496559 prefixEnd_6496559 := by exact prefixLift 6496559
  have htrace : WordTrace (prefixWord ++ tailWord_6496559) baseStart_6496559 baseEnd_6496559 := by
    simpa [prefixWord, tailWord_6496559, baseEnd_6496559] using wordTrace_append hprefix tailTrace_6496559
  have hstable : (prefixWord ++ tailWord_6496559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6496559).length < 2 ^ (prefixWord ++ tailWord_6496559).sum := by decide
  have hdescent : baseEnd_6496559 < baseStart_6496559 := by decide
  rcases family_descends (prefixWord ++ tailWord_6496559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6496577 : List Nat := [1, 2, 5, 2, 3, 1, 2, 2, 1, 4]
def baseStart_6496577 : Nat := 118140960795 + 6496577 * 2 ^ 59
def prefixEnd_6496577 : Nat := 4983230072969 + 3 ^ 40 * 6496577 * 2
def baseEnd_6496577 : Nat := 1111955536648111282103431

theorem tailTrace_6496577 : CollatzResearch.WordTrace tailWord_6496577 prefixEnd_6496577 1111955536648111282103431 := by
  unfold tailWord_6496577
  simp only [CollatzResearch.WordTrace]
  refine ⟨236949629385018530862751985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157966419590012353908501323 236949629385018530862751985)
  ·
    refine ⟨177712222038763898147063989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236949629385018530862751985 177712222038763898147063989)
    ·
      refine ⟨16660520816134115451287249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 177712222038763898147063989 16660520816134115451287249)
      ·
        refine ⟨12495390612100586588465437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16660520816134115451287249 12495390612100586588465437)
        ·
          refine ⟨4685771479537719970674539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12495390612100586588465437 4685771479537719970674539)
          ·
            refine ⟨7028657219306579956011809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4685771479537719970674539 7028657219306579956011809)
            ·
              refine ⟨5271492914479934967008857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7028657219306579956011809 5271492914479934967008857)
              ·
                refine ⟨3953619685859951225256643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5271492914479934967008857 3953619685859951225256643)
                ·
                  refine ⟨5930429528789926837884965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3953619685859951225256643 5930429528789926837884965)
                  ·
                    refine ⟨1111955536648111282103431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5930429528789926837884965 1111955536648111282103431)
                    ·
                      rfl

theorem cell23_6496577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 2, 2, 1, 4].length) (baseStart_6496577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6496577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6496577 prefixEnd_6496577 := by exact prefixLift 6496577
  have htrace : WordTrace (prefixWord ++ tailWord_6496577) baseStart_6496577 baseEnd_6496577 := by
    simpa [prefixWord, tailWord_6496577, baseEnd_6496577] using wordTrace_append hprefix tailTrace_6496577
  have hstable : (prefixWord ++ tailWord_6496577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6496577).length < 2 ^ (prefixWord ++ tailWord_6496577).sum := by decide
  have hdescent : baseEnd_6496577 < baseStart_6496577 := by decide
  rcases family_descends (prefixWord ++ tailWord_6496577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6496595 : List Nat := [1, 1, 1, 2, 1, 1, 4, 12]
def baseStart_6496595 : Nat := 118140960795 + 6496595 * 2 ^ 59
def prefixEnd_6496595 : Nat := 4983230072969 + 3 ^ 40 * 6496595 * 2
def baseEnd_6496595 : Nat := 123550957503559806514267

theorem tailTrace_6496595 : CollatzResearch.WordTrace tailWord_6496595 prefixEnd_6496595 123550957503559806514267 := by
  unfold tailWord_6496595
  simp only [CollatzResearch.WordTrace]
  refine ⟨236950285898953319936907239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157966857265968879957938159 236950285898953319936907239)
  ·
    refine ⟨355425428848429979905360859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236950285898953319936907239 355425428848429979905360859)
    ·
      refine ⟨533138143272644969858041289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 355425428848429979905360859 533138143272644969858041289)
      ·
        refine ⟨399853607454483727393530967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 533138143272644969858041289 399853607454483727393530967)
        ·
          refine ⟨599780411181725591090296451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 399853607454483727393530967 599780411181725591090296451)
          ·
            refine ⟨899670616772588386635444677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 599780411181725591090296451 899670616772588386635444677)
            ·
              refine ⟨168688240644860322494145877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 899670616772588386635444677 168688240644860322494145877)
              ·
                refine ⟨123550957503559806514267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 168688240644860322494145877 123550957503559806514267)
                ·
                  rfl

theorem cell23_6496595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 12].length) (baseStart_6496595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6496595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6496595 prefixEnd_6496595 := by exact prefixLift 6496595
  have htrace : WordTrace (prefixWord ++ tailWord_6496595) baseStart_6496595 baseEnd_6496595 := by
    simpa [prefixWord, tailWord_6496595, baseEnd_6496595] using wordTrace_append hprefix tailTrace_6496595
  have hstable : (prefixWord ++ tailWord_6496595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6496595).length < 2 ^ (prefixWord ++ tailWord_6496595).sum := by decide
  have hdescent : baseEnd_6496595 < baseStart_6496595 := by decide
  rcases family_descends (prefixWord ++ tailWord_6496595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6496599 : List Nat := [1, 1, 3, 2, 3, 1, 1, 5, 2, 4]
def baseStart_6496599 : Nat := 118140960795 + 6496599 * 2 ^ 59
def prefixEnd_6496599 : Nat := 4983230072969 + 3 ^ 40 * 6496599 * 2
def baseEnd_6496599 : Nat := 1111959302172910920078397

theorem tailTrace_6496599 : CollatzResearch.WordTrace tailWord_6496599 prefixEnd_6496599 1111959302172910920078397 := by
  unfold tailWord_6496599
  simp only [CollatzResearch.WordTrace]
  refine ⟨236950431790938828620052851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157966954527292552413368567 236950431790938828620052851)
  ·
    refine ⟨355425647686408242930079277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236950431790938828620052851 355425647686408242930079277)
    ·
      refine ⟨133284617882403091098779729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 355425647686408242930079277 133284617882403091098779729)
      ·
        refine ⟨99963463411802318324084797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133284617882403091098779729 99963463411802318324084797)
        ·
          refine ⟨37486298779425869371531799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99963463411802318324084797 37486298779425869371531799)
          ·
            refine ⟨56229448169138804057297699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37486298779425869371531799 56229448169138804057297699)
            ·
              refine ⟨84344172253708206085946549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56229448169138804057297699 84344172253708206085946549)
              ·
                refine ⟨7907266148785144320557489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 84344172253708206085946549 7907266148785144320557489)
                ·
                  refine ⟨5930449611588858240418117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7907266148785144320557489 5930449611588858240418117)
                  ·
                    refine ⟨1111959302172910920078397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5930449611588858240418117 1111959302172910920078397)
                    ·
                      rfl

theorem cell23_6496599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 5, 2, 4].length) (baseStart_6496599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6496599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6496599 prefixEnd_6496599 := by exact prefixLift 6496599
  have htrace : WordTrace (prefixWord ++ tailWord_6496599) baseStart_6496599 baseEnd_6496599 := by
    simpa [prefixWord, tailWord_6496599, baseEnd_6496599] using wordTrace_append hprefix tailTrace_6496599
  have hstable : (prefixWord ++ tailWord_6496599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6496599).length < 2 ^ (prefixWord ++ tailWord_6496599).sum := by decide
  have hdescent : baseEnd_6496599 < baseStart_6496599 := by decide
  rcases family_descends (prefixWord ++ tailWord_6496599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6496626 : List Nat := [3, 2, 1, 2, 1, 4, 1, 3, 1, 2, 3]
def baseStart_6496626 : Nat := 118140960795 + 6496626 * 2 ^ 59
def prefixEnd_6496626 : Nat := 4983230072969 + 3 ^ 40 * 6496626 * 2
def baseEnd_6496626 : Nat := 3335891770496404154597567

theorem tailTrace_6496626 : CollatzResearch.WordTrace tailWord_6496626 prefixEnd_6496626 3335891770496404154597567 := by
  unfold tailWord_6496626
  simp only [CollatzResearch.WordTrace]
  refine ⟨59237854140460253057821433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157967611041227341487523821 59237854140460253057821433)
  ·
    refine ⟨44428390605345189793366075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59237854140460253057821433 44428390605345189793366075)
    ·
      refine ⟨66642585908017784690049113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44428390605345189793366075 66642585908017784690049113)
      ·
        refine ⟨49981939431013338517536835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66642585908017784690049113 49981939431013338517536835)
        ·
          refine ⟨74972909146520007776305253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49981939431013338517536835 74972909146520007776305253)
          ·
            refine ⟨14057420464972501458057235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74972909146520007776305253 14057420464972501458057235)
            ·
              refine ⟨21086130697458752187085853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14057420464972501458057235 21086130697458752187085853)
              ·
                refine ⟨7907299011547032070157195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21086130697458752187085853 7907299011547032070157195)
                ·
                  refine ⟨11860948517320548105235793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7907299011547032070157195 11860948517320548105235793)
                  ·
                    refine ⟨8895711387990411078926845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11860948517320548105235793 8895711387990411078926845)
                    ·
                      refine ⟨3335891770496404154597567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8895711387990411078926845 3335891770496404154597567)
                      ·
                        rfl

theorem cell23_6496626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 3, 1, 2, 3].length) (baseStart_6496626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6496626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6496626 prefixEnd_6496626 := by exact prefixLift 6496626
  have htrace : WordTrace (prefixWord ++ tailWord_6496626) baseStart_6496626 baseEnd_6496626 := by
    simpa [prefixWord, tailWord_6496626, baseEnd_6496626] using wordTrace_append hprefix tailTrace_6496626
  have hstable : (prefixWord ++ tailWord_6496626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6496626).length < 2 ^ (prefixWord ++ tailWord_6496626).sum := by decide
  have hdescent : baseEnd_6496626 < baseStart_6496626 := by decide
  rcases family_descends (prefixWord ++ tailWord_6496626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6496639 : List Nat := [1, 1, 2, 2, 1, 1, 2, 5, 4, 1, 3]
def baseStart_6496639 : Nat := 118140960795 + 6496639 * 2 ^ 59
def prefixEnd_6496639 : Nat := 4983230072969 + 3 ^ 40 * 6496639 * 2
def baseEnd_6496639 : Nat := 3335898445744912603735007

theorem tailTrace_6496639 : CollatzResearch.WordTrace tailWord_6496639 prefixEnd_6496639 3335898445744912603735007 := by
  unfold tailWord_6496639
  simp only [CollatzResearch.WordTrace]
  refine ⟨236951890710793915451508971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157967927140529276967672647 236951890710793915451508971)
  ·
    refine ⟨355427836066190873177263457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236951890710793915451508971 355427836066190873177263457)
    ·
      refine ⟨266570877049643154882947593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 355427836066190873177263457 266570877049643154882947593)
      ·
        refine ⟨199928157787232366162210695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 266570877049643154882947593 199928157787232366162210695)
        ·
          refine ⟨299892236680848549243316043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199928157787232366162210695 299892236680848549243316043)
          ·
            refine ⟨449838355021272823864974065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 299892236680848549243316043 449838355021272823864974065)
            ·
              refine ⟨337378766265954617898730549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 449838355021272823864974065 337378766265954617898730549)
              ·
                refine ⟨31629259337433245428005989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 337378766265954617898730549 31629259337433245428005989)
                ·
                  refine ⟨5930486125768733517751123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31629259337433245428005989 5930486125768733517751123)
                  ·
                    refine ⟨8895729188653100276626685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5930486125768733517751123 8895729188653100276626685)
                    ·
                      refine ⟨3335898445744912603735007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8895729188653100276626685 3335898445744912603735007)
                      ·
                        rfl

theorem cell23_6496639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 5, 4, 1, 3].length) (baseStart_6496639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6496639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6496639 prefixEnd_6496639 := by exact prefixLift 6496639
  have htrace : WordTrace (prefixWord ++ tailWord_6496639) baseStart_6496639 baseEnd_6496639 := by
    simpa [prefixWord, tailWord_6496639, baseEnd_6496639] using wordTrace_append hprefix tailTrace_6496639
  have hstable : (prefixWord ++ tailWord_6496639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6496639).length < 2 ^ (prefixWord ++ tailWord_6496639).sum := by decide
  have hdescent : baseEnd_6496639 < baseStart_6496639 := by decide
  rcases family_descends (prefixWord ++ tailWord_6496639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6496650 : List Nat := [3, 1, 2, 5, 1, 1, 3, 1, 2, 4]
def baseStart_6496650 : Nat := 118140960795 + 6496650 * 2 ^ 59
def prefixEnd_6496650 : Nat := 4983230072969 + 3 ^ 40 * 6496650 * 2
def baseEnd_6496650 : Nat := 1111968031344037353565819

theorem tailTrace_6496650 : CollatzResearch.WordTrace tailWord_6496650 prefixEnd_6496650 1111968031344037353565819 := by
  unfold tailWord_6496650
  simp only [CollatzResearch.WordTrace]
  refine ⟨59238072978438516082539851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157968194609169376220106269 59238072978438516082539851)
  ·
    refine ⟨88857109467657774123809777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59238072978438516082539851 88857109467657774123809777)
    ·
      refine ⟨66642832100743330592857333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88857109467657774123809777 66642832100743330592857333)
      ·
        refine ⟨6247765509444687243080375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 66642832100743330592857333 6247765509444687243080375)
        ·
          refine ⟨9371648264167030864620563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6247765509444687243080375 9371648264167030864620563)
          ·
            refine ⟨14057472396250546296930845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9371648264167030864620563 14057472396250546296930845)
            ·
              refine ⟨5271552148593954861349067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14057472396250546296930845 5271552148593954861349067)
              ·
                refine ⟨7907328222890932292023601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5271552148593954861349067 7907328222890932292023601)
                ·
                  refine ⟨5930496167168199219017701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7907328222890932292023601 5930496167168199219017701)
                  ·
                    refine ⟨1111968031344037353565819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5930496167168199219017701 1111968031344037353565819)
                    ·
                      rfl

theorem cell23_6496650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 3, 1, 2, 4].length) (baseStart_6496650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6496650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6496650 prefixEnd_6496650 := by exact prefixLift 6496650
  have htrace : WordTrace (prefixWord ++ tailWord_6496650) baseStart_6496650 baseEnd_6496650 := by
    simpa [prefixWord, tailWord_6496650, baseEnd_6496650] using wordTrace_append hprefix tailTrace_6496650
  have hstable : (prefixWord ++ tailWord_6496650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6496650).length < 2 ^ (prefixWord ++ tailWord_6496650).sum := by decide
  have hdescent : baseEnd_6496650 < baseStart_6496650 := by decide
  rcases family_descends (prefixWord ++ tailWord_6496650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6496856 : List Nat := [2, 1, 2, 2, 1, 2, 4, 3, 1, 5]
def baseStart_6496856 : Nat := 118140960795 + 6496856 * 2 ^ 59
def prefixEnd_6496856 : Nat := 4983230072969 + 3 ^ 40 * 6496856 * 2
def baseEnd_6496856 : Nat := 1112003290348979418240503

theorem tailTrace_6496856 : CollatzResearch.WordTrace tailWord_6496856 prefixEnd_6496856 1112003290348979418240503 := by
  unfold tailWord_6496856
  simp only [CollatzResearch.WordTrace]
  refine ⟨118479902675503880756079211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157973203567338507674772281 118479902675503880756079211)
  ·
    refine ⟨177719854013255821134118817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118479902675503880756079211 177719854013255821134118817)
    ·
      refine ⟨133289890509941865850589113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177719854013255821134118817 133289890509941865850589113)
      ·
        refine ⟨99967417882456399387941835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133289890509941865850589113 99967417882456399387941835)
        ·
          refine ⟨149951126823684599081912753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99967417882456399387941835 149951126823684599081912753)
          ·
            refine ⟨112463345117763449311434565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149951126823684599081912753 112463345117763449311434565)
            ·
              refine ⟨21086877209580646745893981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 112463345117763449311434565 21086877209580646745893981)
              ·
                refine ⟨7907578953592742529710243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21086877209580646745893981 7907578953592742529710243)
                ·
                  refine ⟨11861368430389113794565365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7907578953592742529710243 11861368430389113794565365)
                  ·
                    refine ⟨1112003290348979418240503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11861368430389113794565365 1112003290348979418240503)
                    ·
                      rfl

theorem cell23_6496856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 3, 1, 5].length) (baseStart_6496856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6496856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6496856 prefixEnd_6496856 := by exact prefixLift 6496856
  have htrace : WordTrace (prefixWord ++ tailWord_6496856) baseStart_6496856 baseEnd_6496856 := by
    simpa [prefixWord, tailWord_6496856, baseEnd_6496856] using wordTrace_append hprefix tailTrace_6496856
  have hstable : (prefixWord ++ tailWord_6496856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6496856).length < 2 ^ (prefixWord ++ tailWord_6496856).sum := by decide
  have hdescent : baseEnd_6496856 < baseStart_6496856 := by decide
  rcases family_descends (prefixWord ++ tailWord_6496856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6496893 : List Nat := [1, 4, 1, 1, 5, 1, 1, 1, 3, 1, 4]
def baseStart_6496893 : Nat := 118140960795 + 6496893 * 2 ^ 59
def prefixEnd_6496893 : Nat := 4983230072969 + 3 ^ 40 * 6496893 * 2
def baseEnd_6496893 : Nat := 3336028869831154609958839

theorem tailTrace_6496893 : CollatzResearch.WordTrace tailWord_6496893 prefixEnd_6496893 3336028869831154609958839 := by
  unfold tailWord_6496893
  simp only [CollatzResearch.WordTrace]
  refine ⟨236961154851873716831255333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157974103234582477887503555 236961154851873716831255333)
  ·
    refine ⟨44430216534726321905860375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 236961154851873716831255333 44430216534726321905860375)
    ·
      refine ⟨66645324802089482858790563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44430216534726321905860375 66645324802089482858790563)
      ·
        refine ⟨99967987203134224288185845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66645324802089482858790563 99967987203134224288185845)
        ·
          refine ⟨9371998800293833527017423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 99967987203134224288185845 9371998800293833527017423)
          ·
            refine ⟨14057998200440750290526135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9371998800293833527017423 14057998200440750290526135)
            ·
              refine ⟨21086997300661125435789203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14057998200440750290526135 21086997300661125435789203)
              ·
                refine ⟨31630495950991688153683805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21086997300661125435789203 31630495950991688153683805)
                ·
                  refine ⟨11861435981621883057631427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31630495950991688153683805 11861435981621883057631427)
                  ·
                    refine ⟨17792153972432824586447141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11861435981621883057631427 17792153972432824586447141)
                    ·
                      refine ⟨3336028869831154609958839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17792153972432824586447141 3336028869831154609958839)
                      ·
                        rfl

theorem cell23_6496893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 1, 3, 1, 4].length) (baseStart_6496893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6496893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6496893 prefixEnd_6496893 := by exact prefixLift 6496893
  have htrace : WordTrace (prefixWord ++ tailWord_6496893) baseStart_6496893 baseEnd_6496893 := by
    simpa [prefixWord, tailWord_6496893, baseEnd_6496893] using wordTrace_append hprefix tailTrace_6496893
  have hstable : (prefixWord ++ tailWord_6496893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6496893).length < 2 ^ (prefixWord ++ tailWord_6496893).sum := by decide
  have hdescent : baseEnd_6496893 < baseStart_6496893 := by decide
  rcases family_descends (prefixWord ++ tailWord_6496893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6496899 : List Nat := [1, 1, 1, 3, 3, 1, 4, 9]
def baseStart_6496899 : Nat := 118140960795 + 6496899 * 2 ^ 59
def prefixEnd_6496899 : Nat := 4983230072969 + 3 ^ 40 * 6496899 * 2
def baseEnd_6496899 : Nat := 123556738915373392091993

theorem tailTrace_6496899 : CollatzResearch.WordTrace tailWord_6496899 prefixEnd_6496899 123556738915373392091993 := by
  unfold tailWord_6496899
  simp only [CollatzResearch.WordTrace]
  refine ⟨236961373689851979855973751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157974249126567986570649167 236961373689851979855973751)
  ·
    refine ⟨355442060534777969783960627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236961373689851979855973751 355442060534777969783960627)
    ·
      refine ⟨533163090802166954675940941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 355442060534777969783960627 533163090802166954675940941)
      ·
        refine ⟨199936159050812608003477853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 533163090802166954675940941 199936159050812608003477853)
        ·
          refine ⟨74976059644054728001304195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 199936159050812608003477853 74976059644054728001304195)
          ·
            refine ⟨112464089466082092001956293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74976059644054728001304195 112464089466082092001956293)
            ·
              refine ⟨21087016774890392250366805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 112464089466082092001956293 21087016774890392250366805)
              ·
                refine ⟨123556738915373392091993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21087016774890392250366805 123556738915373392091993)
                ·
                  rfl

theorem cell23_6496899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 9].length) (baseStart_6496899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6496899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6496899 prefixEnd_6496899 := by exact prefixLift 6496899
  have htrace : WordTrace (prefixWord ++ tailWord_6496899) baseStart_6496899 baseEnd_6496899 := by
    simpa [prefixWord, tailWord_6496899, baseEnd_6496899] using wordTrace_append hprefix tailTrace_6496899
  have hstable : (prefixWord ++ tailWord_6496899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6496899).length < 2 ^ (prefixWord ++ tailWord_6496899).sum := by decide
  have hdescent : baseEnd_6496899 < baseStart_6496899 := by decide
  rcases family_descends (prefixWord ++ tailWord_6496899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6496910 : List Nat := [4, 1, 1, 3, 1, 1, 5, 1, 1, 1, 4]
def baseStart_6496910 : Nat := 118140960795 + 6496910 * 2 ^ 59
def prefixEnd_6496910 : Nat := 4983230072969 + 3 ^ 40 * 6496910 * 2
def baseEnd_6496910 : Nat := 3336037599002281043446261

theorem tailTrace_6496910 : CollatzResearch.WordTrace tailWord_6496910 prefixEnd_6496910 3336037599002281043446261 := by
  unfold tailWord_6496910
  simp only [CollatzResearch.WordTrace]
  refine ⟨29620221861601516091828023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157974516595208085823082789 29620221861601516091828023)
  ·
    refine ⟨44430332792402274137742035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29620221861601516091828023 44430332792402274137742035)
    ·
      refine ⟨66645499188603411206613053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44430332792402274137742035 66645499188603411206613053)
      ·
        refine ⟨24992062195726279202479895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66645499188603411206613053 24992062195726279202479895)
        ·
          refine ⟨37488093293589418803719843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24992062195726279202479895 37488093293589418803719843)
          ·
            refine ⟨56232139940384128205579765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37488093293589418803719843 56232139940384128205579765)
            ·
              refine ⟨5271763119411012019273103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56232139940384128205579765 5271763119411012019273103)
              ·
                refine ⟨7907644679116518028909655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5271763119411012019273103 7907644679116518028909655)
                ·
                  refine ⟨11861467018674777043364483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7907644679116518028909655 11861467018674777043364483)
                  ·
                    refine ⟨17792200528012165565046725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11861467018674777043364483 17792200528012165565046725)
                    ·
                      refine ⟨3336037599002281043446261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17792200528012165565046725 3336037599002281043446261)
                      ·
                        rfl

theorem cell23_6496910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 5, 1, 1, 1, 4].length) (baseStart_6496910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6496910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6496910 prefixEnd_6496910 := by exact prefixLift 6496910
  have htrace : WordTrace (prefixWord ++ tailWord_6496910) baseStart_6496910 baseEnd_6496910 := by
    simpa [prefixWord, tailWord_6496910, baseEnd_6496910] using wordTrace_append hprefix tailTrace_6496910
  have hstable : (prefixWord ++ tailWord_6496910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6496910).length < 2 ^ (prefixWord ++ tailWord_6496910).sum := by decide
  have hdescent : baseEnd_6496910 < baseStart_6496910 := by decide
  rcases family_descends (prefixWord ++ tailWord_6496910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6496916 : List Nat := [2, 4, 2, 2, 1, 12]
def baseStart_6496916 : Nat := 118140960795 + 6496916 * 2 ^ 59
def prefixEnd_6496916 : Nat := 4983230072969 + 3 ^ 40 * 6496916 * 2
def baseEnd_6496916 : Nat := 13728562468667522715931

theorem tailTrace_6496916 : CollatzResearch.WordTrace tailWord_6496916 prefixEnd_6496916 13728562468667522715931 := by
  unfold tailWord_6496916
  simp only [CollatzResearch.WordTrace]
  refine ⟨118480996865395195879671301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157974662487193594506228401 118480996865395195879671301)
  ·
    refine ⟨22215186912261599227438369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 118480996865395195879671301 22215186912261599227438369)
    ·
      refine ⟨16661390184196199420578777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22215186912261599227438369 16661390184196199420578777)
      ·
        refine ⟨12496042638147149565434083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16661390184196199420578777 12496042638147149565434083)
        ·
          refine ⟨18744063957220724348151125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12496042638147149565434083 18744063957220724348151125)
          ·
            refine ⟨13728562468667522715931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 18744063957220724348151125 13728562468667522715931)
            ·
              rfl

theorem cell23_6496916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 12].length) (baseStart_6496916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6496916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6496916 prefixEnd_6496916 := by exact prefixLift 6496916
  have htrace : WordTrace (prefixWord ++ tailWord_6496916) baseStart_6496916 baseEnd_6496916 := by
    simpa [prefixWord, tailWord_6496916, baseEnd_6496916] using wordTrace_append hprefix tailTrace_6496916
  have hstable : (prefixWord ++ tailWord_6496916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6496916).length < 2 ^ (prefixWord ++ tailWord_6496916).sum := by decide
  have hdescent : baseEnd_6496916 < baseStart_6496916 := by decide
  rcases family_descends (prefixWord ++ tailWord_6496916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6496943 : List Nat := [1, 1, 2, 1, 2, 6, 2, 1, 1, 3, 3]
def baseStart_6496943 : Nat := 118140960795 + 6496943 * 2 ^ 59
def prefixEnd_6496943 : Nat := 4983230072969 + 3 ^ 40 * 6496943 * 2
def baseEnd_6496943 : Nat := 3336054543863879414333609

theorem tailTrace_6496943 : CollatzResearch.WordTrace tailWord_6496943 prefixEnd_6496943 3336054543863879414333609 := by
  unfold tailWord_6496943
  simp only [CollatzResearch.WordTrace]
  refine ⟨236962978501692575370575483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157975319001128383580383655 236962978501692575370575483)
  ·
    refine ⟨355444467752538863055863225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236962978501692575370575483 355444467752538863055863225)
    ·
      refine ⟨266583350814404147291897419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 355444467752538863055863225 266583350814404147291897419)
      ·
        refine ⟨399875026221606220937846129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266583350814404147291897419 399875026221606220937846129)
        ·
          refine ⟨299906269666204665703384597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 399875026221606220937846129 299906269666204665703384597)
          ·
            refine ⟨14058106390603343704846153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 299906269666204665703384597 14058106390603343704846153)
            ·
              refine ⟨10543579792952507778634615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14058106390603343704846153 10543579792952507778634615)
              ·
                refine ⟨15815369689428761667951923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10543579792952507778634615 15815369689428761667951923)
                ·
                  refine ⟨23723054534143142501927885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15815369689428761667951923 23723054534143142501927885)
                  ·
                    refine ⟨8896145450303678438222957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23723054534143142501927885 8896145450303678438222957)
                    ·
                      refine ⟨3336054543863879414333609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8896145450303678438222957 3336054543863879414333609)
                      ·
                        rfl

theorem cell23_6496943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 2, 1, 1, 3, 3].length) (baseStart_6496943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6496943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6496943 prefixEnd_6496943 := by exact prefixLift 6496943
  have htrace : WordTrace (prefixWord ++ tailWord_6496943) baseStart_6496943 baseEnd_6496943 := by
    simpa [prefixWord, tailWord_6496943, baseEnd_6496943] using wordTrace_append hprefix tailTrace_6496943
  have hstable : (prefixWord ++ tailWord_6496943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6496943).length < 2 ^ (prefixWord ++ tailWord_6496943).sum := by decide
  have hdescent : baseEnd_6496943 < baseStart_6496943 := by decide
  rcases family_descends (prefixWord ++ tailWord_6496943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6496956 : List Nat := [2, 2, 2, 3, 1, 1, 2, 1, 2, 2, 5]
def baseStart_6496956 : Nat := 118140960795 + 6496956 * 2 ^ 59
def prefixEnd_6496956 : Nat := 4983230072969 + 3 ^ 40 * 6496956 * 2
def baseEnd_6496956 : Nat := 3336061219112387863471049

theorem tailTrace_6496956 : CollatzResearch.WordTrace tailWord_6496956 prefixEnd_6496956 3336061219112387863471049 := by
  unfold tailWord_6496956
  simp only [CollatzResearch.WordTrace]
  refine ⟨118481726325322739295399361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157975635100430319060532481 118481726325322739295399361)
  ·
    refine ⟨88861294743992054471549521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118481726325322739295399361 88861294743992054471549521)
    ·
      refine ⟨66645971057994040853662141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88861294743992054471549521 66645971057994040853662141)
      ·
        refine ⟨24992239146747765320123303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66645971057994040853662141 24992239146747765320123303)
        ·
          refine ⟨37488358720121647980184955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24992239146747765320123303 37488358720121647980184955)
          ·
            refine ⟨56232538080182471970277433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37488358720121647980184955 56232538080182471970277433)
            ·
              refine ⟨42174403560136853977708075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56232538080182471970277433 42174403560136853977708075)
              ·
                refine ⟨63261605340205280966562113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42174403560136853977708075 63261605340205280966562113)
                ·
                  refine ⟨47446204005153960724921585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63261605340205280966562113 47446204005153960724921585)
                  ·
                    refine ⟨35584653003865470543691189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47446204005153960724921585 35584653003865470543691189)
                    ·
                      refine ⟨3336061219112387863471049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35584653003865470543691189 3336061219112387863471049)
                      ·
                        rfl

theorem cell23_6496956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_6496956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6496956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6496956 prefixEnd_6496956 := by exact prefixLift 6496956
  have htrace : WordTrace (prefixWord ++ tailWord_6496956) baseStart_6496956 baseEnd_6496956 := by
    simpa [prefixWord, tailWord_6496956, baseEnd_6496956] using wordTrace_append hprefix tailTrace_6496956
  have hstable : (prefixWord ++ tailWord_6496956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6496956).length < 2 ^ (prefixWord ++ tailWord_6496956).sum := by decide
  have hdescent : baseEnd_6496956 < baseStart_6496956 := by decide
  rcases family_descends (prefixWord ++ tailWord_6496956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6496961 : List Nat := [1, 2, 6, 2, 2, 1, 2, 1, 1, 1, 4]
def baseStart_6496961 : Nat := 118140960795 + 6496961 * 2 ^ 59
def prefixEnd_6496961 : Nat := 4983230072969 + 3 ^ 40 * 6496961 * 2
def baseEnd_6496961 : Nat := 3336063786515660343908527

theorem tailTrace_6496961 : CollatzResearch.WordTrace tailWord_6496961 prefixEnd_6496961 3336063786515660343908527 := by
  unfold tailWord_6496961
  simp only [CollatzResearch.WordTrace]
  refine ⟨236963635015627364444730737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157975756677084909629820491 236963635015627364444730737)
  ·
    refine ⟨177722726261720523333548053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236963635015627364444730737 177722726261720523333548053)
    ·
      refine ⟨8330752793518149531260065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 177722726261720523333548053 8330752793518149531260065)
      ·
        refine ⟨6248064595138612148445049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8330752793518149531260065 6248064595138612148445049)
        ·
          refine ⟨4686048446353959111333787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6248064595138612148445049 4686048446353959111333787)
          ·
            refine ⟨7029072669530938667000681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4686048446353959111333787 7029072669530938667000681)
            ·
              refine ⟨5271804502148204000250511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7029072669530938667000681 5271804502148204000250511)
              ·
                refine ⟨7907706753222306000375767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5271804502148204000250511 7907706753222306000375767)
                ·
                  refine ⟨11861560129833459000563651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7907706753222306000375767 11861560129833459000563651)
                  ·
                    refine ⟨17792340194750188500845477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11861560129833459000563651 17792340194750188500845477)
                    ·
                      refine ⟨3336063786515660343908527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17792340194750188500845477 3336063786515660343908527)
                      ·
                        rfl

theorem cell23_6496961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_6496961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6496961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6496961 prefixEnd_6496961 := by exact prefixLift 6496961
  have htrace : WordTrace (prefixWord ++ tailWord_6496961) baseStart_6496961 baseEnd_6496961 := by
    simpa [prefixWord, tailWord_6496961, baseEnd_6496961] using wordTrace_append hprefix tailTrace_6496961
  have hstable : (prefixWord ++ tailWord_6496961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6496961).length < 2 ^ (prefixWord ++ tailWord_6496961).sum := by decide
  have hdescent : baseEnd_6496961 < baseStart_6496961 := by decide
  rcases family_descends (prefixWord ++ tailWord_6496961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6497043 : List Nat := [1, 1, 1, 2, 1, 3, 4, 1, 2, 5, 2]
def baseStart_6497043 : Nat := 118140960795 + 6497043 * 2 ^ 59
def prefixEnd_6497043 : Nat := 4983230072969 + 3 ^ 40 * 6497043 * 2
def baseEnd_6497043 : Nat := 3336105891929329023083149

theorem tailTrace_6497043 : CollatzResearch.WordTrace tailWord_6497043 prefixEnd_6497043 3336105891929329023083149 := by
  unfold tailWord_6497043
  simp only [CollatzResearch.WordTrace]
  refine ⟨236966625801330292449215783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157977750534220194966143855 236966625801330292449215783)
  ·
    refine ⟨355449938701995438673823675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236966625801330292449215783 355449938701995438673823675)
    ·
      refine ⟨533174908052993158010735513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 355449938701995438673823675 533174908052993158010735513)
      ·
        refine ⟨399881181039744868508051635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 533174908052993158010735513 399881181039744868508051635)
        ·
          refine ⟨599821771559617302762077453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 399881181039744868508051635 599821771559617302762077453)
          ·
            refine ⟨224933164334856488535779045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 599821771559617302762077453 224933164334856488535779045)
            ·
              refine ⟨42174968312785591600458571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 224933164334856488535779045 42174968312785591600458571)
              ·
                refine ⟨63262452469178387400687857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42174968312785591600458571 63262452469178387400687857)
                ·
                  refine ⟨47446839351883790550515893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63262452469178387400687857 47446839351883790550515893)
                  ·
                    refine ⟨4448141189239105364110865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47446839351883790550515893 4448141189239105364110865)
                    ·
                      refine ⟨3336105891929329023083149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4448141189239105364110865 3336105891929329023083149)
                      ·
                        rfl

theorem cell23_6497043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 1, 2, 5, 2].length) (baseStart_6497043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6497043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6497043 prefixEnd_6497043 := by exact prefixLift 6497043
  have htrace : WordTrace (prefixWord ++ tailWord_6497043) baseStart_6497043 baseEnd_6497043 := by
    simpa [prefixWord, tailWord_6497043, baseEnd_6497043] using wordTrace_append hprefix tailTrace_6497043
  have hstable : (prefixWord ++ tailWord_6497043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6497043).length < 2 ^ (prefixWord ++ tailWord_6497043).sum := by decide
  have hdescent : baseEnd_6497043 < baseStart_6497043 := by decide
  rcases family_descends (prefixWord ++ tailWord_6497043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6497070 : List Nat := [4, 1, 3, 2, 1, 1, 1, 3, 2, 5]
def baseStart_6497070 : Nat := 118140960795 + 6497070 * 2 ^ 59
def prefixEnd_6497070 : Nat := 4983230072969 + 3 ^ 40 * 6497070 * 2
def baseEnd_6497070 : Nat := 1112039918635666805815175

theorem tailTrace_6497070 : CollatzResearch.WordTrace tailWord_6497070 prefixEnd_6497070 1112039918635666805815175 := by
  unfold tailWord_6497070
  simp only [CollatzResearch.WordTrace]
  refine ⟨29620951321529059507556083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157978407048154984040299109 29620951321529059507556083)
  ·
    refine ⟨44431426982293589261334125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29620951321529059507556083 44431426982293589261334125)
    ·
      refine ⟨16661785118360095973000297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44431426982293589261334125 16661785118360095973000297)
      ·
        refine ⟨12496338838770071979750223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16661785118360095973000297 12496338838770071979750223)
        ·
          refine ⟨18744508258155107969625335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12496338838770071979750223 18744508258155107969625335)
          ·
            refine ⟨28116762387232661954438003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18744508258155107969625335 28116762387232661954438003)
            ·
              refine ⟨42175143580848992931657005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28116762387232661954438003 42175143580848992931657005)
              ·
                refine ⟨15815678842818372349371377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42175143580848992931657005 15815678842818372349371377)
                ·
                  refine ⟨11861759132113779262028533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15815678842818372349371377 11861759132113779262028533)
                  ·
                    refine ⟨1112039918635666805815175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11861759132113779262028533 1112039918635666805815175)
                    ·
                      rfl

theorem cell23_6497070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 3, 2, 5].length) (baseStart_6497070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6497070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6497070 prefixEnd_6497070 := by exact prefixLift 6497070
  have htrace : WordTrace (prefixWord ++ tailWord_6497070) baseStart_6497070 baseEnd_6497070 := by
    simpa [prefixWord, tailWord_6497070, baseEnd_6497070] using wordTrace_append hprefix tailTrace_6497070
  have hstable : (prefixWord ++ tailWord_6497070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6497070).length < 2 ^ (prefixWord ++ tailWord_6497070).sum := by decide
  have hdescent : baseEnd_6497070 < baseStart_6497070 := by decide
  rcases family_descends (prefixWord ++ tailWord_6497070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6497093 : List Nat := [1, 3, 1, 1, 1, 2, 2, 3, 4, 2, 3]
def baseStart_6497093 : Nat := 118140960795 + 6497093 * 2 ^ 59
def prefixEnd_6497093 : Nat := 4983230072969 + 3 ^ 40 * 6497093 * 2
def baseEnd_6497093 : Nat := 3336131565962053827457919

theorem tailTrace_6497093 : CollatzResearch.WordTrace tailWord_6497093 prefixEnd_6497093 3336131565962053827457919 := by
  unfold tailWord_6497093
  simp only [CollatzResearch.WordTrace]
  refine ⟨236968449451149150988535933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157978966300766100659023955 236968449451149150988535933)
  ·
    refine ⟨88863168544180931620700975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 236968449451149150988535933 88863168544180931620700975)
    ·
      refine ⟨133294752816271397431051463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88863168544180931620700975 133294752816271397431051463)
      ·
        refine ⟨199942129224407096146577195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133294752816271397431051463 199942129224407096146577195)
        ·
          refine ⟨299913193836610644219865793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199942129224407096146577195 299913193836610644219865793)
          ·
            refine ⟨224934895377457983164899345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 299913193836610644219865793 224934895377457983164899345)
            ·
              refine ⟨168701171533093487373674509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 224934895377457983164899345 168701171533093487373674509)
              ·
                refine ⟨63262939324910057765127941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 168701171533093487373674509 63262939324910057765127941)
                ·
                  refine ⟨11861801123420635830961489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63262939324910057765127941 11861801123420635830961489)
                  ·
                    refine ⟨8896350842565476873221117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11861801123420635830961489 8896350842565476873221117)
                    ·
                      refine ⟨3336131565962053827457919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8896350842565476873221117 3336131565962053827457919)
                      ·
                        rfl

theorem cell23_6497093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 3, 4, 2, 3].length) (baseStart_6497093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6497093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6497093 prefixEnd_6497093 := by exact prefixLift 6497093
  have htrace : WordTrace (prefixWord ++ tailWord_6497093) baseStart_6497093 baseEnd_6497093 := by
    simpa [prefixWord, tailWord_6497093, baseEnd_6497093] using wordTrace_append hprefix tailTrace_6497093
  have hstable : (prefixWord ++ tailWord_6497093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6497093).length < 2 ^ (prefixWord ++ tailWord_6497093).sum := by decide
  have hdescent : baseEnd_6497093 < baseStart_6497093 := by decide
  rcases family_descends (prefixWord ++ tailWord_6497093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6497113 : List Nat := [1, 2, 1, 2, 2, 4, 2, 3, 6]
def baseStart_6497113 : Nat := 118140960795 + 6497113 * 2 ^ 59
def prefixEnd_6497113 : Nat := 4983230072969 + 3 ^ 40 * 6497113 * 2
def baseEnd_6497113 : Nat := 370682426175015972134203

theorem tailTrace_6497113 : CollatzResearch.WordTrace tailWord_6497113 prefixEnd_6497113 370682426175015972134203 := by
  unfold tailWord_6497113
  simp only [CollatzResearch.WordTrace]
  refine ⟨236969178911076694404263993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157979452607384462936175995 236969178911076694404263993)
  ·
    refine ⟨177726884183307520803197995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236969178911076694404263993 177726884183307520803197995)
    ·
      refine ⟨266590326274961281204796993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177726884183307520803197995 266590326274961281204796993)
      ·
        refine ⟨199942744706220960903597745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 266590326274961281204796993 199942744706220960903597745)
        ·
          refine ⟨149957058529665720677698309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 199942744706220960903597745 149957058529665720677698309)
          ·
            refine ⟨28116948474312322627068433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 149957058529665720677698309 28116948474312322627068433)
            ·
              refine ⟨21087711355734241970301325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28116948474312322627068433 21087711355734241970301325)
              ·
                refine ⟨7907891758400340738862997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21087711355734241970301325 7907891758400340738862997)
                ·
                  refine ⟨370682426175015972134203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7907891758400340738862997 370682426175015972134203)
                  ·
                    rfl

theorem cell23_6497113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 3, 6].length) (baseStart_6497113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6497113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6497113 prefixEnd_6497113 := by exact prefixLift 6497113
  have htrace : WordTrace (prefixWord ++ tailWord_6497113) baseStart_6497113 baseEnd_6497113 := by
    simpa [prefixWord, tailWord_6497113, baseEnd_6497113] using wordTrace_append hprefix tailTrace_6497113
  have hstable : (prefixWord ++ tailWord_6497113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6497113).length < 2 ^ (prefixWord ++ tailWord_6497113).sum := by decide
  have hdescent : baseEnd_6497113 < baseStart_6497113 := by decide
  rcases family_descends (prefixWord ++ tailWord_6497113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6497127 : List Nat := [1, 1, 5, 1, 2, 4, 1, 1, 2, 2, 3]
def baseStart_6497127 : Nat := 118140960795 + 6497127 * 2 ^ 59
def prefixEnd_6497127 : Nat := 4983230072969 + 3 ^ 40 * 6497127 * 2
def baseEnd_6497127 : Nat := 3336149024304306694432763

theorem tailTrace_6497127 : CollatzResearch.WordTrace tailWord_6497127 prefixEnd_6497127 3336149024304306694432763 := by
  unfold tailWord_6497127
  simp only [CollatzResearch.WordTrace]
  refine ⟨236969689533025974795273635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157979793022017316530182423 236969689533025974795273635)
  ·
    refine ⟨355454534299538962192910453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236969689533025974795273635 355454534299538962192910453)
    ·
      refine ⟨33323862590581777705585355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 355454534299538962192910453 33323862590581777705585355)
      ·
        refine ⟨49985793885872666558378033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33323862590581777705585355 49985793885872666558378033)
        ·
          refine ⟨37489345414404499918783525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49985793885872666558378033 37489345414404499918783525)
          ·
            refine ⟨7029252265200843734771911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37489345414404499918783525 7029252265200843734771911)
            ·
              refine ⟨10543878397801265602157867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7029252265200843734771911 10543878397801265602157867)
              ·
                refine ⟨15815817596701898403236801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10543878397801265602157867 15815817596701898403236801)
                ·
                  refine ⟨11861863197526423802427601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15815817596701898403236801 11861863197526423802427601)
                  ·
                    refine ⟨8896397398144817851820701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11861863197526423802427601 8896397398144817851820701)
                    ·
                      refine ⟨3336149024304306694432763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8896397398144817851820701 3336149024304306694432763)
                      ·
                        rfl

theorem cell23_6497127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 1, 1, 2, 2, 3].length) (baseStart_6497127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6497127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6497127 prefixEnd_6497127 := by exact prefixLift 6497127
  have htrace : WordTrace (prefixWord ++ tailWord_6497127) baseStart_6497127 baseEnd_6497127 := by
    simpa [prefixWord, tailWord_6497127, baseEnd_6497127] using wordTrace_append hprefix tailTrace_6497127
  have hstable : (prefixWord ++ tailWord_6497127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6497127).length < 2 ^ (prefixWord ++ tailWord_6497127).sum := by decide
  have hdescent : baseEnd_6497127 < baseStart_6497127 := by decide
  rcases family_descends (prefixWord ++ tailWord_6497127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6497157 : List Nat := [1, 3, 1, 1, 3, 4, 2, 1, 3, 1, 3]
def baseStart_6497157 : Nat := 118140960795 + 6497157 * 2 ^ 59
def prefixEnd_6497157 : Nat := 4983230072969 + 3 ^ 40 * 6497157 * 2
def baseEnd_6497157 : Nat := 3336164428723941577057625

theorem tailTrace_6497157 : CollatzResearch.WordTrace tailWord_6497157 prefixEnd_6497157 3336164428723941577057625 := by
  unfold tailWord_6497157
  simp only [CollatzResearch.WordTrace]
  refine ⟨236970783722917289918865725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157980522481944859945910483 236970783722917289918865725)
  ·
    refine ⟨88864043896093983719574647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 236970783722917289918865725 88864043896093983719574647)
    ·
      refine ⟨133296065844140975579361971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88864043896093983719574647 133296065844140975579361971)
      ·
        refine ⟨199944098766211463369042957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133296065844140975579361971 199944098766211463369042957)
        ·
          refine ⟨74979037037329298763391109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 199944098766211463369042957 74979037037329298763391109)
          ·
            refine ⟨14058569444499243518135833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74979037037329298763391109 14058569444499243518135833)
            ·
              refine ⟨10543927083374432638601875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14058569444499243518135833 10543927083374432638601875)
              ·
                refine ⟨15815890625061648957902813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10543927083374432638601875 15815890625061648957902813)
                ·
                  refine ⟨5930958984398118359213555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15815890625061648957902813 5930958984398118359213555)
                  ·
                    refine ⟨8896438476597177538820333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5930958984398118359213555 8896438476597177538820333)
                    ·
                      refine ⟨3336164428723941577057625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8896438476597177538820333 3336164428723941577057625)
                      ·
                        rfl

theorem cell23_6497157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 2, 1, 3, 1, 3].length) (baseStart_6497157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6497157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6497157 prefixEnd_6497157 := by exact prefixLift 6497157
  have htrace : WordTrace (prefixWord ++ tailWord_6497157) baseStart_6497157 baseEnd_6497157 := by
    simpa [prefixWord, tailWord_6497157, baseEnd_6497157] using wordTrace_append hprefix tailTrace_6497157
  have hstable : (prefixWord ++ tailWord_6497157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6497157).length < 2 ^ (prefixWord ++ tailWord_6497157).sum := by decide
  have hdescent : baseEnd_6497157 < baseStart_6497157 := by decide
  rcases family_descends (prefixWord ++ tailWord_6497157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6497163 : List Nat := [1, 1, 1, 1, 4, 2, 2, 1, 5, 1, 4]
def baseStart_6497163 : Nat := 118140960795 + 6497163 * 2 ^ 59
def prefixEnd_6497163 : Nat := 4983230072969 + 3 ^ 40 * 6497163 * 2
def baseEnd_6497163 : Nat := 3336167509607868553582597

theorem tailTrace_6497163 : CollatzResearch.WordTrace tailWord_6497163 prefixEnd_6497163 3336167509607868553582597 := by
  unfold tailWord_6497163
  simp only [CollatzResearch.WordTrace]
  refine ⟨236971002560895552943584143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157980668373930368629056095 236971002560895552943584143)
  ·
    refine ⟨355456503841343329415376215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236971002560895552943584143 355456503841343329415376215)
    ·
      refine ⟨533184755762014994123064323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 355456503841343329415376215 533184755762014994123064323)
      ·
        refine ⟨799777133643022491184596485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 533184755762014994123064323 799777133643022491184596485)
        ·
          refine ⟨149958212558066717097111841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 799777133643022491184596485 149958212558066717097111841)
          ·
            refine ⟨112468659418550037822833881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149958212558066717097111841 112468659418550037822833881)
            ·
              refine ⟨84351494563912528367125411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112468659418550037822833881 84351494563912528367125411)
              ·
                refine ⟨126527241845868792550688117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84351494563912528367125411 126527241845868792550688117)
                ·
                  refine ⟨11861928923050199301627011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 126527241845868792550688117 11861928923050199301627011)
                  ·
                    refine ⟨17792893384575298952440517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11861928923050199301627011 17792893384575298952440517)
                    ·
                      refine ⟨3336167509607868553582597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17792893384575298952440517 3336167509607868553582597)
                      ·
                        rfl

theorem cell23_6497163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 1, 5, 1, 4].length) (baseStart_6497163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6497163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6497163 prefixEnd_6497163 := by exact prefixLift 6497163
  have htrace : WordTrace (prefixWord ++ tailWord_6497163) baseStart_6497163 baseEnd_6497163 := by
    simpa [prefixWord, tailWord_6497163, baseEnd_6497163] using wordTrace_append hprefix tailTrace_6497163
  have hstable : (prefixWord ++ tailWord_6497163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6497163).length < 2 ^ (prefixWord ++ tailWord_6497163).sum := by decide
  have hdescent : baseEnd_6497163 < baseStart_6497163 := by decide
  rcases family_descends (prefixWord ++ tailWord_6497163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6497193 : List Nat := [1, 2, 1, 1, 1, 1, 6, 1, 3, 2, 4]
def baseStart_6497193 : Nat := 118140960795 + 6497193 * 2 ^ 59
def prefixEnd_6497193 : Nat := 4983230072969 + 3 ^ 40 * 6497193 * 2
def baseEnd_6497193 : Nat := 3336182914027503436207459

theorem tailTrace_6497193 : CollatzResearch.WordTrace tailWord_6497193 prefixEnd_6497193 3336182914027503436207459 := by
  unfold tailWord_6497193
  simp only [CollatzResearch.WordTrace]
  refine ⟨236972096750786868067176233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157981397833857912044784155 236972096750786868067176233)
  ·
    refine ⟨177729072563090151050382175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236972096750786868067176233 177729072563090151050382175)
    ·
      refine ⟨266593608844635226575573263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177729072563090151050382175 266593608844635226575573263)
      ·
        refine ⟨399890413266952839863359895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266593608844635226575573263 399890413266952839863359895)
        ·
          refine ⟨599835619900429259795039843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 399890413266952839863359895 599835619900429259795039843)
          ·
            refine ⟨899753429850643889692559765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 599835619900429259795039843 899753429850643889692559765)
            ·
              refine ⟨42175942024248932329338739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 899753429850643889692559765 42175942024248932329338739)
              ·
                refine ⟨63263913036373398494008109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42175942024248932329338739 63263913036373398494008109)
                ·
                  refine ⟨23723967388640024435253041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63263913036373398494008109 23723967388640024435253041)
                  ·
                    refine ⟨17792975541480018326439781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23723967388640024435253041 17792975541480018326439781)
                    ·
                      refine ⟨3336182914027503436207459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17792975541480018326439781 3336182914027503436207459)
                      ·
                        rfl

theorem cell23_6497193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 1, 3, 2, 4].length) (baseStart_6497193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6497193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6497193 prefixEnd_6497193 := by exact prefixLift 6497193
  have htrace : WordTrace (prefixWord ++ tailWord_6497193) baseStart_6497193 baseEnd_6497193 := by
    simpa [prefixWord, tailWord_6497193, baseEnd_6497193] using wordTrace_append hprefix tailTrace_6497193
  have hstable : (prefixWord ++ tailWord_6497193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6497193).length < 2 ^ (prefixWord ++ tailWord_6497193).sum := by decide
  have hdescent : baseEnd_6497193 < baseStart_6497193 := by decide
  rcases family_descends (prefixWord ++ tailWord_6497193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6497234 : List Nat := [3, 2, 2, 3, 1, 1, 3, 2, 1, 2, 3]
def baseStart_6497234 : Nat := 118140960795 + 6497234 * 2 ^ 59
def prefixEnd_6497234 : Nat := 4983230072969 + 3 ^ 40 * 6497234 * 2
def baseEnd_6497234 : Nat := 3336203966734337775794771

theorem tailTrace_6497234 : CollatzResearch.WordTrace tailWord_6497234 prefixEnd_6497234 3336203966734337775794771 := by
  unfold tailWord_6497234
  simp only [CollatzResearch.WordTrace]
  refine ⟨59243398035909583017354689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157982394762425554712945837 59243398035909583017354689)
  ·
    refine ⟨44432548526932187263016017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59243398035909583017354689 44432548526932187263016017)
    ·
      refine ⟨33324411395199140447262013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44432548526932187263016017 33324411395199140447262013)
      ·
        refine ⟨12496654273199677667723255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33324411395199140447262013 12496654273199677667723255)
        ·
          refine ⟨18744981409799516501584883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12496654273199677667723255 18744981409799516501584883)
          ·
            refine ⟨28117472114699274752377325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18744981409799516501584883 28117472114699274752377325)
            ·
              refine ⟨10544052043012228032141497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28117472114699274752377325 10544052043012228032141497)
              ·
                refine ⟨7908039032259171024106123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10544052043012228032141497 7908039032259171024106123)
                ·
                  refine ⟨11862058548388756536159185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7908039032259171024106123 11862058548388756536159185)
                  ·
                    refine ⟨8896543911291567402119389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11862058548388756536159185 8896543911291567402119389)
                    ·
                      refine ⟨3336203966734337775794771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8896543911291567402119389 3336203966734337775794771)
                      ·
                        rfl

theorem cell23_6497234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_6497234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6497234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6497234 prefixEnd_6497234 := by exact prefixLift 6497234
  have htrace : WordTrace (prefixWord ++ tailWord_6497234) baseStart_6497234 baseEnd_6497234 := by
    simpa [prefixWord, tailWord_6497234, baseEnd_6497234] using wordTrace_append hprefix tailTrace_6497234
  have hstable : (prefixWord ++ tailWord_6497234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6497234).length < 2 ^ (prefixWord ++ tailWord_6497234).sum := by decide
  have hdescent : baseEnd_6497234 < baseStart_6497234 := by decide
  rcases family_descends (prefixWord ++ tailWord_6497234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6497247 : List Nat := [1, 1, 2, 3, 5, 1, 1, 2, 1, 3, 3]
def baseStart_6497247 : Nat := 118140960795 + 6497247 * 2 ^ 59
def prefixEnd_6497247 : Nat := 4983230072969 + 3 ^ 40 * 6497247 * 2
def baseEnd_6497247 : Nat := 3336210641982846224932211

theorem tailTrace_6497247 : CollatzResearch.WordTrace tailWord_6497247 prefixEnd_6497247 3336210641982846224932211 := by
  unfold tailWord_6497247
  simp only [CollatzResearch.WordTrace]
  refine ⟨236974066292591235289641995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157982710861727490193094663 236974066292591235289641995)
  ·
    refine ⟨355461099438886852934462993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236974066292591235289641995 355461099438886852934462993)
    ·
      refine ⟨266595824579165139700847245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 355461099438886852934462993 266595824579165139700847245)
      ·
        refine ⟨99973434217186927387817717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 266595824579165139700847245 99973434217186927387817717)
        ·
          refine ⟨9372509457861274442607911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 99973434217186927387817717 9372509457861274442607911)
          ·
            refine ⟨14058764186791911663911867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9372509457861274442607911 14058764186791911663911867)
            ·
              refine ⟨21088146280187867495867801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14058764186791911663911867 21088146280187867495867801)
              ·
                refine ⟨15816109710140900621900851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21088146280187867495867801 15816109710140900621900851)
                ·
                  refine ⟨23724164565211350932851277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15816109710140900621900851 23724164565211350932851277)
                  ·
                    refine ⟨8896561711954256599819229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23724164565211350932851277 8896561711954256599819229)
                    ·
                      refine ⟨3336210641982846224932211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8896561711954256599819229 3336210641982846224932211)
                      ·
                        rfl

theorem cell23_6497247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 2, 1, 3, 3].length) (baseStart_6497247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6497247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6497247 prefixEnd_6497247 := by exact prefixLift 6497247
  have htrace : WordTrace (prefixWord ++ tailWord_6497247) baseStart_6497247 baseEnd_6497247 := by
    simpa [prefixWord, tailWord_6497247, baseEnd_6497247] using wordTrace_append hprefix tailTrace_6497247
  have hstable : (prefixWord ++ tailWord_6497247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6497247).length < 2 ^ (prefixWord ++ tailWord_6497247).sum := by decide
  have hdescent : baseEnd_6497247 < baseStart_6497247 := by decide
  rcases family_descends (prefixWord ++ tailWord_6497247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6497308 : List Nat := [2, 2, 3, 1, 4, 2, 2, 1, 1, 3, 2]
def baseStart_6497308 : Nat := 118140960795 + 6497308 * 2 ^ 59
def prefixEnd_6497308 : Nat := 4983230072969 + 3 ^ 40 * 6497308 * 2
def baseEnd_6497308 : Nat := 3336241964302770486269431

theorem tailTrace_6497308 : CollatzResearch.WordTrace tailWord_6497308 prefixEnd_6497308 3336241964302770486269431 := by
  unfold tailWord_6497308
  simp only [CollatzResearch.WordTrace]
  refine ⟨118488145572685121353806289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157984194096913495138408385 118488145572685121353806289)
  ·
    refine ⟨88866109179513841015354717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118488145572685121353806289 88866109179513841015354717)
    ·
      refine ⟨33324790942317690380758019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88866109179513841015354717 33324790942317690380758019)
      ·
        refine ⟨49987186413476535571137029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33324790942317690380758019 49987186413476535571137029)
        ·
          refine ⟨9372597452526850419588193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49987186413476535571137029 9372597452526850419588193)
          ·
            refine ⟨7029448089395137814691145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9372597452526850419588193 7029448089395137814691145)
            ·
              refine ⟨5272086067046353361018359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7029448089395137814691145 5272086067046353361018359)
              ·
                refine ⟨7908129100569530041527539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5272086067046353361018359 7908129100569530041527539)
                ·
                  refine ⟨11862193650854295062291309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7908129100569530041527539 11862193650854295062291309)
                  ·
                    refine ⟨4448322619070360648359241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11862193650854295062291309 4448322619070360648359241)
                    ·
                      refine ⟨3336241964302770486269431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4448322619070360648359241 3336241964302770486269431)
                      ·
                        rfl

theorem cell23_6497308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 2, 1, 1, 3, 2].length) (baseStart_6497308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6497308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6497308 prefixEnd_6497308 := by exact prefixLift 6497308
  have htrace : WordTrace (prefixWord ++ tailWord_6497308) baseStart_6497308 baseEnd_6497308 := by
    simpa [prefixWord, tailWord_6497308, baseEnd_6497308] using wordTrace_append hprefix tailTrace_6497308
  have hstable : (prefixWord ++ tailWord_6497308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6497308).length < 2 ^ (prefixWord ++ tailWord_6497308).sum := by decide
  have hdescent : baseEnd_6497308 < baseStart_6497308 := by decide
  rcases family_descends (prefixWord ++ tailWord_6497308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6497337 : List Nat := [1, 2, 1, 5, 2, 1, 2, 1, 2, 3, 3]
def baseStart_6497337 : Nat := 118140960795 + 6497337 * 2 ^ 59
def prefixEnd_6497337 : Nat := 4983230072969 + 3 ^ 40 * 6497337 * 2
def baseEnd_6497337 : Nat := 3336256855241750872806797

theorem tailTrace_6497337 : CollatzResearch.WordTrace tailWord_6497337 prefixEnd_6497337 3336256855241750872806797 := by
  unfold tailWord_6497337
  simp only [CollatzResearch.WordTrace]
  refine ⟨236977348862265180660418265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157984899241510120440278843 236977348862265180660418265)
  ·
    refine ⟨177733011646698885495313699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236977348862265180660418265 177733011646698885495313699)
    ·
      refine ⟨266599517470048328242970549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177733011646698885495313699 266599517470048328242970549)
      ·
        refine ⟨24993704762817030772778489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 266599517470048328242970549 24993704762817030772778489)
        ·
          refine ⟨18745278572112773079583867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24993704762817030772778489 18745278572112773079583867)
          ·
            refine ⟨28117917858169159619375801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18745278572112773079583867 28117917858169159619375801)
            ·
              refine ⟨21088438393626869714531851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28117917858169159619375801 21088438393626869714531851)
              ·
                refine ⟨31632657590440304571797777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21088438393626869714531851 31632657590440304571797777)
                ·
                  refine ⟨23724493192830228428848333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31632657590440304571797777 23724493192830228428848333)
                  ·
                    refine ⟨8896684947311335660818125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23724493192830228428848333 8896684947311335660818125)
                    ·
                      refine ⟨3336256855241750872806797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8896684947311335660818125 3336256855241750872806797)
                      ·
                        rfl

theorem cell23_6497337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 1, 2, 3, 3].length) (baseStart_6497337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6497337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6497337 prefixEnd_6497337 := by exact prefixLift 6497337
  have htrace : WordTrace (prefixWord ++ tailWord_6497337) baseStart_6497337 baseEnd_6497337 := by
    simpa [prefixWord, tailWord_6497337, baseEnd_6497337] using wordTrace_append hprefix tailTrace_6497337
  have hstable : (prefixWord ++ tailWord_6497337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6497337).length < 2 ^ (prefixWord ++ tailWord_6497337).sum := by decide
  have hdescent : baseEnd_6497337 < baseStart_6497337 := by decide
  rcases family_descends (prefixWord ++ tailWord_6497337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6497340 : List Nat := [2, 2, 2, 2, 2, 2, 1, 2, 1, 7]
def baseStart_6497340 : Nat := 118140960795 + 6497340 * 2 ^ 59
def prefixEnd_6497340 : Nat := 4983230072969 + 3 ^ 40 * 6497340 * 2
def baseEnd_6497340 : Nat := 1112086131894571453689761

theorem tailTrace_6497340 : CollatzResearch.WordTrace tailWord_6497340 prefixEnd_6497340 1112086131894571453689761 := by
  unfold tailWord_6497340
  simp only [CollatzResearch.WordTrace]
  refine ⟨118488729140627156086388737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157984972187502874781851649 118488729140627156086388737)
  ·
    refine ⟨88866546855470367064791553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118488729140627156086388737 88866546855470367064791553)
    ·
      refine ⟨66649910141602775298593665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88866546855470367064791553 66649910141602775298593665)
      ·
        refine ⟨49987432606202081473945249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66649910141602775298593665 49987432606202081473945249)
        ·
          refine ⟨37490574454651561105458937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49987432606202081473945249 37490574454651561105458937)
          ·
            refine ⟨28117930840988670829094203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37490574454651561105458937 28117930840988670829094203)
            ·
              refine ⟨42176896261483006243641305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28117930840988670829094203 42176896261483006243641305)
              ·
                refine ⟨31632672196112254682730979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42176896261483006243641305 31632672196112254682730979)
                ·
                  refine ⟨47449008294168382024096469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31632672196112254682730979 47449008294168382024096469)
                  ·
                    refine ⟨1112086131894571453689761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47449008294168382024096469 1112086131894571453689761)
                    ·
                      rfl

theorem cell23_6497340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 2, 1, 7].length) (baseStart_6497340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6497340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6497340 prefixEnd_6497340 := by exact prefixLift 6497340
  have htrace : WordTrace (prefixWord ++ tailWord_6497340) baseStart_6497340 baseEnd_6497340 := by
    simpa [prefixWord, tailWord_6497340, baseEnd_6497340] using wordTrace_append hprefix tailTrace_6497340
  have hstable : (prefixWord ++ tailWord_6497340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6497340).length < 2 ^ (prefixWord ++ tailWord_6497340).sum := by decide
  have hdescent : baseEnd_6497340 < baseStart_6497340 := by decide
  rcases family_descends (prefixWord ++ tailWord_6497340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6497357 : List Nat := [1, 6, 1, 1, 1, 2, 2, 1, 1, 7]
def baseStart_6497357 : Nat := 118140960795 + 6497357 * 2 ^ 59
def prefixEnd_6497357 : Nat := 4983230072969 + 3 ^ 40 * 6497357 * 2
def baseEnd_6497357 : Nat := 1112089041618280264852235

theorem tailTrace_6497357 : CollatzResearch.WordTrace tailWord_6497357 prefixEnd_6497357 1112089041618280264852235 := by
  unfold tailWord_6497357
  simp only [CollatzResearch.WordTrace]
  refine ⟨236978078322192724076146325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157985385548128482717430883 236978078322192724076146325)
  ·
    refine ⟨11108347421352783941069359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 236978078322192724076146325 11108347421352783941069359)
    ·
      refine ⟨16662521132029175911604039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11108347421352783941069359 16662521132029175911604039)
      ·
        refine ⟨24993781698043763867406059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16662521132029175911604039 24993781698043763867406059)
        ·
          refine ⟨37490672547065645801109089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24993781698043763867406059 37490672547065645801109089)
          ·
            refine ⟨28118004410299234350831817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37490672547065645801109089 28118004410299234350831817)
            ·
              refine ⟨21088503307724425763123863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28118004410299234350831817 21088503307724425763123863)
              ·
                refine ⟨31632754961586638644685795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21088503307724425763123863 31632754961586638644685795)
                ·
                  refine ⟨47449132442379957967028693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31632754961586638644685795 47449132442379957967028693)
                  ·
                    refine ⟨1112089041618280264852235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47449132442379957967028693 1112089041618280264852235)
                    ·
                      rfl

theorem cell23_6497357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_6497357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6497357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6497357 prefixEnd_6497357 := by exact prefixLift 6497357
  have htrace : WordTrace (prefixWord ++ tailWord_6497357) baseStart_6497357 baseEnd_6497357 := by
    simpa [prefixWord, tailWord_6497357, baseEnd_6497357] using wordTrace_append hprefix tailTrace_6497357
  have hstable : (prefixWord ++ tailWord_6497357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6497357).length < 2 ^ (prefixWord ++ tailWord_6497357).sum := by decide
  have hdescent : baseEnd_6497357 < baseStart_6497357 := by decide
  rcases family_descends (prefixWord ++ tailWord_6497357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6497360 : List Nat := [2, 1, 1, 1, 1, 3, 1, 2, 6, 1, 4]
def baseStart_6497360 : Nat := 118140960795 + 6497360 * 2 ^ 59
def prefixEnd_6497360 : Nat := 4983230072969 + 3 ^ 40 * 6497360 * 2
def baseEnd_6497360 : Nat := 3336268665296804282819191

theorem tailTrace_6497360 : CollatzResearch.WordTrace tailWord_6497360 prefixEnd_6497360 3336268665296804282819191 := by
  unfold tailWord_6497360
  simp only [CollatzResearch.WordTrace]
  refine ⟨118489093870590927794252767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157985458494121237059003689 118489093870590927794252767)
  ·
    refine ⟨177733640805886391691379151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118489093870590927794252767 177733640805886391691379151)
    ·
      refine ⟨266600461208829587537068727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177733640805886391691379151 266600461208829587537068727)
      ·
        refine ⟨399900691813244381305603091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266600461208829587537068727 399900691813244381305603091)
        ·
          refine ⟨599851037719866571958404637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 399900691813244381305603091 599851037719866571958404637)
          ·
            refine ⟨224944139144949964484401739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 599851037719866571958404637 224944139144949964484401739)
            ·
              refine ⟨337416208717424946726602609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 224944139144949964484401739 337416208717424946726602609)
              ·
                refine ⟨253062156538068710044951957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 337416208717424946726602609 253062156538068710044951957)
                ·
                  refine ⟨11862288587721970783357123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 253062156538068710044951957 11862288587721970783357123)
                  ·
                    refine ⟨17793432881582956175035685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11862288587721970783357123 17793432881582956175035685)
                    ·
                      refine ⟨3336268665296804282819191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17793432881582956175035685 3336268665296804282819191)
                      ·
                        rfl

theorem cell23_6497360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 6, 1, 4].length) (baseStart_6497360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6497360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6497360 prefixEnd_6497360 := by exact prefixLift 6497360
  have htrace : WordTrace (prefixWord ++ tailWord_6497360) baseStart_6497360 baseEnd_6497360 := by
    simpa [prefixWord, tailWord_6497360, baseEnd_6497360] using wordTrace_append hprefix tailTrace_6497360
  have hstable : (prefixWord ++ tailWord_6497360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6497360).length < 2 ^ (prefixWord ++ tailWord_6497360).sum := by decide
  have hdescent : baseEnd_6497360 < baseStart_6497360 := by decide
  rcases family_descends (prefixWord ++ tailWord_6497360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6497377 : List Nat := [1, 2, 3, 1, 1, 2, 2, 1, 4, 4, 2]
def baseStart_6497377 : Nat := 118140960795 + 6497377 * 2 ^ 59
def prefixEnd_6497377 : Nat := 4983230072969 + 3 ^ 40 * 6497377 * 2
def baseEnd_6497377 : Nat := 3336277394467930716306613

theorem tailTrace_6497377 : CollatzResearch.WordTrace tailWord_6497377 prefixEnd_6497377 3336277394467930716306613 := by
  unfold tailWord_6497377
  simp only [CollatzResearch.WordTrace]
  refine ⟨236978807782120267491874385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157985871854746844994582923 236978807782120267491874385)
  ·
    refine ⟨177734105836590200618905789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236978807782120267491874385 177734105836590200618905789)
    ·
      refine ⟨66650289688721325232089671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177734105836590200618905789 66650289688721325232089671)
      ·
        refine ⟨99975434533081987848134507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66650289688721325232089671 99975434533081987848134507)
        ·
          refine ⟨149963151799622981772201761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99975434533081987848134507 149963151799622981772201761)
          ·
            refine ⟨112472363849717236329151321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149963151799622981772201761 112472363849717236329151321)
            ·
              refine ⟨84354272887287927246863491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112472363849717236329151321 84354272887287927246863491)
              ·
                refine ⟨126531409330931890870295237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84354272887287927246863491 126531409330931890870295237)
                ·
                  refine ⟨23724639249549729538180357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 126531409330931890870295237 23724639249549729538180357)
                  ·
                    refine ⟨4448369859290574288408817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23724639249549729538180357 4448369859290574288408817)
                    ·
                      refine ⟨3336277394467930716306613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4448369859290574288408817 3336277394467930716306613)
                      ·
                        rfl

theorem cell23_6497377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 1, 4, 4, 2].length) (baseStart_6497377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6497377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6497377 prefixEnd_6497377 := by exact prefixLift 6497377
  have htrace : WordTrace (prefixWord ++ tailWord_6497377) baseStart_6497377 baseEnd_6497377 := by
    simpa [prefixWord, tailWord_6497377, baseEnd_6497377] using wordTrace_append hprefix tailTrace_6497377
  have hstable : (prefixWord ++ tailWord_6497377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6497377).length < 2 ^ (prefixWord ++ tailWord_6497377).sum := by decide
  have hdescent : baseEnd_6497377 < baseStart_6497377 := by decide
  rcases family_descends (prefixWord ++ tailWord_6497377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6497384 : List Nat := [2, 1, 4, 4, 1, 1, 1, 1, 1, 2, 5]
def baseStart_6497384 : Nat := 118140960795 + 6497384 * 2 ^ 59
def prefixEnd_6497384 : Nat := 4983230072969 + 3 ^ 40 * 6497384 * 2
def baseEnd_6497384 : Nat := 3336280988832512188919081

theorem tailTrace_6497384 : CollatzResearch.WordTrace tailWord_6497384 prefixEnd_6497384 3336280988832512188919081 := by
  unfold tailWord_6497384
  simp only [CollatzResearch.WordTrace]
  refine ⟨118489531546547453843689603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157986042062063271791586137 118489531546547453843689603)
  ·
    refine ⟨177734297319821180765534405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118489531546547453843689603 177734297319821180765534405)
    ·
      refine ⟨33325180747466471393537701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 177734297319821180765534405 33325180747466471393537701)
      ·
        refine ⟨6248471390149963386288319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33325180747466471393537701 6248471390149963386288319)
        ·
          refine ⟨9372707085224945079432479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6248471390149963386288319 9372707085224945079432479)
          ·
            refine ⟨14059060627837417619148719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9372707085224945079432479 14059060627837417619148719)
            ·
              refine ⟨21088590941756126428723079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14059060627837417619148719 21088590941756126428723079)
              ·
                refine ⟨31632886412634189643084619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21088590941756126428723079 31632886412634189643084619)
                ·
                  refine ⟨47449329618951284464626929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31632886412634189643084619 47449329618951284464626929)
                  ·
                    refine ⟨35586997214213463348470197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47449329618951284464626929 35586997214213463348470197)
                    ·
                      refine ⟨3336280988832512188919081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35586997214213463348470197 3336280988832512188919081)
                      ·
                        rfl

theorem cell23_6497384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_6497384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6497384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6497384 prefixEnd_6497384 := by exact prefixLift 6497384
  have htrace : WordTrace (prefixWord ++ tailWord_6497384) baseStart_6497384 baseEnd_6497384 := by
    simpa [prefixWord, tailWord_6497384, baseEnd_6497384] using wordTrace_append hprefix tailTrace_6497384
  have hstable : (prefixWord ++ tailWord_6497384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6497384).length < 2 ^ (prefixWord ++ tailWord_6497384).sum := by decide
  have hdescent : baseEnd_6497384 < baseStart_6497384 := by decide
  rcases family_descends (prefixWord ++ tailWord_6497384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6497434 : List Nat := [3, 1, 1, 5, 1, 2, 2, 2, 6]
def baseStart_6497434 : Nat := 118140960795 + 6497434 * 2 ^ 59
def prefixEnd_6497434 : Nat := 4983230072969 + 3 ^ 40 * 6497434 * 2
def baseEnd_6497434 : Nat := 370700740318359665921539

theorem tailTrace_6497434 : CollatzResearch.WordTrace tailWord_6497434 prefixEnd_6497434 370700740318359665921539 := by
  unfold tailWord_6497434
  simp only [CollatzResearch.WordTrace]
  refine ⟨59245221685728441556674839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157987257828609177484466237 59245221685728441556674839)
  ·
    refine ⟨88867832528592662335012259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59245221685728441556674839 88867832528592662335012259)
    ·
      refine ⟨133301748792888993502518389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88867832528592662335012259 133301748792888993502518389)
      ·
        refine ⟨12497038949333343140861099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 133301748792888993502518389 12497038949333343140861099)
        ·
          refine ⟨18745558424000014711291649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12497038949333343140861099 18745558424000014711291649)
          ·
            refine ⟨14059168818000011033468737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18745558424000014711291649 14059168818000011033468737)
            ·
              refine ⟨10544376613500008275101553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14059168818000011033468737 10544376613500008275101553)
              ·
                refine ⟨7908282460125006206326165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10544376613500008275101553 7908282460125006206326165)
                ·
                  refine ⟨370700740318359665921539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7908282460125006206326165 370700740318359665921539)
                  ·
                    rfl

theorem cell23_6497434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 2, 2, 6].length) (baseStart_6497434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6497434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6497434 prefixEnd_6497434 := by exact prefixLift 6497434
  have htrace : WordTrace (prefixWord ++ tailWord_6497434) baseStart_6497434 baseEnd_6497434 := by
    simpa [prefixWord, tailWord_6497434, baseEnd_6497434] using wordTrace_append hprefix tailTrace_6497434
  have hstable : (prefixWord ++ tailWord_6497434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6497434).length < 2 ^ (prefixWord ++ tailWord_6497434).sum := by decide
  have hdescent : baseEnd_6497434 < baseStart_6497434 := by decide
  rcases family_descends (prefixWord ++ tailWord_6497434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6497438 : List Nat := [4, 3, 1, 1, 2, 2, 1, 4, 1, 4]
def baseStart_6497438 : Nat := 118140960795 + 6497438 * 2 ^ 59
def prefixEnd_6497438 : Nat := 4983230072969 + 3 ^ 40 * 6497438 * 2
def baseEnd_6497438 : Nat := 1112102905595951659214611

theorem tailTrace_6497438 : CollatzResearch.WordTrace tailWord_6497438 prefixEnd_6497438 1112102905595951659214611 := by
  unfold tailWord_6497438
  simp only [CollatzResearch.WordTrace]
  refine ⟨29622629079362409363730621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157987355089932849939896645 29622629079362409363730621)
  ·
    refine ⟨11108485904760903511398983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29622629079362409363730621 11108485904760903511398983)
    ·
      refine ⟨16662728857141355267098475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11108485904760903511398983 16662728857141355267098475)
      ·
        refine ⟨24994093285712032900647713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16662728857141355267098475 24994093285712032900647713)
        ·
          refine ⟨18745569964284024675485785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24994093285712032900647713 18745569964284024675485785)
          ·
            refine ⟨14059177473213018506614339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18745569964284024675485785 14059177473213018506614339)
            ·
              refine ⟨21088766209819527759921509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14059177473213018506614339 21088766209819527759921509)
              ·
                refine ⟨3954143664341161454985283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21088766209819527759921509 3954143664341161454985283)
                ·
                  refine ⟨5931215496511742182477925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3954143664341161454985283 5931215496511742182477925)
                  ·
                    refine ⟨1112102905595951659214611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5931215496511742182477925 1112102905595951659214611)
                    ·
                      rfl

theorem cell23_6497438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 4, 1, 4].length) (baseStart_6497438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6497438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6497438 prefixEnd_6497438 := by exact prefixLift 6497438
  have htrace : WordTrace (prefixWord ++ tailWord_6497438) baseStart_6497438 baseEnd_6497438 := by
    simpa [prefixWord, tailWord_6497438, baseEnd_6497438] using wordTrace_append hprefix tailTrace_6497438
  have hstable : (prefixWord ++ tailWord_6497438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6497438).length < 2 ^ (prefixWord ++ tailWord_6497438).sum := by decide
  have hdescent : baseEnd_6497438 < baseStart_6497438 := by decide
  rcases family_descends (prefixWord ++ tailWord_6497438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6497467 : List Nat := [1, 1, 1, 1, 1, 2, 4, 1, 1, 8, 2]
def baseStart_6497467 : Nat := 118140960795 + 6497467 * 2 ^ 59
def prefixEnd_6497467 : Nat := 4983230072969 + 3 ^ 40 * 6497467 * 2
def baseEnd_6497467 : Nat := 3336323607726835364181199

theorem tailTrace_6497467 : CollatzResearch.WordTrace tailWord_6497467 prefixEnd_6497467 3336323607726835364181199 := by
  unfold tailWord_6497467
  simp only [CollatzResearch.WordTrace]
  refine ⟨236982090351794212862650655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157988060234529475241767103 236982090351794212862650655)
  ·
    refine ⟨355473135527691319293975983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236982090351794212862650655 355473135527691319293975983)
    ·
      refine ⟨533209703291536978940963975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 355473135527691319293975983 533209703291536978940963975)
      ·
        refine ⟨799814554937305468411445963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 533209703291536978940963975 799814554937305468411445963)
        ·
          refine ⟨1199721832405958202617168945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 799814554937305468411445963 1199721832405958202617168945)
          ·
            refine ⟨899791374304468651962876709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1199721832405958202617168945 899791374304468651962876709)
            ·
              refine ⟨168710882682087872243039383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 899791374304468651962876709 168710882682087872243039383)
              ·
                refine ⟨253066324023131808364559075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 168710882682087872243039383 253066324023131808364559075)
                ·
                  refine ⟨379599486034697712546838613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 253066324023131808364559075 379599486034697712546838613)
                  ·
                    refine ⟨4448431476969113818908265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 379599486034697712546838613 4448431476969113818908265)
                    ·
                      refine ⟨3336323607726835364181199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4448431476969113818908265 3336323607726835364181199)
                      ·
                        rfl

theorem cell23_6497467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 8, 2].length) (baseStart_6497467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6497467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6497467 prefixEnd_6497467 := by exact prefixLift 6497467
  have htrace : WordTrace (prefixWord ++ tailWord_6497467) baseStart_6497467 baseEnd_6497467 := by
    simpa [prefixWord, tailWord_6497467, baseEnd_6497467] using wordTrace_append hprefix tailTrace_6497467
  have hstable : (prefixWord ++ tailWord_6497467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6497467).length < 2 ^ (prefixWord ++ tailWord_6497467).sum := by decide
  have hdescent : baseEnd_6497467 < baseStart_6497467 := by decide
  rcases family_descends (prefixWord ++ tailWord_6497467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6497477 : List Nat := [1, 3, 1, 1, 1, 1, 3, 4, 4, 4]
def baseStart_6497477 : Nat := 118140960795 + 6497477 * 2 ^ 59
def prefixEnd_6497477 : Nat := 4983230072969 + 3 ^ 40 * 6497477 * 2
def baseEnd_6497477 : Nat := 1112109580844460108352051

theorem tailTrace_6497477 : CollatzResearch.WordTrace tailWord_6497477 prefixEnd_6497477 1112109580844460108352051 := by
  unfold tailWord_6497477
  simp only [CollatzResearch.WordTrace]
  refine ⟨236982455081757984570514685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157988303387838656380343123 236982455081757984570514685)
  ·
    refine ⟨88868420655659244213943007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 236982455081757984570514685 88868420655659244213943007)
    ·
      refine ⟨133302630983488866320914511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88868420655659244213943007 133302630983488866320914511)
      ·
        refine ⟨199953946475233299481371767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133302630983488866320914511 199953946475233299481371767)
        ·
          refine ⟨299930919712849949222057651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199953946475233299481371767 299930919712849949222057651)
          ·
            refine ⟨449896379569274923833086477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 299930919712849949222057651 449896379569274923833086477)
            ·
              refine ⟨168711142338478096437407429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 449896379569274923833086477 168711142338478096437407429)
              ·
                refine ⟨31633339188464643082013893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 168711142338478096437407429 31633339188464643082013893)
                ·
                  refine ⟨5931251097837120577877605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31633339188464643082013893 5931251097837120577877605)
                  ·
                    refine ⟨1112109580844460108352051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5931251097837120577877605 1112109580844460108352051)
                    ·
                      rfl

theorem cell23_6497477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 4, 4, 4].length) (baseStart_6497477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6497477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6497477 prefixEnd_6497477 := by exact prefixLift 6497477
  have htrace : WordTrace (prefixWord ++ tailWord_6497477) baseStart_6497477 baseEnd_6497477 := by
    simpa [prefixWord, tailWord_6497477, baseEnd_6497477] using wordTrace_append hprefix tailTrace_6497477
  have hstable : (prefixWord ++ tailWord_6497477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6497477).length < 2 ^ (prefixWord ++ tailWord_6497477).sum := by decide
  have hdescent : baseEnd_6497477 < baseStart_6497477 := by decide
  rcases family_descends (prefixWord ++ tailWord_6497477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6497485 : List Nat := [1, 6, 2, 2, 2, 1, 1, 2, 6]
def baseStart_6497485 : Nat := 118140960795 + 6497485 * 2 ^ 59
def prefixEnd_6497485 : Nat := 4983230072969 + 3 ^ 40 * 6497485 * 2
def baseEnd_6497485 : Nat := 370703650042068477084013

theorem tailTrace_6497485 : CollatzResearch.WordTrace tailWord_6497485 prefixEnd_6497485 370703650042068477084013 := by
  unfold tailWord_6497485
  simp only [CollatzResearch.WordTrace]
  refine ⟨236982746865729001936805909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157988497910486001291203939 236982746865729001936805909)
  ·
    refine ⟨11108566259331046965787777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 236982746865729001936805909 11108566259331046965787777)
    ·
      refine ⟨8331424694498285224340833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11108566259331046965787777 8331424694498285224340833)
      ·
        refine ⟨6248568520873713918255625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8331424694498285224340833 6248568520873713918255625)
        ·
          refine ⟨4686426390655285438691719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6248568520873713918255625 4686426390655285438691719)
          ·
            refine ⟨7029639585982928158037579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4686426390655285438691719 7029639585982928158037579)
            ·
              refine ⟨10544459378974392237056369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7029639585982928158037579 10544459378974392237056369)
              ·
                refine ⟨7908344534230794177792277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10544459378974392237056369 7908344534230794177792277)
                ·
                  refine ⟨370703650042068477084013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7908344534230794177792277 370703650042068477084013)
                  ·
                    rfl

theorem cell23_6497485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 1, 2, 6].length) (baseStart_6497485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6497485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6497485 prefixEnd_6497485 := by exact prefixLift 6497485
  have htrace : WordTrace (prefixWord ++ tailWord_6497485) baseStart_6497485 baseEnd_6497485 := by
    simpa [prefixWord, tailWord_6497485, baseEnd_6497485] using wordTrace_append hprefix tailTrace_6497485
  have hstable : (prefixWord ++ tailWord_6497485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6497485).length < 2 ^ (prefixWord ++ tailWord_6497485).sum := by decide
  have hdescent : baseEnd_6497485 < baseStart_6497485 := by decide
  rcases family_descends (prefixWord ++ tailWord_6497485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6497487 : List Nat := [1, 1, 2, 1, 1, 3, 2, 2, 5, 2, 3]
def baseStart_6497487 : Nat := 118140960795 + 6497487 * 2 ^ 59
def prefixEnd_6497487 : Nat := 4983230072969 + 3 ^ 40 * 6497487 * 2
def baseEnd_6497487 : Nat := 3336333877339925285931107

theorem tailTrace_6497487 : CollatzResearch.WordTrace tailWord_6497487 prefixEnd_6497487 3336333877339925285931107 := by
  unfold tailWord_6497487
  simp only [CollatzResearch.WordTrace]
  refine ⟨236982819811721756278378715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157988546541147837518919143 236982819811721756278378715)
  ·
    refine ⟨355474229717582634417568073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236982819811721756278378715 355474229717582634417568073)
    ·
      refine ⟨266605672288186975813176055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 355474229717582634417568073 266605672288186975813176055)
      ·
        refine ⟨399908508432280463719764083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266605672288186975813176055 399908508432280463719764083)
        ·
          refine ⟨599862762648420695579646125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 399908508432280463719764083 599862762648420695579646125)
          ·
            refine ⟨224948535993157760842367297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 599862762648420695579646125 224948535993157760842367297)
            ·
              refine ⟨168711401994868320631775473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 224948535993157760842367297 168711401994868320631775473)
              ·
                refine ⟨126533551496151240473831605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 168711401994868320631775473 126533551496151240473831605)
                ·
                  refine ⟨11862520452764178794421713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 126533551496151240473831605 11862520452764178794421713)
                  ·
                    refine ⟨8896890339573134095816285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11862520452764178794421713 8896890339573134095816285)
                    ·
                      refine ⟨3336333877339925285931107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8896890339573134095816285 3336333877339925285931107)
                      ·
                        rfl

theorem cell23_6497487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 2, 5, 2, 3].length) (baseStart_6497487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6497487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6497487 prefixEnd_6497487 := by exact prefixLift 6497487
  have htrace : WordTrace (prefixWord ++ tailWord_6497487) baseStart_6497487 baseEnd_6497487 := by
    simpa [prefixWord, tailWord_6497487, baseEnd_6497487] using wordTrace_append hprefix tailTrace_6497487
  have hstable : (prefixWord ++ tailWord_6497487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6497487).length < 2 ^ (prefixWord ++ tailWord_6497487).sum := by decide
  have hdescent : baseEnd_6497487 < baseStart_6497487 := by decide
  rcases family_descends (prefixWord ++ tailWord_6497487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6497511 : List Nat := [1, 1, 5, 3, 2, 2, 1, 1, 1, 6]
def baseStart_6497511 : Nat := 118140960795 + 6497511 * 2 ^ 59
def prefixEnd_6497511 : Nat := 4983230072969 + 3 ^ 40 * 6497511 * 2
def baseEnd_6497511 : Nat := 1112115400291877730676999

theorem tailTrace_6497511 : CollatzResearch.WordTrace tailWord_6497511 prefixEnd_6497511 1112115400291877730676999 := by
  unfold tailWord_6497511
  simp only [CollatzResearch.WordTrace]
  refine ⟨236983695163634808377252387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157989130109089872251501591 236983695163634808377252387)
  ·
    refine ⟨355475542745452212565878581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236983695163634808377252387 355475542745452212565878581)
    ·
      refine ⟨33325832132386144928051117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 355475542745452212565878581 33325832132386144928051117)
      ·
        refine ⟨12497187049644804348019169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33325832132386144928051117 12497187049644804348019169)
        ·
          refine ⟨9372890287233603261014377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12497187049644804348019169 9372890287233603261014377)
          ·
            refine ⟨7029667715425202445760783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9372890287233603261014377 7029667715425202445760783)
            ·
              refine ⟨10544501573137803668641175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7029667715425202445760783 10544501573137803668641175)
              ·
                refine ⟨15816752359706705502961763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10544501573137803668641175 15816752359706705502961763)
                ·
                  refine ⟨23725128539560058254442645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15816752359706705502961763 23725128539560058254442645)
                  ·
                    refine ⟨1112115400291877730676999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23725128539560058254442645 1112115400291877730676999)
                    ·
                      rfl

theorem cell23_6497511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 1, 1, 1, 6].length) (baseStart_6497511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6497511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6497511 prefixEnd_6497511 := by exact prefixLift 6497511
  have htrace : WordTrace (prefixWord ++ tailWord_6497511) baseStart_6497511 baseEnd_6497511 := by
    simpa [prefixWord, tailWord_6497511, baseEnd_6497511] using wordTrace_append hprefix tailTrace_6497511
  have hstable : (prefixWord ++ tailWord_6497511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6497511).length < 2 ^ (prefixWord ++ tailWord_6497511).sum := by decide
  have hdescent : baseEnd_6497511 < baseStart_6497511 := by decide
  rcases family_descends (prefixWord ++ tailWord_6497511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6497514 : List Nat := [3, 1, 3, 1, 1, 3, 3, 1, 1, 2, 4]
def baseStart_6497514 : Nat := 118140960795 + 6497514 * 2 ^ 59
def prefixEnd_6497514 : Nat := 4983230072969 + 3 ^ 40 * 6497514 * 2
def baseEnd_6497514 : Nat := 3336347741317596680293483

theorem tailTrace_6497514 : CollatzResearch.WordTrace tailWord_6497514 prefixEnd_6497514 3336347741317596680293483 := by
  unfold tailWord_6497514
  simp only [CollatzResearch.WordTrace]
  refine ⟨59245951145655984972402899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157989203055082626593074397 59245951145655984972402899)
  ·
    refine ⟨88868926718483977458604349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59245951145655984972402899 88868926718483977458604349)
    ·
      refine ⟨33325847519431491546976631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88868926718483977458604349 33325847519431491546976631)
      ·
        refine ⟨49988771279147237320464947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33325847519431491546976631 49988771279147237320464947)
        ·
          refine ⟨74983156918720855980697421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49988771279147237320464947 74983156918720855980697421)
          ·
            refine ⟨28118683844520320992761533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74983156918720855980697421 28118683844520320992761533)
            ·
              refine ⟨10544506441695120372285575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28118683844520320992761533 10544506441695120372285575)
              ·
                refine ⟨15816759662542680558428363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10544506441695120372285575 15816759662542680558428363)
                ·
                  refine ⟨23725139493814020837642545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15816759662542680558428363 23725139493814020837642545)
                  ·
                    refine ⟨17793854620360515628231909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23725139493814020837642545 17793854620360515628231909)
                    ·
                      refine ⟨3336347741317596680293483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17793854620360515628231909 3336347741317596680293483)
                      ·
                        rfl

theorem cell23_6497514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 3, 1, 1, 2, 4].length) (baseStart_6497514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6497514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6497514 prefixEnd_6497514 := by exact prefixLift 6497514
  have htrace : WordTrace (prefixWord ++ tailWord_6497514) baseStart_6497514 baseEnd_6497514 := by
    simpa [prefixWord, tailWord_6497514, baseEnd_6497514] using wordTrace_append hprefix tailTrace_6497514
  have hstable : (prefixWord ++ tailWord_6497514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6497514).length < 2 ^ (prefixWord ++ tailWord_6497514).sum := by decide
  have hdescent : baseEnd_6497514 < baseStart_6497514 := by decide
  rcases family_descends (prefixWord ++ tailWord_6497514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6497535 : List Nat := [1, 1, 2, 2, 1, 7, 1, 3, 1, 2, 2]
def baseStart_6497535 : Nat := 118140960795 + 6497535 * 2 ^ 59
def prefixEnd_6497535 : Nat := 4983230072969 + 3 ^ 40 * 6497535 * 2
def baseEnd_6497535 : Nat := 3336358524411341098130887

theorem tailTrace_6497535 : CollatzResearch.WordTrace tailWord_6497535 prefixEnd_6497535 3336358524411341098130887 := by
  unfold tailWord_6497535
  simp only [CollatzResearch.WordTrace]
  refine ⟨236984570515547860476126059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157989713677031906984084039 236984570515547860476126059)
  ·
    refine ⟨355476855773321790714189089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236984570515547860476126059 355476855773321790714189089)
    ·
      refine ⟨266607641829991343035641817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 355476855773321790714189089 266607641829991343035641817)
      ·
        refine ⟨199955731372493507276731363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 266607641829991343035641817 199955731372493507276731363)
        ·
          refine ⟨299933597058740260915097045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199955731372493507276731363 299933597058740260915097045)
          ·
            refine ⟨7029693681064224865197587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 299933597058740260915097045 7029693681064224865197587)
            ·
              refine ⟨10544540521596337297796381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7029693681064224865197587 10544540521596337297796381)
              ·
                refine ⟨3954202695598626486673643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10544540521596337297796381 3954202695598626486673643)
                ·
                  refine ⟨5931304043397939730010465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3954202695598626486673643 5931304043397939730010465)
                  ·
                    refine ⟨4448478032548454797507849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5931304043397939730010465 4448478032548454797507849)
                    ·
                      refine ⟨3336358524411341098130887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4448478032548454797507849 3336358524411341098130887)
                      ·
                        rfl

theorem cell23_6497535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 1, 3, 1, 2, 2].length) (baseStart_6497535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6497535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6497535 prefixEnd_6497535 := by exact prefixLift 6497535
  have htrace : WordTrace (prefixWord ++ tailWord_6497535) baseStart_6497535 baseEnd_6497535 := by
    simpa [prefixWord, tailWord_6497535, baseEnd_6497535] using wordTrace_append hprefix tailTrace_6497535
  have hstable : (prefixWord ++ tailWord_6497535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6497535).length < 2 ^ (prefixWord ++ tailWord_6497535).sum := by decide
  have hdescent : baseEnd_6497535 < baseStart_6497535 := by decide
  rcases family_descends (prefixWord ++ tailWord_6497535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6497557 : List Nat := [1, 3, 2, 1, 2, 1, 1, 3, 2, 3, 4]
def baseStart_6497557 : Nat := 118140960795 + 6497557 * 2 ^ 59
def prefixEnd_6497557 : Nat := 4983230072969 + 3 ^ 40 * 6497557 * 2
def baseEnd_6497557 : Nat := 3336369820985740012055785

theorem tailTrace_6497557 : CollatzResearch.WordTrace tailWord_6497557 prefixEnd_6497557 3336369820985740012055785 := by
  unfold tailWord_6497557
  simp only [CollatzResearch.WordTrace]
  refine ⟨236985372921468158233426925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157990248614312105488951283 236985372921468158233426925)
  ·
    refine ⟨88869514845550559337535097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 236985372921468158233426925 88869514845550559337535097)
    ·
      refine ⟨66652136134162919503151323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88869514845550559337535097 66652136134162919503151323)
      ·
        refine ⟨99978204201244379254726985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66652136134162919503151323 99978204201244379254726985)
        ·
          refine ⟨74983653150933284441045239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99978204201244379254726985 74983653150933284441045239)
          ·
            refine ⟨112475479726399926661567859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74983653150933284441045239 112475479726399926661567859)
            ·
              refine ⟨168713219589599889992351789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112475479726399926661567859 168713219589599889992351789)
              ·
                refine ⟨63267457346099958747131921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 168713219589599889992351789 63267457346099958747131921)
                ·
                  refine ⟨47450593009574969060348941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63267457346099958747131921 47450593009574969060348941)
                  ·
                    refine ⟨17793972378590613397630853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47450593009574969060348941 17793972378590613397630853)
                    ·
                      refine ⟨3336369820985740012055785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17793972378590613397630853 3336369820985740012055785)
                      ·
                        rfl

theorem cell23_6497557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 3, 2, 3, 4].length) (baseStart_6497557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6497557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6497557 prefixEnd_6497557 := by exact prefixLift 6497557
  have htrace : WordTrace (prefixWord ++ tailWord_6497557) baseStart_6497557 baseEnd_6497557 := by
    simpa [prefixWord, tailWord_6497557, baseEnd_6497557] using wordTrace_append hprefix tailTrace_6497557
  have hstable : (prefixWord ++ tailWord_6497557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6497557).length < 2 ^ (prefixWord ++ tailWord_6497557).sum := by decide
  have hdescent : baseEnd_6497557 < baseStart_6497557 := by decide
  rcases family_descends (prefixWord ++ tailWord_6497557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6497568 : List Nat := [2, 1, 1, 5, 3, 1, 1, 3, 2, 1, 3]
def baseStart_6497568 : Nat := 118140960795 + 6497568 * 2 ^ 59
def prefixEnd_6497568 : Nat := 4983230072969 + 3 ^ 40 * 6497568 * 2
def baseEnd_6497568 : Nat := 3336375469272939469018235

theorem tailTrace_6497568 : CollatzResearch.WordTrace tailWord_6497568 prefixEnd_6497568 3336375469272939469018235 := by
  unfold tailWord_6497568
  simp only [CollatzResearch.WordTrace]
  refine ⟨118492887062214153556038679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157990516082952204741384905 118492887062214153556038679)
  ·
    refine ⟨177739330593321230334058019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118492887062214153556038679 177739330593321230334058019)
    ·
      refine ⟨266608995889981845501087029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177739330593321230334058019 266608995889981845501087029)
      ·
        refine ⟨24994593364685798015726909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 266608995889981845501087029 24994593364685798015726909)
        ·
          refine ⟨9372972511757174255897591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24994593364685798015726909 9372972511757174255897591)
          ·
            refine ⟨14059458767635761383846387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9372972511757174255897591 14059458767635761383846387)
            ·
              refine ⟨21089188151453642075769581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14059458767635761383846387 21089188151453642075769581)
              ·
                refine ⟨7908445556795115778413593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21089188151453642075769581 7908445556795115778413593)
                ·
                  refine ⟨5931334167596336833810195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7908445556795115778413593 5931334167596336833810195)
                  ·
                    refine ⟨8897001251394505250715293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5931334167596336833810195 8897001251394505250715293)
                    ·
                      refine ⟨3336375469272939469018235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8897001251394505250715293 3336375469272939469018235)
                      ·
                        rfl

theorem cell23_6497568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 3, 2, 1, 3].length) (baseStart_6497568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6497568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6497568 prefixEnd_6497568 := by exact prefixLift 6497568
  have htrace : WordTrace (prefixWord ++ tailWord_6497568) baseStart_6497568 baseEnd_6497568 := by
    simpa [prefixWord, tailWord_6497568, baseEnd_6497568] using wordTrace_append hprefix tailTrace_6497568
  have hstable : (prefixWord ++ tailWord_6497568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6497568).length < 2 ^ (prefixWord ++ tailWord_6497568).sum := by decide
  have hdescent : baseEnd_6497568 < baseStart_6497568 := by decide
  rcases family_descends (prefixWord ++ tailWord_6497568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6497578 : List Nat := [3, 1, 4, 2, 1, 2, 1, 1, 3, 3, 2]
def baseStart_6497578 : Nat := 118140960795 + 6497578 * 2 ^ 59
def prefixEnd_6497578 : Nat := 4983230072969 + 3 ^ 40 * 6497578 * 2
def baseEnd_6497578 : Nat := 3336380604079484429893189

theorem tailTrace_6497578 : CollatzResearch.WordTrace tailWord_6497578 prefixEnd_6497578 3336380604079484429893189 := by
  unfold tailWord_6497578
  simp only [CollatzResearch.WordTrace]
  refine ⟨59246534713598019704985347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157990759236261385879960925 59246534713598019704985347)
  ·
    refine ⟨88869802070397029557478021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59246534713598019704985347 88869802070397029557478021)
    ·
      refine ⟨16663087888199443042027129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88869802070397029557478021 16663087888199443042027129)
      ·
        refine ⟨12497315916149582281520347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16663087888199443042027129 12497315916149582281520347)
        ·
          refine ⟨18745973874224373422280521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12497315916149582281520347 18745973874224373422280521)
          ·
            refine ⟨14059480405668280066710391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18745973874224373422280521 14059480405668280066710391)
            ·
              refine ⟨21089220608502420100065587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14059480405668280066710391 21089220608502420100065587)
              ·
                refine ⟨31633830912753630150098381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21089220608502420100065587 31633830912753630150098381)
                ·
                  refine ⟨11862686592282611306286893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31633830912753630150098381 11862686592282611306286893)
                  ·
                    refine ⟨4448507472105979239857585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11862686592282611306286893 4448507472105979239857585)
                    ·
                      refine ⟨3336380604079484429893189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4448507472105979239857585 3336380604079484429893189)
                      ·
                        rfl

theorem cell23_6497578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 1, 3, 3, 2].length) (baseStart_6497578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6497578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6497578 prefixEnd_6497578 := by exact prefixLift 6497578
  have htrace : WordTrace (prefixWord ++ tailWord_6497578) baseStart_6497578 baseEnd_6497578 := by
    simpa [prefixWord, tailWord_6497578, baseEnd_6497578] using wordTrace_append hprefix tailTrace_6497578
  have hstable : (prefixWord ++ tailWord_6497578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6497578).length < 2 ^ (prefixWord ++ tailWord_6497578).sum := by decide
  have hdescent : baseEnd_6497578 < baseStart_6497578 := by decide
  rcases family_descends (prefixWord ++ tailWord_6497578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6497624 : List Nat := [2, 1, 2, 2, 1, 1, 5, 1, 2, 3, 3]
def baseStart_6497624 : Nat := 118140960795 + 6497624 * 2 ^ 59
def prefixEnd_6497624 : Nat := 4983230072969 + 3 ^ 40 * 6497624 * 2
def baseEnd_6497624 : Nat := 3336404224189591249917977

theorem tailTrace_6497624 : CollatzResearch.WordTrace tailWord_6497624 prefixEnd_6497624 3336404224189591249917977 := by
  unfold tailWord_6497624
  simp only [CollatzResearch.WordTrace]
  refine ⟨118493908306112714338057963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157991877741483619117410617 118493908306112714338057963)
  ·
    refine ⟨177740862459169071507086945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118493908306112714338057963 177740862459169071507086945)
    ·
      refine ⟨133305646844376803630315209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177740862459169071507086945 133305646844376803630315209)
      ·
        refine ⟨99979235133282602722736407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133305646844376803630315209 99979235133282602722736407)
        ·
          refine ⟨149968852699923904084104611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99979235133282602722736407 149968852699923904084104611)
          ·
            refine ⟨224953279049885856126156917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149968852699923904084104611 224953279049885856126156917)
            ·
              refine ⟨21089369910926799011827211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 224953279049885856126156917 21089369910926799011827211)
              ·
                refine ⟨31634054866390198517740817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21089369910926799011827211 31634054866390198517740817)
                ·
                  refine ⟨23725541149792648888305613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31634054866390198517740817 23725541149792648888305613)
                  ·
                    refine ⟨8897077931172243333114605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23725541149792648888305613 8897077931172243333114605)
                    ·
                      refine ⟨3336404224189591249917977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8897077931172243333114605 3336404224189591249917977)
                      ·
                        rfl

theorem cell23_6497624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 1, 2, 3, 3].length) (baseStart_6497624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6497624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6497624 prefixEnd_6497624 := by exact prefixLift 6497624
  have htrace : WordTrace (prefixWord ++ tailWord_6497624) baseStart_6497624 baseEnd_6497624 := by
    simpa [prefixWord, tailWord_6497624, baseEnd_6497624] using wordTrace_append hprefix tailTrace_6497624
  have hstable : (prefixWord ++ tailWord_6497624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6497624).length < 2 ^ (prefixWord ++ tailWord_6497624).sum := by decide
  have hdescent : baseEnd_6497624 < baseStart_6497624 := by decide
  rcases family_descends (prefixWord ++ tailWord_6497624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6497644 : List Nat := [2, 2, 1, 1, 5, 2, 1, 1, 1, 7]
def baseStart_6497644 : Nat := 118140960795 + 6497644 * 2 ^ 59
def prefixEnd_6497644 : Nat := 4983230072969 + 3 ^ 40 * 6497644 * 2
def baseEnd_6497644 : Nat := 1112138164600893723889295

theorem tailTrace_6497644 : CollatzResearch.WordTrace tailWord_6497644 prefixEnd_6497644 1112138164600893723889295 := by
  unfold tailWord_6497644
  simp only [CollatzResearch.WordTrace]
  refine ⟨118494273036076486045921993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157992364048101981394562657 118494273036076486045921993)
  ·
    refine ⟨88870704777057364534441495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118494273036076486045921993 88870704777057364534441495)
    ·
      refine ⟨133306057165586046801662243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88870704777057364534441495 133306057165586046801662243)
      ·
        refine ⟨199959085748379070202493365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133306057165586046801662243 199959085748379070202493365)
        ·
          refine ⟨18746164288910537831483753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 199959085748379070202493365 18746164288910537831483753)
          ·
            refine ⟨14059623216682903373612815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18746164288910537831483753 14059623216682903373612815)
            ·
              refine ⟨21089434825024355060419223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14059623216682903373612815 21089434825024355060419223)
              ·
                refine ⟨31634152237536532590628835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21089434825024355060419223 31634152237536532590628835)
                ·
                  refine ⟨47451228356304798885943253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31634152237536532590628835 47451228356304798885943253)
                  ·
                    refine ⟨1112138164600893723889295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47451228356304798885943253 1112138164600893723889295)
                    ·
                      rfl

theorem cell23_6497644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 7].length) (baseStart_6497644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6497644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6497644 prefixEnd_6497644 := by exact prefixLift 6497644
  have htrace : WordTrace (prefixWord ++ tailWord_6497644) baseStart_6497644 baseEnd_6497644 := by
    simpa [prefixWord, tailWord_6497644, baseEnd_6497644] using wordTrace_append hprefix tailTrace_6497644
  have hstable : (prefixWord ++ tailWord_6497644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6497644).length < 2 ^ (prefixWord ++ tailWord_6497644).sum := by decide
  have hdescent : baseEnd_6497644 < baseStart_6497644 := by decide
  rcases family_descends (prefixWord ++ tailWord_6497644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6497664 : List Nat := [2, 1, 1, 2, 1, 2, 1, 6, 2, 1, 4]
def baseStart_6497664 : Nat := 118140960795 + 6497664 * 2 ^ 59
def prefixEnd_6497664 : Nat := 4983230072969 + 3 ^ 40 * 6497664 * 2
def baseEnd_6497664 : Nat := 3336424763415771093417793

theorem tailTrace_6497664 : CollatzResearch.WordTrace tailWord_6497664 prefixEnd_6497664 3336424763415771093417793 := by
  unfold tailWord_6497664
  simp only [CollatzResearch.WordTrace]
  refine ⟨118494637766040257753786023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157992850354720343671714697 118494637766040257753786023)
  ·
    refine ⟨177741956649060386630679035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118494637766040257753786023 177741956649060386630679035)
    ·
      refine ⟨266612934973590579946018553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177741956649060386630679035 266612934973590579946018553)
      ·
        refine ⟨199959701230192934959513915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 266612934973590579946018553 199959701230192934959513915)
        ·
          refine ⟨299939551845289402439270873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199959701230192934959513915 299939551845289402439270873)
          ·
            refine ⟨224954663883967051829453155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 299939551845289402439270873 224954663883967051829453155)
            ·
              refine ⟨337431995825950577744179733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 224954663883967051829453155 337431995825950577744179733)
              ·
                refine ⟨15817124804341433331758425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 337431995825950577744179733 15817124804341433331758425)
                ·
                  refine ⟨11862843603256074998818819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15817124804341433331758425 11862843603256074998818819)
                  ·
                    refine ⟨17794265404884112498228229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11862843603256074998818819 17794265404884112498228229)
                    ·
                      refine ⟨3336424763415771093417793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17794265404884112498228229 3336424763415771093417793)
                      ·
                        rfl

theorem cell23_6497664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 6, 2, 1, 4].length) (baseStart_6497664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6497664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6497664 prefixEnd_6497664 := by exact prefixLift 6497664
  have htrace : WordTrace (prefixWord ++ tailWord_6497664) baseStart_6497664 baseEnd_6497664 := by
    simpa [prefixWord, tailWord_6497664, baseEnd_6497664] using wordTrace_append hprefix tailTrace_6497664
  have hstable : (prefixWord ++ tailWord_6497664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6497664).length < 2 ^ (prefixWord ++ tailWord_6497664).sum := by decide
  have hdescent : baseEnd_6497664 < baseStart_6497664 := by decide
  rcases family_descends (prefixWord ++ tailWord_6497664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6497708 : List Nat := [2, 2, 1, 1, 1, 1, 7, 3, 1, 4]
def baseStart_6497708 : Nat := 118140960795 + 6497708 * 2 ^ 59
def prefixEnd_6497708 : Nat := 4983230072969 + 3 ^ 40 * 6497708 * 2
def baseEnd_6497708 : Nat := 1112149118854856307089197

theorem tailTrace_6497708 : CollatzResearch.WordTrace tailWord_6497708 prefixEnd_6497708 1112149118854856307089197 := by
  unfold tailWord_6497708
  simp only [CollatzResearch.WordTrace]
  refine ⟨118495440171960555511086889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157993920229280740681449185 118495440171960555511086889)
  ·
    refine ⟨88871580128970416633315167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118495440171960555511086889 88871580128970416633315167)
    ·
      refine ⟨133307370193455624949972751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88871580128970416633315167 133307370193455624949972751)
      ·
        refine ⟨199961055290183437424959127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133307370193455624949972751 199961055290183437424959127)
        ·
          refine ⟨299941582935275156137438691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199961055290183437424959127 299941582935275156137438691)
          ·
            refine ⟨449912374402912734206158037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 299941582935275156137438691 449912374402912734206158037)
            ·
              refine ⟨10544821275068267207956829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 449912374402912734206158037 10544821275068267207956829)
              ·
                refine ⟨3954307978150600202983811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10544821275068267207956829 3954307978150600202983811)
                ·
                  refine ⟨5931461967225900304475717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3954307978150600202983811 5931461967225900304475717)
                  ·
                    refine ⟨1112149118854856307089197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5931461967225900304475717 1112149118854856307089197)
                    ·
                      rfl

theorem cell23_6497708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 7, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 7, 3, 1, 4].length) (baseStart_6497708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6497708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6497708 prefixEnd_6497708 := by exact prefixLift 6497708
  have htrace : WordTrace (prefixWord ++ tailWord_6497708) baseStart_6497708 baseEnd_6497708 := by
    simpa [prefixWord, tailWord_6497708, baseEnd_6497708] using wordTrace_append hprefix tailTrace_6497708
  have hstable : (prefixWord ++ tailWord_6497708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6497708).length < 2 ^ (prefixWord ++ tailWord_6497708).sum := by decide
  have hdescent : baseEnd_6497708 < baseStart_6497708 := by decide
  rcases family_descends (prefixWord ++ tailWord_6497708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6497725 : List Nat := [1, 4, 1, 2, 2, 1, 5, 2, 1, 4]
def baseStart_6497725 : Nat := 118140960795 + 6497725 * 2 ^ 59
def prefixEnd_6497725 : Nat := 4983230072969 + 3 ^ 40 * 6497725 * 2
def baseEnd_6497725 : Nat := 1112152028578565118251671

theorem tailTrace_6497725 : CollatzResearch.WordTrace tailWord_6497725 prefixEnd_6497725 1112152028578565118251671 := by
  unfold tailWord_6497725
  simp only [CollatzResearch.WordTrace]
  refine ⟨236991500384859522925542629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157994333589906348617028419 236991500384859522925542629)
  ·
    refine ⟨44435906322161160548539243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 236991500384859522925542629 44435906322161160548539243)
    ·
      refine ⟨66653859483241740822808865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44435906322161160548539243 66653859483241740822808865)
      ·
        refine ⟨49990394612431305617106649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66653859483241740822808865 49990394612431305617106649)
        ·
          refine ⟨37492795959323479212829987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49990394612431305617106649 37492795959323479212829987)
          ·
            refine ⟨56239193938985218819244981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37492795959323479212829987 56239193938985218819244981)
            ·
              refine ⟨5272424431779864264304217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56239193938985218819244981 5272424431779864264304217)
              ·
                refine ⟨3954318323834898198228163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5272424431779864264304217 3954318323834898198228163)
                ·
                  refine ⟨5931477485752347297342245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3954318323834898198228163 5931477485752347297342245)
                  ·
                    refine ⟨1112152028578565118251671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5931477485752347297342245 1112152028578565118251671)
                    ·
                      rfl

theorem cell23_6497725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 5, 2, 1, 4].length) (baseStart_6497725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6497725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6497725 prefixEnd_6497725 := by exact prefixLift 6497725
  have htrace : WordTrace (prefixWord ++ tailWord_6497725) baseStart_6497725 baseEnd_6497725 := by
    simpa [prefixWord, tailWord_6497725, baseEnd_6497725] using wordTrace_append hprefix tailTrace_6497725
  have hstable : (prefixWord ++ tailWord_6497725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6497725).length < 2 ^ (prefixWord ++ tailWord_6497725).sum := by decide
  have hdescent : baseEnd_6497725 < baseStart_6497725 := by decide
  rcases family_descends (prefixWord ++ tailWord_6497725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6497738 : List Nat := [3, 1, 2, 1, 2, 5, 2, 1, 6]
def baseStart_6497738 : Nat := 118140960795 + 6497738 * 2 ^ 59
def prefixEnd_6497738 : Nat := 4983230072969 + 3 ^ 40 * 6497738 * 2
def baseEnd_6497738 : Nat := 370718084553800422654717

theorem tailTrace_6497738 : CollatzResearch.WordTrace tailWord_6497738 prefixEnd_6497738 370718084553800422654717 := by
  unfold tailWord_6497738
  simp only [CollatzResearch.WordTrace]
  refine ⟨59247993633453106536441467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157994649689208284097177245 59247993633453106536441467)
  ·
    refine ⟨88871990450179659804662201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59247993633453106536441467 88871990450179659804662201)
    ·
      refine ⟨66653992837634744853496651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88871990450179659804662201 66653992837634744853496651)
      ·
        refine ⟨99980989256452117280244977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66653992837634744853496651 99980989256452117280244977)
        ·
          refine ⟨74985741942339087960183733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99980989256452117280244977 74985741942339087960183733)
          ·
            refine ⟨7029913307094289496267225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 74985741942339087960183733 7029913307094289496267225)
            ·
              refine ⟨5272434980320717122200419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7029913307094289496267225 5272434980320717122200419)
              ·
                refine ⟨7908652470481075683300629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5272434980320717122200419 7908652470481075683300629)
                ·
                  refine ⟨370718084553800422654717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7908652470481075683300629 370718084553800422654717)
                  ·
                    rfl

theorem cell23_6497738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 2, 1, 6].length) (baseStart_6497738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6497738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6497738 prefixEnd_6497738 := by exact prefixLift 6497738
  have htrace : WordTrace (prefixWord ++ tailWord_6497738) baseStart_6497738 baseEnd_6497738 := by
    simpa [prefixWord, tailWord_6497738, baseEnd_6497738] using wordTrace_append hprefix tailTrace_6497738
  have hstable : (prefixWord ++ tailWord_6497738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6497738).length < 2 ^ (prefixWord ++ tailWord_6497738).sum := by decide
  have hdescent : baseEnd_6497738 < baseStart_6497738 := by decide
  rcases family_descends (prefixWord ++ tailWord_6497738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6497768 : List Nat := [2, 1, 4, 1, 1, 2, 5, 1, 1, 5]
def baseStart_6497768 : Nat := 118140960795 + 6497768 * 2 ^ 59
def prefixEnd_6497768 : Nat := 4983230072969 + 3 ^ 40 * 6497768 * 2
def baseEnd_6497768 : Nat := 1112159388467946228839105

theorem tailTrace_6497768 : CollatzResearch.WordTrace tailWord_6497768 prefixEnd_6497768 1112159388467946228839105 := by
  unfold tailWord_6497768
  simp only [CollatzResearch.WordTrace]
  refine ⟨118496534361851870634678979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157995379149135827512905305 118496534361851870634678979)
  ·
    refine ⟨177744801542777805952018469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118496534361851870634678979 177744801542777805952018469)
    ·
      refine ⟨33327150289270838616003463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 177744801542777805952018469 33327150289270838616003463)
      ·
        refine ⟨49990725433906257924005195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33327150289270838616003463 49990725433906257924005195)
        ·
          refine ⟨74986088150859386886007793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49990725433906257924005195 74986088150859386886007793)
          ·
            refine ⟨56239566113144540164505845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74986088150859386886007793 56239566113144540164505845)
            ·
              refine ⟨5272459323107300640422423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56239566113144540164505845 5272459323107300640422423)
              ·
                refine ⟨7908688984660950960633635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5272459323107300640422423 7908688984660950960633635)
                ·
                  refine ⟨11863033476991426440950453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7908688984660950960633635 11863033476991426440950453)
                  ·
                    refine ⟨1112159388467946228839105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11863033476991426440950453 1112159388467946228839105)
                    ·
                      rfl

theorem cell23_6497768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 5, 1, 1, 5].length) (baseStart_6497768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6497768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6497768 prefixEnd_6497768 := by exact prefixLift 6497768
  have htrace : WordTrace (prefixWord ++ tailWord_6497768) baseStart_6497768 baseEnd_6497768 := by
    simpa [prefixWord, tailWord_6497768, baseEnd_6497768] using wordTrace_append hprefix tailTrace_6497768
  have hstable : (prefixWord ++ tailWord_6497768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6497768).length < 2 ^ (prefixWord ++ tailWord_6497768).sum := by decide
  have hdescent : baseEnd_6497768 < baseStart_6497768 := by decide
  rcases family_descends (prefixWord ++ tailWord_6497768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6497782 : List Nat := [5, 1, 1, 1, 2, 3, 1, 4, 1, 1, 3]
def baseStart_6497782 : Nat := 118140960795 + 6497782 * 2 ^ 59
def prefixEnd_6497782 : Nat := 4983230072969 + 3 ^ 40 * 6497782 * 2
def baseEnd_6497782 : Nat := 3336485354133001631742251

theorem tailTrace_6497782 : CollatzResearch.WordTrace tailWord_6497782 prefixEnd_6497782 3336485354133001631742251 := by
  unfold tailWord_6497782
  simp only [CollatzResearch.WordTrace]
  refine ⟨14812098709103313853772975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 157995719563768681106911733 14812098709103313853772975)
  ·
    refine ⟨22218148063654970780659463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14812098709103313853772975 22218148063654970780659463)
    ·
      refine ⟨33327222095482456170989195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22218148063654970780659463 33327222095482456170989195)
      ·
        refine ⟨49990833143223684256483793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33327222095482456170989195 49990833143223684256483793)
        ·
          refine ⟨37493124857417763192362845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49990833143223684256483793 37493124857417763192362845)
          ·
            refine ⟨14059921821531661197136067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37493124857417763192362845 14059921821531661197136067)
            ·
              refine ⟨21089882732297491795704101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14059921821531661197136067 21089882732297491795704101)
              ·
                refine ⟨3954353012305779711694519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21089882732297491795704101 3954353012305779711694519)
                ·
                  refine ⟨5931529518458669567541779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3954353012305779711694519 5931529518458669567541779)
                  ·
                    refine ⟨8897294277688004351312669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5931529518458669567541779 8897294277688004351312669)
                    ·
                      refine ⟨3336485354133001631742251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8897294277688004351312669 3336485354133001631742251)
                      ·
                        rfl

theorem cell23_6497782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 4, 1, 1, 3].length) (baseStart_6497782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6497782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6497782 prefixEnd_6497782 := by exact prefixLift 6497782
  have htrace : WordTrace (prefixWord ++ tailWord_6497782) baseStart_6497782 baseEnd_6497782 := by
    simpa [prefixWord, tailWord_6497782, baseEnd_6497782] using wordTrace_append hprefix tailTrace_6497782
  have hstable : (prefixWord ++ tailWord_6497782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6497782).length < 2 ^ (prefixWord ++ tailWord_6497782).sum := by decide
  have hdescent : baseEnd_6497782 < baseStart_6497782 := by decide
  rcases family_descends (prefixWord ++ tailWord_6497782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6497801 : List Nat := [1, 2, 1, 1, 3, 1, 6, 1, 1, 2, 4]
def baseStart_6497801 : Nat := 118140960795 + 6497801 * 2 ^ 59
def prefixEnd_6497801 : Nat := 4983230072969 + 3 ^ 40 * 6497801 * 2
def baseEnd_6497801 : Nat := 3336495110265437057404663

theorem tailTrace_6497801 : CollatzResearch.WordTrace tailWord_6497801 prefixEnd_6497801 3336495110265437057404663 := by
  unfold tailWord_6497801
  simp only [CollatzResearch.WordTrace]
  refine ⟨236994272332584187905309257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157996181555056125270206171 236994272332584187905309257)
  ·
    refine ⟨177745704249438140928981943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236994272332584187905309257 177745704249438140928981943)
    ·
      refine ⟨266618556374157211393472915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177745704249438140928981943 266618556374157211393472915)
      ·
        refine ⟨399927834561235817090209373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266618556374157211393472915 399927834561235817090209373)
        ·
          refine ⟨149972937960463431408828515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 399927834561235817090209373 149972937960463431408828515)
          ·
            refine ⟨224959406940695147113242773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149972937960463431408828515 224959406940695147113242773)
            ·
              refine ⟨10544972200345085020933255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 224959406940695147113242773 10544972200345085020933255)
              ·
                refine ⟨15817458300517627531399883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10544972200345085020933255 15817458300517627531399883)
                ·
                  refine ⟨23726187450776441297099825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15817458300517627531399883 23726187450776441297099825)
                  ·
                    refine ⟨17794640588082330972824869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23726187450776441297099825 17794640588082330972824869)
                    ·
                      refine ⟨3336495110265437057404663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17794640588082330972824869 3336495110265437057404663)
                      ·
                        rfl

theorem cell23_6497801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 6, 1, 1, 2, 4].length) (baseStart_6497801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6497801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6497801 prefixEnd_6497801 := by exact prefixLift 6497801
  have htrace : WordTrace (prefixWord ++ tailWord_6497801) baseStart_6497801 baseEnd_6497801 := by
    simpa [prefixWord, tailWord_6497801, baseEnd_6497801] using wordTrace_append hprefix tailTrace_6497801
  have hstable : (prefixWord ++ tailWord_6497801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6497801).length < 2 ^ (prefixWord ++ tailWord_6497801).sum := by decide
  have hdescent : baseEnd_6497801 < baseStart_6497801 := by decide
  rcases family_descends (prefixWord ++ tailWord_6497801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6497811 : List Nat := [1, 1, 1, 2, 1, 7, 3, 7]
def baseStart_6497811 : Nat := 118140960795 + 6497811 * 2 ^ 59
def prefixEnd_6497811 : Nat := 4983230072969 + 3 ^ 40 * 6497811 * 2
def baseEnd_6497811 : Nat := 123574083150814148825171

theorem tailTrace_6497811 : CollatzResearch.WordTrace tailWord_6497811 prefixEnd_6497811 123574083150814148825171 := by
  unfold tailWord_6497811
  simp only [CollatzResearch.WordTrace]
  refine ⟨236994637062547959613173287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157996424708365306408782191 236994637062547959613173287)
  ·
    refine ⟨355491955593821939419759931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236994637062547959613173287 355491955593821939419759931)
    ·
      refine ⟨533237933390732909129639897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 355491955593821939419759931 533237933390732909129639897)
      ·
        refine ⟨399928450043049681847229923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 533237933390732909129639897 399928450043049681847229923)
        ·
          refine ⟨599892675064574522770844885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 399928450043049681847229923 599892675064574522770844885)
          ·
            refine ⟨14059984571825965377441677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 599892675064574522770844885 14059984571825965377441677)
            ·
              refine ⟨5272494214434737016540629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14059984571825965377441677 5272494214434737016540629)
              ·
                refine ⟨123574083150814148825171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5272494214434737016540629 123574083150814148825171)
                ·
                  rfl

theorem cell23_6497811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 3, 7].length) (baseStart_6497811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6497811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6497811 prefixEnd_6497811 := by exact prefixLift 6497811
  have htrace : WordTrace (prefixWord ++ tailWord_6497811) baseStart_6497811 baseEnd_6497811 := by
    simpa [prefixWord, tailWord_6497811, baseEnd_6497811] using wordTrace_append hprefix tailTrace_6497811
  have hstable : (prefixWord ++ tailWord_6497811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6497811).length < 2 ^ (prefixWord ++ tailWord_6497811).sum := by decide
  have hdescent : baseEnd_6497811 < baseStart_6497811 := by decide
  rcases family_descends (prefixWord ++ tailWord_6497811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6497825 : List Nat := [1, 2, 3, 2, 2, 2, 4, 1, 1, 2, 3]
def baseStart_6497825 : Nat := 118140960795 + 6497825 * 2 ^ 59
def prefixEnd_6497825 : Nat := 4983230072969 + 3 ^ 40 * 6497825 * 2
def baseEnd_6497825 : Nat := 3336507433801144963504553

theorem tailTrace_6497825 : CollatzResearch.WordTrace tailWord_6497825 prefixEnd_6497825 3336507433801144963504553 := by
  unfold tailWord_6497825
  simp only [CollatzResearch.WordTrace]
  refine ⟨236995147684497240004182929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157996765122998160002788619 236995147684497240004182929)
  ·
    refine ⟨177746360763372930003137197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236995147684497240004182929 177746360763372930003137197)
    ·
      refine ⟨66654885286264848751176449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177746360763372930003137197 66654885286264848751176449)
      ·
        refine ⟨49991163964698636563382337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66654885286264848751176449 49991163964698636563382337)
        ·
          refine ⟨37493372973523977422536753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49991163964698636563382337 37493372973523977422536753)
          ·
            refine ⟨28120029730142983066902565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37493372973523977422536753 28120029730142983066902565)
            ·
              refine ⟨5272505574401809325044231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28120029730142983066902565 5272505574401809325044231)
              ·
                refine ⟨7908758361602713987566347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5272505574401809325044231 7908758361602713987566347)
                ·
                  refine ⟨11863137542404070981349521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7908758361602713987566347 11863137542404070981349521)
                  ·
                    refine ⟨8897353156803053236012141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11863137542404070981349521 8897353156803053236012141)
                    ·
                      refine ⟨3336507433801144963504553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8897353156803053236012141 3336507433801144963504553)
                      ·
                        rfl

theorem cell23_6497825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 4, 1, 1, 2, 3].length) (baseStart_6497825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6497825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6497825 prefixEnd_6497825 := by exact prefixLift 6497825
  have htrace : WordTrace (prefixWord ++ tailWord_6497825) baseStart_6497825 baseEnd_6497825 := by
    simpa [prefixWord, tailWord_6497825, baseEnd_6497825] using wordTrace_append hprefix tailTrace_6497825
  have hstable : (prefixWord ++ tailWord_6497825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6497825).length < 2 ^ (prefixWord ++ tailWord_6497825).sum := by decide
  have hdescent : baseEnd_6497825 < baseStart_6497825 := by decide
  rcases family_descends (prefixWord ++ tailWord_6497825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6497832 : List Nat := [2, 1, 5, 2, 2, 2, 1, 2, 2, 4]
def baseStart_6497832 : Nat := 118140960795 + 6497832 * 2 ^ 59
def prefixEnd_6497832 : Nat := 4983230072969 + 3 ^ 40 * 6497832 * 2
def baseEnd_6497832 : Nat := 1112170342721908812039007

theorem tailTrace_6497832 : CollatzResearch.WordTrace tailWord_6497832 prefixEnd_6497832 1112170342721908812039007 := by
  unfold tailWord_6497832
  simp only [CollatzResearch.WordTrace]
  refine ⟨118497701497735940099843875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157996935330314586799791833 118497701497735940099843875)
  ·
    refine ⟨177746552246603910149765813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118497701497735940099843875 177746552246603910149765813)
    ·
      refine ⟨16663739273119116576540545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 177746552246603910149765813 16663739273119116576540545)
      ·
        refine ⟨12497804454839337432405409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16663739273119116576540545 12497804454839337432405409)
        ·
          refine ⟨9373353341129503074304057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12497804454839337432405409 9373353341129503074304057)
          ·
            refine ⟨7030015005847127305728043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9373353341129503074304057 7030015005847127305728043)
            ·
              refine ⟨10545022508770690958592065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7030015005847127305728043 10545022508770690958592065)
              ·
                refine ⟨7908766881578018218944049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10545022508770690958592065 7908766881578018218944049)
                ·
                  refine ⟨5931575161183513664208037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7908766881578018218944049 5931575161183513664208037)
                  ·
                    refine ⟨1112170342721908812039007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5931575161183513664208037 1112170342721908812039007)
                    ·
                      rfl

theorem cell23_6497832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 1, 2, 2, 4].length) (baseStart_6497832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6497832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6497832 prefixEnd_6497832 := by exact prefixLift 6497832
  have htrace : WordTrace (prefixWord ++ tailWord_6497832) baseStart_6497832 baseEnd_6497832 := by
    simpa [prefixWord, tailWord_6497832, baseEnd_6497832] using wordTrace_append hprefix tailTrace_6497832
  have hstable : (prefixWord ++ tailWord_6497832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6497832).length < 2 ^ (prefixWord ++ tailWord_6497832).sum := by decide
  have hdescent : baseEnd_6497832 < baseStart_6497832 := by decide
  rcases family_descends (prefixWord ++ tailWord_6497832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6497862 : List Nat := [6, 1, 1, 1, 3, 2, 2, 7]
def baseStart_6497862 : Nat := 118140960795 + 6497862 * 2 ^ 59
def prefixEnd_6497862 : Nat := 4983230072969 + 3 ^ 40 * 6497862 * 2
def baseEnd_6497862 : Nat := 123575053058717085879329

theorem tailTrace_6497862 : CollatzResearch.WordTrace tailWord_6497862 prefixEnd_6497862 123575053058717085879329 := by
  unfold tailWord_6497862
  simp only [CollatzResearch.WordTrace]
  refine ⟨7406140537042599853852495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 157997664790242130215519893 7406140537042599853852495)
  ·
    refine ⟨11109210805563899780778743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7406140537042599853852495 11109210805563899780778743)
    ·
      refine ⟨16663816208345849671168115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11109210805563899780778743 16663816208345849671168115)
      ·
        refine ⟨24995724312518774506752173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16663816208345849671168115 24995724312518774506752173)
        ·
          refine ⟨9373396617194540440032065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24995724312518774506752173 9373396617194540440032065)
          ·
            refine ⟨7030047462895905330024049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9373396617194540440032065 7030047462895905330024049)
            ·
              refine ⟨5272535597171928997518037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7030047462895905330024049 5272535597171928997518037)
              ·
                refine ⟨123575053058717085879329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5272535597171928997518037 123575053058717085879329)
                ·
                  rfl

theorem cell23_6497862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 2, 7].length) (baseStart_6497862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6497862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6497862 prefixEnd_6497862 := by exact prefixLift 6497862
  have htrace : WordTrace (prefixWord ++ tailWord_6497862) baseStart_6497862 baseEnd_6497862 := by
    simpa [prefixWord, tailWord_6497862, baseEnd_6497862] using wordTrace_append hprefix tailTrace_6497862
  have hstable : (prefixWord ++ tailWord_6497862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6497862).length < 2 ^ (prefixWord ++ tailWord_6497862).sum := by decide
  have hdescent : baseEnd_6497862 < baseStart_6497862 := by decide
  rcases family_descends (prefixWord ++ tailWord_6497862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6497895 : List Nat := [1, 1, 5, 1, 1, 1, 4, 1, 4, 2, 2]
def baseStart_6497895 : Nat := 118140960795 + 6497895 * 2 ^ 59
def prefixEnd_6497895 : Nat := 4983230072969 + 3 ^ 40 * 6497895 * 2
def baseEnd_6497895 : Nat := 3336543377446959689629231

theorem tailTrace_6497895 : CollatzResearch.WordTrace tailWord_6497895 prefixEnd_6497895 3336543377446959689629231 := by
  unfold tailWord_6497895
  simp only [CollatzResearch.WordTrace]
  refine ⟨236997700794243641959231139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157998467196162427972820759 236997700794243641959231139)
  ·
    refine ⟨355496551191365462938846709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236997700794243641959231139 355496551191365462938846709)
    ·
      refine ⟨33327801674190512150516879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 355496551191365462938846709 33327801674190512150516879)
      ·
        refine ⟨49991702511285768225775319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33327801674190512150516879 49991702511285768225775319)
        ·
          refine ⟨74987553766928652338662979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49991702511285768225775319 74987553766928652338662979)
          ·
            refine ⟨112481330650392978507994469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74987553766928652338662979 112481330650392978507994469)
            ·
              refine ⟨21090249496948683470248963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 112481330650392978507994469 21090249496948683470248963)
              ·
                refine ⟨31635374245423025205373445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21090249496948683470248963 31635374245423025205373445)
                ·
                  refine ⟨5931632671016817226007521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31635374245423025205373445 5931632671016817226007521)
                  ·
                    refine ⟨4448724503262612919505641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5931632671016817226007521 4448724503262612919505641)
                    ·
                      refine ⟨3336543377446959689629231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4448724503262612919505641 3336543377446959689629231)
                      ·
                        rfl

theorem cell23_6497895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 1, 4, 2, 2].length) (baseStart_6497895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6497895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6497895 prefixEnd_6497895 := by exact prefixLift 6497895
  have htrace : WordTrace (prefixWord ++ tailWord_6497895) baseStart_6497895 baseEnd_6497895 := by
    simpa [prefixWord, tailWord_6497895, baseEnd_6497895] using wordTrace_append hprefix tailTrace_6497895
  have hstable : (prefixWord ++ tailWord_6497895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6497895).length < 2 ^ (prefixWord ++ tailWord_6497895).sum := by decide
  have hdescent : baseEnd_6497895 < baseStart_6497895 := by decide
  rcases family_descends (prefixWord ++ tailWord_6497895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6497911 : List Nat := [1, 1, 3, 1, 1, 3, 1, 3, 1, 5, 3]
def baseStart_6497911 : Nat := 118140960795 + 6497911 * 2 ^ 59
def prefixEnd_6497911 : Nat := 4983230072969 + 3 ^ 40 * 6497911 * 2
def baseEnd_6497911 : Nat := 3336551593137431627029157

theorem tailTrace_6497911 : CollatzResearch.WordTrace tailWord_6497911 prefixEnd_6497911 3336551593137431627029157 := by
  unfold tailWord_6497911
  simp only [CollatzResearch.WordTrace]
  refine ⟨236998284362185676691813587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157998856241457117794542391 236998284362185676691813587)
  ·
    refine ⟨355497426543278515037720381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236998284362185676691813587 355497426543278515037720381)
    ·
      refine ⟨133311534953729443139145143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 355497426543278515037720381 133311534953729443139145143)
      ·
        refine ⟨199967302430594164708717715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133311534953729443139145143 199967302430594164708717715)
        ·
          refine ⟨299950953645891247063076573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199967302430594164708717715 299950953645891247063076573)
          ·
            refine ⟨112481607617209217648653715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 299950953645891247063076573 112481607617209217648653715)
            ·
              refine ⟨168722411425813826472980573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112481607617209217648653715 168722411425813826472980573)
              ·
                refine ⟨63270904284680184927367715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 168722411425813826472980573 63270904284680184927367715)
                ·
                  refine ⟨94906356427020277391051573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63270904284680184927367715 94906356427020277391051573)
                  ·
                    refine ⟨8897470915033151005411085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 94906356427020277391051573 8897470915033151005411085)
                    ·
                      refine ⟨3336551593137431627029157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8897470915033151005411085 3336551593137431627029157)
                      ·
                        rfl

theorem cell23_6497911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 3, 1, 5, 3].length) (baseStart_6497911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6497911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6497911 prefixEnd_6497911 := by exact prefixLift 6497911
  have htrace : WordTrace (prefixWord ++ tailWord_6497911) baseStart_6497911 baseEnd_6497911 := by
    simpa [prefixWord, tailWord_6497911, baseEnd_6497911] using wordTrace_append hprefix tailTrace_6497911
  have hstable : (prefixWord ++ tailWord_6497911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6497911).length < 2 ^ (prefixWord ++ tailWord_6497911).sum := by decide
  have hdescent : baseEnd_6497911 < baseStart_6497911 := by decide
  rcases family_descends (prefixWord ++ tailWord_6497911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6497952 : List Nat := [2, 1, 1, 4, 3, 3, 2, 2, 5]
def baseStart_6497952 : Nat := 118140960795 + 6497952 * 2 ^ 59
def prefixEnd_6497952 : Nat := 4983230072969 + 3 ^ 40 * 6497952 * 2
def baseEnd_6497952 : Nat := 370730293982696218512941

theorem tailTrace_6497952 : CollatzResearch.WordTrace tailWord_6497952 prefixEnd_6497952 370730293982696218512941 := by
  unfold tailWord_6497952
  simp only [CollatzResearch.WordTrace]
  refine ⟨118499889877518570347028055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157999853170024760462704073 118499889877518570347028055)
  ·
    refine ⟨177749834816277855520542083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118499889877518570347028055 177749834816277855520542083)
    ·
      refine ⟨266624752224416783280813125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177749834816277855520542083 266624752224416783280813125)
      ·
        refine ⟨49992141042078146865152461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 266624752224416783280813125 49992141042078146865152461)
        ·
          refine ⟨18747052890779305074432173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49992141042078146865152461 18747052890779305074432173)
          ·
            refine ⟨7030144834042239402912065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18747052890779305074432173 7030144834042239402912065)
            ·
              refine ⟨5272608625531679552184049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7030144834042239402912065 5272608625531679552184049)
              ·
                refine ⟨3954456469148759664138037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5272608625531679552184049 3954456469148759664138037)
                ·
                  refine ⟨370730293982696218512941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3954456469148759664138037 370730293982696218512941)
                  ·
                    rfl

theorem cell23_6497952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 2, 2, 5].length) (baseStart_6497952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6497952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6497952 prefixEnd_6497952 := by exact prefixLift 6497952
  have htrace : WordTrace (prefixWord ++ tailWord_6497952) baseStart_6497952 baseEnd_6497952 := by
    simpa [prefixWord, tailWord_6497952, baseEnd_6497952] using wordTrace_append hprefix tailTrace_6497952
  have hstable : (prefixWord ++ tailWord_6497952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6497952).length < 2 ^ (prefixWord ++ tailWord_6497952).sum := by decide
  have hdescent : baseEnd_6497952 < baseStart_6497952 := by decide
  rcases family_descends (prefixWord ++ tailWord_6497952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6497968 : List Nat := [2, 1, 1, 1, 2, 1, 5, 1, 1, 6, 2]
def baseStart_6497968 : Nat := 118140960795 + 6497968 * 2 ^ 59
def prefixEnd_6497968 : Nat := 4983230072969 + 3 ^ 40 * 6497968 * 2
def baseEnd_6497968 : Nat := 3336580861534737904016395

theorem tailTrace_6497968 : CollatzResearch.WordTrace tailWord_6497968 prefixEnd_6497968 3336580861534737904016395 := by
  unfold tailWord_6497968
  simp only [CollatzResearch.WordTrace]
  refine ⟨118500181661489587713319279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158000242215319450284425705 118500181661489587713319279)
  ·
    refine ⟨177750272492234381569978919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118500181661489587713319279 177750272492234381569978919)
    ·
      refine ⟨266625408738351572354968379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177750272492234381569978919 266625408738351572354968379)
      ·
        refine ⟨399938113107527358532452569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266625408738351572354968379 399938113107527358532452569)
        ·
          refine ⟨299953584830645518899339427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 399938113107527358532452569 299953584830645518899339427)
          ·
            refine ⟨449930377245968278349009141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 299953584830645518899339427 449930377245968278349009141)
            ·
              refine ⟨42180972866809526095219607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 449930377245968278349009141 42180972866809526095219607)
              ·
                refine ⟨63271459300214289142829411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42180972866809526095219607 63271459300214289142829411)
                ·
                  refine ⟨94907188950321433714244117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63271459300214289142829411 94907188950321433714244117)
                  ·
                    refine ⟨4448774482046317205355193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 94907188950321433714244117 4448774482046317205355193)
                    ·
                      refine ⟨3336580861534737904016395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4448774482046317205355193 3336580861534737904016395)
                      ·
                        rfl

theorem cell23_6497968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 1, 1, 6, 2].length) (baseStart_6497968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6497968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6497968 prefixEnd_6497968 := by exact prefixLift 6497968
  have htrace : WordTrace (prefixWord ++ tailWord_6497968) baseStart_6497968 baseEnd_6497968 := by
    simpa [prefixWord, tailWord_6497968, baseEnd_6497968] using wordTrace_append hprefix tailTrace_6497968
  have hstable : (prefixWord ++ tailWord_6497968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6497968).length < 2 ^ (prefixWord ++ tailWord_6497968).sum := by decide
  have hdescent : baseEnd_6497968 < baseStart_6497968 := by decide
  rcases family_descends (prefixWord ++ tailWord_6497968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6497978 : List Nat := [3, 1, 1, 1, 2, 4, 1, 1, 5, 4]
def baseStart_6497978 : Nat := 118140960795 + 6497978 * 2 ^ 59
def prefixEnd_6497978 : Nat := 4983230072969 + 3 ^ 40 * 6497978 * 2
def baseEnd_6497978 : Nat := 1112195332113760954963783

theorem tailTrace_6497978 : CollatzResearch.WordTrace tailWord_6497978 prefixEnd_6497978 1112195332113760954963783 := by
  unfold tailWord_6497978
  simp only [CollatzResearch.WordTrace]
  refine ⟨59250182013235736783625647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158000485368628631423001725 59250182013235736783625647)
  ·
    refine ⟨88875273019853605175438471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59250182013235736783625647 88875273019853605175438471)
    ·
      refine ⟨133312909529780407763157707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88875273019853605175438471 133312909529780407763157707)
      ·
        refine ⟨199969364294670611644736561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133312909529780407763157707 199969364294670611644736561)
        ·
          refine ⟨149977023221002958733552421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 199969364294670611644736561 149977023221002958733552421)
          ·
            refine ⟨28120691853938054762541079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 149977023221002958733552421 28120691853938054762541079)
            ·
              refine ⟨42181037780907082143811619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28120691853938054762541079 42181037780907082143811619)
              ·
                refine ⟨63271556671360623215717429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42181037780907082143811619 63271556671360623215717429)
                ·
                  refine ⟨5931708437940058426473509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 63271556671360623215717429 5931708437940058426473509)
                  ·
                    refine ⟨1112195332113760954963783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5931708437940058426473509 1112195332113760954963783)
                    ·
                      rfl

theorem cell23_6497978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 1, 5, 4].length) (baseStart_6497978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6497978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6497978 prefixEnd_6497978 := by exact prefixLift 6497978
  have htrace : WordTrace (prefixWord ++ tailWord_6497978) baseStart_6497978 baseEnd_6497978 := by
    simpa [prefixWord, tailWord_6497978, baseEnd_6497978] using wordTrace_append hprefix tailTrace_6497978
  have hstable : (prefixWord ++ tailWord_6497978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6497978).length < 2 ^ (prefixWord ++ tailWord_6497978).sum := by decide
  have hdescent : baseEnd_6497978 < baseStart_6497978 := by decide
  rcases family_descends (prefixWord ++ tailWord_6497978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6497986 : List Nat := [3, 5, 1, 2, 1, 1, 2, 3, 5]
def baseStart_6497986 : Nat := 118140960795 + 6497986 * 2 ^ 59
def prefixEnd_6497986 : Nat := 4983230072969 + 3 ^ 40 * 6497986 * 2
def baseEnd_6497986 : Nat := 370732233798502092621257

theorem tailTrace_6497986 : CollatzResearch.WordTrace tailWord_6497986 prefixEnd_6497986 370732233798502092621257 := by
  unfold tailWord_6497986
  simp only [CollatzResearch.WordTrace]
  refine ⟨59250254959228491125198453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158000679891275976333862541 59250254959228491125198453)
  ·
    refine ⟨5554711402427671042987355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 59250254959228491125198453 5554711402427671042987355)
    ·
      refine ⟨8332067103641506564481033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5554711402427671042987355 8332067103641506564481033)
      ·
        refine ⟨6249050327731129923360775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8332067103641506564481033 6249050327731129923360775)
        ·
          refine ⟨9373575491596694885041163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6249050327731129923360775 9373575491596694885041163)
          ·
            refine ⟨14060363237395042327561745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9373575491596694885041163 14060363237395042327561745)
            ·
              refine ⟨10545272428046281745671309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14060363237395042327561745 10545272428046281745671309)
              ·
                refine ⟨3954477160517355654626741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10545272428046281745671309 3954477160517355654626741)
                ·
                  refine ⟨370732233798502092621257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3954477160517355654626741 370732233798502092621257)
                  ·
                    rfl

theorem cell23_6497986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 2, 3, 5].length) (baseStart_6497986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6497986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6497986 prefixEnd_6497986 := by exact prefixLift 6497986
  have htrace : WordTrace (prefixWord ++ tailWord_6497986) baseStart_6497986 baseEnd_6497986 := by
    simpa [prefixWord, tailWord_6497986, baseEnd_6497986] using wordTrace_append hprefix tailTrace_6497986
  have hstable : (prefixWord ++ tailWord_6497986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6497986).length < 2 ^ (prefixWord ++ tailWord_6497986).sum := by decide
  have hdescent : baseEnd_6497986 < baseStart_6497986 := by decide
  rcases family_descends (prefixWord ++ tailWord_6497986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6497991 : List Nat := [1, 1, 4, 1, 1, 1, 4, 2, 8]
def baseStart_6497991 : Nat := 118140960795 + 6497991 * 2 ^ 59
def prefixEnd_6497991 : Nat := 4983230072969 + 3 ^ 40 * 6497991 * 2
def baseEnd_6497991 : Nat := 370732519065532368225421

theorem tailTrace_6497991 : CollatzResearch.WordTrace tailWord_6497991 prefixEnd_6497991 370732519065532368225421 := by
  unfold tailWord_6497991
  simp only [CollatzResearch.WordTrace]
  refine ⟨237001202201895850354725827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158000801467930566903150551 237001202201895850354725827)
  ·
    refine ⟨355501803302843775532088741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237001202201895850354725827 355501803302843775532088741)
    ·
      refine ⟨66656588119283207912266639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 355501803302843775532088741 66656588119283207912266639)
      ·
        refine ⟨99984882178924811868399959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66656588119283207912266639 99984882178924811868399959)
        ·
          refine ⟨149977323268387217802599939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99984882178924811868399959 149977323268387217802599939)
          ·
            refine ⟨224965984902580826703899909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149977323268387217802599939 224965984902580826703899909)
            ·
              refine ⟨42181122169233905006981233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 224965984902580826703899909 42181122169233905006981233)
              ·
                refine ⟨31635841626925428755235925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42181122169233905006981233 31635841626925428755235925)
                ·
                  refine ⟨370732519065532368225421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31635841626925428755235925 370732519065532368225421)
                  ·
                    rfl

theorem cell23_6497991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 2, 8].length) (baseStart_6497991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6497991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6497991 prefixEnd_6497991 := by exact prefixLift 6497991
  have htrace : WordTrace (prefixWord ++ tailWord_6497991) baseStart_6497991 baseEnd_6497991 := by
    simpa [prefixWord, tailWord_6497991, baseEnd_6497991] using wordTrace_append hprefix tailTrace_6497991
  have hstable : (prefixWord ++ tailWord_6497991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6497991).length < 2 ^ (prefixWord ++ tailWord_6497991).sum := by decide
  have hdescent : baseEnd_6497991 < baseStart_6497991 := by decide
  rcases family_descends (prefixWord ++ tailWord_6497991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6498035 : List Nat := [1, 1, 1, 2, 2, 3, 4, 2, 3, 1, 3]
def baseStart_6498035 : Nat := 118140960795 + 6498035 * 2 ^ 59
def prefixEnd_6498035 : Nat := 4983230072969 + 3 ^ 40 * 6498035 * 2
def baseEnd_6498035 : Nat := 3336615264738589141878587

theorem tailTrace_6498035 : CollatzResearch.WordTrace tailWord_6498035 prefixEnd_6498035 3336615264738589141878587 := by
  unfold tailWord_6498035
  simp only [CollatzResearch.WordTrace]
  refine ⟨237002807013736445869327559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158001871342490963912885039 237002807013736445869327559)
  ·
    refine ⟨355504210520604668803991339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237002807013736445869327559 355504210520604668803991339)
    ·
      refine ⟨533256315780907003205987009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 355504210520604668803991339 533256315780907003205987009)
      ·
        refine ⟨399942236835680252404490257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 533256315780907003205987009 399942236835680252404490257)
        ·
          refine ⟨299956677626760189303367693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 399942236835680252404490257 299956677626760189303367693)
          ·
            refine ⟨112483754110035070988762885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 299956677626760189303367693 112483754110035070988762885)
            ·
              refine ⟨21090703895631575810393041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 112483754110035070988762885 21090703895631575810393041)
              ·
                refine ⟨15818027921723681857794781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21090703895631575810393041 15818027921723681857794781)
                ·
                  refine ⟨5931760470646380696673043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15818027921723681857794781 5931760470646380696673043)
                  ·
                    refine ⟨8897640705969571045009565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5931760470646380696673043 8897640705969571045009565)
                    ·
                      refine ⟨3336615264738589141878587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8897640705969571045009565 3336615264738589141878587)
                      ·
                        rfl

theorem cell23_6498035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 2, 3, 1, 3].length) (baseStart_6498035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6498035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6498035 prefixEnd_6498035 := by exact prefixLift 6498035
  have htrace : WordTrace (prefixWord ++ tailWord_6498035) baseStart_6498035 baseEnd_6498035 := by
    simpa [prefixWord, tailWord_6498035, baseEnd_6498035] using wordTrace_append hprefix tailTrace_6498035
  have hstable : (prefixWord ++ tailWord_6498035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6498035).length < 2 ^ (prefixWord ++ tailWord_6498035).sum := by decide
  have hdescent : baseEnd_6498035 < baseStart_6498035 := by decide
  rcases family_descends (prefixWord ++ tailWord_6498035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6498046 : List Nat := [4, 2, 2, 1, 3, 2, 1, 3, 1, 4]
def baseStart_6498046 : Nat := 118140960795 + 6498046 * 2 ^ 59
def prefixEnd_6498046 : Nat := 4983230072969 + 3 ^ 40 * 6498046 * 2
def baseEnd_6498046 : Nat := 1112206971008596199613679

theorem tailTrace_6498046 : CollatzResearch.WordTrace tailWord_6498046 prefixEnd_6498046 1112206971008596199613679 := by
  unfold tailWord_6498046
  simp only [CollatzResearch.WordTrace]
  refine ⟨29625401027087074343497249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 158002138811131063165318661 29625401027087074343497249)
  ·
    refine ⟨22219050770315305757622937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29625401027087074343497249 22219050770315305757622937)
    ·
      refine ⟨16664288077736479318217203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22219050770315305757622937 16664288077736479318217203)
      ·
        refine ⟨24996432116604718977325805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16664288077736479318217203 24996432116604718977325805)
        ·
          refine ⟨9373662043726769616497177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24996432116604718977325805 9373662043726769616497177)
          ·
            refine ⟨7030246532795077212372883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9373662043726769616497177 7030246532795077212372883)
            ·
              refine ⟨10545369799192615818559325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7030246532795077212372883 10545369799192615818559325)
              ·
                refine ⟨3954513674697230931959747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10545369799192615818559325 3954513674697230931959747)
                ·
                  refine ⟨5931770512045846397939621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3954513674697230931959747 5931770512045846397939621)
                  ·
                    refine ⟨1112206971008596199613679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5931770512045846397939621 1112206971008596199613679)
                    ·
                      rfl

theorem cell23_6498046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 1, 3, 1, 4].length) (baseStart_6498046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6498046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6498046 prefixEnd_6498046 := by exact prefixLift 6498046
  have htrace : WordTrace (prefixWord ++ tailWord_6498046) baseStart_6498046 baseEnd_6498046 := by
    simpa [prefixWord, tailWord_6498046, baseEnd_6498046] using wordTrace_append hprefix tailTrace_6498046
  have hstable : (prefixWord ++ tailWord_6498046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6498046).length < 2 ^ (prefixWord ++ tailWord_6498046).sum := by decide
  have hdescent : baseEnd_6498046 < baseStart_6498046 := by decide
  rcases family_descends (prefixWord ++ tailWord_6498046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6498092 : List Nat := [2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 4]
def baseStart_6498092 : Nat := 118140960795 + 6498092 * 2 ^ 59
def prefixEnd_6498092 : Nat := 4983230072969 + 3 ^ 40 * 6498092 * 2
def baseEnd_6498092 : Nat := 3336644533135895418865825

theorem tailTrace_6498092 : CollatzResearch.WordTrace tailWord_6498092 prefixEnd_6498092 3336644533135895418865825 := by
  unfold tailWord_6498092
  simp only [CollatzResearch.WordTrace]
  refine ⟨118502442987264972302076265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158003257316353296402768353 118502442987264972302076265)
  ·
    refine ⟨88876832240448729226557199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118502442987264972302076265 88876832240448729226557199)
    ·
      refine ⟨133315248360673093839835799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88876832240448729226557199 133315248360673093839835799)
      ·
        refine ⟨199972872541009640759753699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133315248360673093839835799 199972872541009640759753699)
        ·
          refine ⟨299959308811514461139630549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199972872541009640759753699 299959308811514461139630549)
          ·
            refine ⟨7030296300269870182960091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 299959308811514461139630549 7030296300269870182960091)
            ·
              refine ⟨10545444450404805274440137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7030296300269870182960091 10545444450404805274440137)
              ·
                refine ⟨7909083337803603955830103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10545444450404805274440137 7909083337803603955830103)
                ·
                  refine ⟨11863625006705405933745155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7909083337803603955830103 11863625006705405933745155)
                  ·
                    refine ⟨17795437510058108900617733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11863625006705405933745155 17795437510058108900617733)
                    ·
                      refine ⟨3336644533135895418865825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17795437510058108900617733 3336644533135895418865825)
                      ·
                        rfl

theorem cell23_6498092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 4].length) (baseStart_6498092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6498092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6498092 prefixEnd_6498092 := by exact prefixLift 6498092
  have htrace : WordTrace (prefixWord ++ tailWord_6498092) baseStart_6498092 baseEnd_6498092 := by
    simpa [prefixWord, tailWord_6498092, baseEnd_6498092] using wordTrace_append hprefix tailTrace_6498092
  have hstable : (prefixWord ++ tailWord_6498092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6498092).length < 2 ^ (prefixWord ++ tailWord_6498092).sum := by decide
  have hdescent : baseEnd_6498092 < baseStart_6498092 := by decide
  rcases family_descends (prefixWord ++ tailWord_6498092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6498098 : List Nat := [3, 2, 1, 1, 3, 2, 2, 9]
def baseStart_6498098 : Nat := 118140960795 + 6498098 * 2 ^ 59
def prefixEnd_6498098 : Nat := 4983230072969 + 3 ^ 40 * 6498098 * 2
def baseEnd_6498098 : Nat := 123579541259993422051511

theorem tailTrace_6498098 : CollatzResearch.WordTrace tailWord_6498098 prefixEnd_6498098 123579541259993422051511 := by
  unfold tailWord_6498098
  simp only [CollatzResearch.WordTrace]
  refine ⟨59251276203127051907217737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158003403208338805085913965 59251276203127051907217737)
  ·
    refine ⟨44438457152345288930413303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59251276203127051907217737 44438457152345288930413303)
    ·
      refine ⟨66657685728517933395619955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44438457152345288930413303 66657685728517933395619955)
      ·
        refine ⟨99986528592776900093429933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66657685728517933395619955 99986528592776900093429933)
        ·
          refine ⟨37494948222291337535036225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99986528592776900093429933 37494948222291337535036225)
          ·
            refine ⟨28121211166718503151277169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37494948222291337535036225 28121211166718503151277169)
            ·
              refine ⟨21090908375038877363457877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28121211166718503151277169 21090908375038877363457877)
              ·
                refine ⟨123579541259993422051511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21090908375038877363457877 123579541259993422051511)
                ·
                  rfl

theorem cell23_6498098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 9].length) (baseStart_6498098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6498098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6498098 prefixEnd_6498098 := by exact prefixLift 6498098
  have htrace : WordTrace (prefixWord ++ tailWord_6498098) baseStart_6498098 baseEnd_6498098 := by
    simpa [prefixWord, tailWord_6498098, baseEnd_6498098] using wordTrace_append hprefix tailTrace_6498098
  have hstable : (prefixWord ++ tailWord_6498098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6498098).length < 2 ^ (prefixWord ++ tailWord_6498098).sum := by decide
  have hdescent : baseEnd_6498098 < baseStart_6498098 := by decide
  rcases family_descends (prefixWord ++ tailWord_6498098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6498102 : List Nat := [5, 1, 2, 2, 1, 2, 1, 2, 1, 6]
def baseStart_6498102 : Nat := 118140960795 + 6498102 * 2 ^ 59
def prefixEnd_6498102 : Nat := 4983230072969 + 3 ^ 40 * 6498102 * 2
def baseEnd_6498102 : Nat := 1112216555980813459913593

theorem tailTrace_6498102 : CollatzResearch.WordTrace tailWord_6498102 prefixEnd_6498102 1112216555980813459913593 := by
  unfold tailWord_6498102
  simp only [CollatzResearch.WordTrace]
  refine ⟨14812828169030857269501035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 158003500469662477541344373 14812828169030857269501035)
  ·
    refine ⟨22219242253546285904251553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14812828169030857269501035 22219242253546285904251553)
    ·
      refine ⟨16664431690159714428188665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22219242253546285904251553 16664431690159714428188665)
      ·
        refine ⟨12498323767619785821141499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16664431690159714428188665 12498323767619785821141499)
        ·
          refine ⟨18747485651429678731712249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12498323767619785821141499 18747485651429678731712249)
          ·
            refine ⟨14060614238572259048784187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18747485651429678731712249 14060614238572259048784187)
            ·
              refine ⟨21090921357858388573176281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14060614238572259048784187 21090921357858388573176281)
              ·
                refine ⟨15818191018393791429882211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21090921357858388573176281 15818191018393791429882211)
                ·
                  refine ⟨23727286527590687144823317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15818191018393791429882211 23727286527590687144823317)
                  ·
                    refine ⟨1112216555980813459913593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23727286527590687144823317 1112216555980813459913593)
                    ·
                      rfl

theorem cell23_6498102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 2, 1, 6].length) (baseStart_6498102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6498102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6498102 prefixEnd_6498102 := by exact prefixLift 6498102
  have htrace : WordTrace (prefixWord ++ tailWord_6498102) baseStart_6498102 baseEnd_6498102 := by
    simpa [prefixWord, tailWord_6498102, baseEnd_6498102] using wordTrace_append hprefix tailTrace_6498102
  have hstable : (prefixWord ++ tailWord_6498102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6498102).length < 2 ^ (prefixWord ++ tailWord_6498102).sum := by decide
  have hdescent : baseEnd_6498102 < baseStart_6498102 := by decide
  rcases family_descends (prefixWord ++ tailWord_6498102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6498109 : List Nat := [1, 4, 1, 4, 1, 2, 3, 1, 1, 1, 4]
def baseStart_6498109 : Nat := 118140960795 + 6498109 * 2 ^ 59
def prefixEnd_6498109 : Nat := 4983230072969 + 3 ^ 40 * 6498109 * 2
def baseEnd_6498109 : Nat := 3336653262307021852353247

theorem tailTrace_6498109 : CollatzResearch.WordTrace tailWord_6498109 prefixEnd_6498109 3336653262307021852353247 := by
  unfold tailWord_6498109
  simp only [CollatzResearch.WordTrace]
  refine ⟨237005506015468356507521381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158003670676978904338347587 237005506015468356507521381)
  ·
    refine ⟨44438532377900316845160259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 237005506015468356507521381 44438532377900316845160259)
    ·
      refine ⟨66657798566850475267740389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44438532377900316845160259 66657798566850475267740389)
      ·
        refine ⟨12498337231284464112701323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66657798566850475267740389 12498337231284464112701323)
        ·
          refine ⟨18747505846926696169051985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12498337231284464112701323 18747505846926696169051985)
          ·
            refine ⟨14060629385195022126788989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18747505846926696169051985 14060629385195022126788989)
            ·
              refine ⟨5272736019448133297545871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14060629385195022126788989 5272736019448133297545871)
              ·
                refine ⟨7909104029172199946318807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5272736019448133297545871 7909104029172199946318807)
                ·
                  refine ⟨11863656043758299919478211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7909104029172199946318807 11863656043758299919478211)
                  ·
                    refine ⟨17795484065637449879217317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11863656043758299919478211 17795484065637449879217317)
                    ·
                      refine ⟨3336653262307021852353247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17795484065637449879217317 3336653262307021852353247)
                      ·
                        rfl

theorem cell23_6498109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 3, 1, 1, 1, 4].length) (baseStart_6498109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6498109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6498109 prefixEnd_6498109 := by exact prefixLift 6498109
  have htrace : WordTrace (prefixWord ++ tailWord_6498109) baseStart_6498109 baseEnd_6498109 := by
    simpa [prefixWord, tailWord_6498109, baseEnd_6498109] using wordTrace_append hprefix tailTrace_6498109
  have hstable : (prefixWord ++ tailWord_6498109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6498109).length < 2 ^ (prefixWord ++ tailWord_6498109).sum := by decide
  have hdescent : baseEnd_6498109 < baseStart_6498109 := by decide
  rcases family_descends (prefixWord ++ tailWord_6498109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6498152 : List Nat := [2, 1, 4, 2, 1, 1, 1, 3, 3, 3, 2]
def baseStart_6498152 : Nat := 118140960795 + 6498152 * 2 ^ 59
def prefixEnd_6498152 : Nat := 4983230072969 + 3 ^ 40 * 6498152 * 2
def baseEnd_6498152 : Nat := 3336675341975165184115549

theorem tailTrace_6498152 : CollatzResearch.WordTrace tailWord_6498152 prefixEnd_6498152 3336675341975165184115549 := by
  unfold tailWord_6498152
  simp only [CollatzResearch.WordTrace]
  refine ⟨118503537177156287425668355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158004716236208383234224473 118503537177156287425668355)
  ·
    refine ⟨177755305765734431138502533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118503537177156287425668355 177755305765734431138502533)
    ·
      refine ⟨33329119831075205838469225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 177755305765734431138502533 33329119831075205838469225)
      ·
        refine ⟨24996839873306404378851919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33329119831075205838469225 24996839873306404378851919)
        ·
          refine ⟨37495259809959606568277879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24996839873306404378851919 37495259809959606568277879)
          ·
            refine ⟨56242889714939409852416819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37495259809959606568277879 56242889714939409852416819)
            ·
              refine ⟨84364334572409114778625229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56242889714939409852416819 84364334572409114778625229)
              ·
                refine ⟨31636625464653418041984461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84364334572409114778625229 31636625464653418041984461)
                ·
                  refine ⟨11863734549245031765744173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31636625464653418041984461 11863734549245031765744173)
                  ·
                    refine ⟨4448900455966886912154065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11863734549245031765744173 4448900455966886912154065)
                    ·
                      refine ⟨3336675341975165184115549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4448900455966886912154065 3336675341975165184115549)
                      ·
                        rfl

theorem cell23_6498152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 3, 3, 3, 2].length) (baseStart_6498152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6498152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6498152 prefixEnd_6498152 := by exact prefixLift 6498152
  have htrace : WordTrace (prefixWord ++ tailWord_6498152) baseStart_6498152 baseEnd_6498152 := by
    simpa [prefixWord, tailWord_6498152, baseEnd_6498152] using wordTrace_append hprefix tailTrace_6498152
  have hstable : (prefixWord ++ tailWord_6498152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6498152).length < 2 ^ (prefixWord ++ tailWord_6498152).sum := by decide
  have hdescent : baseEnd_6498152 < baseStart_6498152 := by decide
  rcases family_descends (prefixWord ++ tailWord_6498152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6498168 : List Nat := [2, 1, 2, 1, 1, 1, 1, 2, 6, 1, 5]
def baseStart_6498168 : Nat := 118140960795 + 6498168 * 2 ^ 59
def prefixEnd_6498168 : Nat := 4983230072969 + 3 ^ 40 * 6498168 * 2
def baseEnd_6498168 : Nat := 3336683557665637121515475

theorem tailTrace_6498168 : CollatzResearch.WordTrace tailWord_6498168 prefixEnd_6498168 3336683557665637121515475 := by
  unfold tailWord_6498168
  simp only [CollatzResearch.WordTrace]
  refine ⟨118503828961127304791959579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158005105281503073055946105 118503828961127304791959579)
  ·
    refine ⟨177755743441690957187939369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118503828961127304791959579 177755743441690957187939369)
    ·
      refine ⟨133316807581268217890954527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177755743441690957187939369 133316807581268217890954527)
      ·
        refine ⟨199975211371902326836431791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133316807581268217890954527 199975211371902326836431791)
        ·
          refine ⟨299962817057853490254647687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199975211371902326836431791 299962817057853490254647687)
          ·
            refine ⟨449944225586780235381971531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 299962817057853490254647687 449944225586780235381971531)
            ·
              refine ⟨674916338380170353072957297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 449944225586780235381971531 674916338380170353072957297)
              ·
                refine ⟨506187253785127764804717973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 674916338380170353072957297 506187253785127764804717973)
                ·
                  refine ⟨23727527521177863975221155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 506187253785127764804717973 23727527521177863975221155)
                  ·
                    refine ⟨35591291281766795962831733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23727527521177863975221155 35591291281766795962831733)
                    ·
                      refine ⟨3336683557665637121515475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35591291281766795962831733 3336683557665637121515475)
                      ·
                        rfl

theorem cell23_6498168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 6, 1, 5].length) (baseStart_6498168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6498168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6498168 prefixEnd_6498168 := by exact prefixLift 6498168
  have htrace : WordTrace (prefixWord ++ tailWord_6498168) baseStart_6498168 baseEnd_6498168 := by
    simpa [prefixWord, tailWord_6498168, baseEnd_6498168] using wordTrace_append hprefix tailTrace_6498168
  have hstable : (prefixWord ++ tailWord_6498168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6498168).length < 2 ^ (prefixWord ++ tailWord_6498168).sum := by decide
  have hdescent : baseEnd_6498168 < baseStart_6498168 := by decide
  rcases family_descends (prefixWord ++ tailWord_6498168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6498199 : List Nat := [1, 1, 3, 3, 1, 5, 1, 1, 1, 4, 2]
def baseStart_6498199 : Nat := 118140960795 + 6498199 * 2 ^ 59
def prefixEnd_6498199 : Nat := 4983230072969 + 3 ^ 40 * 6498199 * 2
def baseEnd_6498199 : Nat := 3336699475565926500227833

theorem tailTrace_6498199 : CollatzResearch.WordTrace tailWord_6498199 prefixEnd_6498199 3336699475565926500227833 := by
  unfold tailWord_6498199
  simp only [CollatzResearch.WordTrace]
  refine ⟨237008788585142301878297651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158005859056761534585531767 237008788585142301878297651)
  ·
    refine ⟨355513182877713452817446477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237008788585142301878297651 355513182877713452817446477)
    ·
      refine ⟨133317443579142544806542429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 355513182877713452817446477 133317443579142544806542429)
      ·
        refine ⟨49994041342178454302453411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133317443579142544806542429 49994041342178454302453411)
        ·
          refine ⟨74991062013267681453680117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49994041342178454302453411 74991062013267681453680117)
          ·
            refine ⟨7030412063743845136282511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 74991062013267681453680117 7030412063743845136282511)
            ·
              refine ⟨10545618095615767704423767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7030412063743845136282511 10545618095615767704423767)
              ·
                refine ⟨15818427143423651556635651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10545618095615767704423767 15818427143423651556635651)
                ·
                  refine ⟨23727640715135477334953477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15818427143423651556635651 23727640715135477334953477)
                  ·
                    refine ⟨4448932634087902000303777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23727640715135477334953477 4448932634087902000303777)
                    ·
                      refine ⟨3336699475565926500227833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4448932634087902000303777 3336699475565926500227833)
                      ·
                        rfl

theorem cell23_6498199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 1, 1, 1, 4, 2].length) (baseStart_6498199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6498199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6498199 prefixEnd_6498199 := by exact prefixLift 6498199
  have htrace : WordTrace (prefixWord ++ tailWord_6498199) baseStart_6498199 baseEnd_6498199 := by
    simpa [prefixWord, tailWord_6498199, baseEnd_6498199] using wordTrace_append hprefix tailTrace_6498199
  have hstable : (prefixWord ++ tailWord_6498199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6498199).length < 2 ^ (prefixWord ++ tailWord_6498199).sum := by decide
  have hdescent : baseEnd_6498199 < baseStart_6498199 := by decide
  rcases family_descends (prefixWord ++ tailWord_6498199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6498205 : List Nat := [1, 4, 2, 1, 2, 2, 2, 2, 7]
def baseStart_6498205 : Nat := 118140960795 + 6498205 * 2 ^ 59
def prefixEnd_6498205 : Nat := 4983230072969 + 3 ^ 40 * 6498205 * 2
def baseEnd_6498205 : Nat := 370744728494428164083645

theorem tailTrace_6498205 : CollatzResearch.WordTrace tailWord_6498205 prefixEnd_6498205 370744728494428164083645 := by
  unfold tailWord_6498205
  simp only [CollatzResearch.WordTrace]
  refine ⟨237009007423120564903016069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158006004948747043268677379 237009007423120564903016069)
  ·
    refine ⟨44439188891835105919315513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 237009007423120564903016069 44439188891835105919315513)
    ·
      refine ⟨33329391668876329439486635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44439188891835105919315513 33329391668876329439486635)
      ·
        refine ⟨49994087503314494159229953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33329391668876329439486635 49994087503314494159229953)
        ·
          refine ⟨37495565627485870619422465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49994087503314494159229953 37495565627485870619422465)
          ·
            refine ⟨28121674220614402964566849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37495565627485870619422465 28121674220614402964566849)
            ·
              refine ⟨21091255665460802223425137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28121674220614402964566849 21091255665460802223425137)
              ·
                refine ⟨15818441749095601667568853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21091255665460802223425137 15818441749095601667568853)
                ·
                  refine ⟨370744728494428164083645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15818441749095601667568853 370744728494428164083645)
                  ·
                    rfl

theorem cell23_6498205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 2, 7].length) (baseStart_6498205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6498205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6498205 prefixEnd_6498205 := by exact prefixLift 6498205
  have htrace : WordTrace (prefixWord ++ tailWord_6498205) baseStart_6498205 baseEnd_6498205 := by
    simpa [prefixWord, tailWord_6498205, baseEnd_6498205] using wordTrace_append hprefix tailTrace_6498205
  have hstable : (prefixWord ++ tailWord_6498205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6498205).length < 2 ^ (prefixWord ++ tailWord_6498205).sum := by decide
  have hdescent : baseEnd_6498205 < baseStart_6498205 := by decide
  rcases family_descends (prefixWord ++ tailWord_6498205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6498255 : List Nat := [1, 1, 2, 1, 1, 5, 1, 2, 4, 1, 4]
def baseStart_6498255 : Nat := 118140960795 + 6498255 * 2 ^ 59
def prefixEnd_6498255 : Nat := 4983230072969 + 3 ^ 40 * 6498255 * 2
def baseEnd_6498255 : Nat := 3336728230482578281127575

theorem tailTrace_6498255 : CollatzResearch.WordTrace tailWord_6498255 prefixEnd_6498255 3336728230482578281127575 := by
  unfold tailWord_6498255
  simp only [CollatzResearch.WordTrace]
  refine ⟨237010831072939423442336219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158007220715292948961557479 237010831072939423442336219)
  ·
    refine ⟨355516246609409135163504329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237010831072939423442336219 355516246609409135163504329)
    ·
      refine ⟨266637184957056851372628247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 355516246609409135163504329 266637184957056851372628247)
      ·
        refine ⟨399955777435585277058942371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266637184957056851372628247 399955777435585277058942371)
        ·
          refine ⟨599933666153377915588413557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 399955777435585277058942371 599933666153377915588413557)
          ·
            refine ⟨56243781201879179586413771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 599933666153377915588413557 56243781201879179586413771)
            ·
              refine ⟨84365671802818769379620657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56243781201879179586413771 84365671802818769379620657)
              ·
                refine ⟨63274253852114077034715493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84365671802818769379620657 63274253852114077034715493)
                ·
                  refine ⟨11863922597271389444009155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63274253852114077034715493 11863922597271389444009155)
                  ·
                    refine ⟨17795883895907084166013733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11863922597271389444009155 17795883895907084166013733)
                    ·
                      refine ⟨3336728230482578281127575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17795883895907084166013733 3336728230482578281127575)
                      ·
                        rfl

theorem cell23_6498255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 2, 4, 1, 4].length) (baseStart_6498255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6498255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6498255 prefixEnd_6498255 := by exact prefixLift 6498255
  have htrace : WordTrace (prefixWord ++ tailWord_6498255) baseStart_6498255 baseEnd_6498255 := by
    simpa [prefixWord, tailWord_6498255, baseEnd_6498255] using wordTrace_append hprefix tailTrace_6498255
  have hstable : (prefixWord ++ tailWord_6498255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6498255).length < 2 ^ (prefixWord ++ tailWord_6498255).sum := by decide
  have hdescent : baseEnd_6498255 < baseStart_6498255 := by decide
  rcases family_descends (prefixWord ++ tailWord_6498255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6498269 : List Nat := [1, 4, 3, 1, 3, 1, 2, 1, 2, 5]
def baseStart_6498269 : Nat := 118140960795 + 6498269 * 2 ^ 59
def prefixEnd_6498269 : Nat := 4983230072969 + 3 ^ 40 * 6498269 * 2
def baseEnd_6498269 : Nat := 1112245139737247075450837

theorem tailTrace_6498269 : CollatzResearch.WordTrace tailWord_6498269 prefixEnd_6498269 1112245139737247075450837 := by
  unfold tailWord_6498269
  simp only [CollatzResearch.WordTrace]
  refine ⟨237011341694888703833345861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158007561129925802555563907 237011341694888703833345861)
  ·
    refine ⟨44439626567791631968752349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 237011341694888703833345861 44439626567791631968752349)
    ·
      refine ⟨16664859962921861988282131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44439626567791631968752349 16664859962921861988282131)
      ·
        refine ⟨24997289944382792982423197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16664859962921861988282131 24997289944382792982423197)
        ·
          refine ⟨9373983729143547368408699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24997289944382792982423197 9373983729143547368408699)
          ·
            refine ⟨14060975593715321052613049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9373983729143547368408699 14060975593715321052613049)
            ·
              refine ⟨10545731695286490789459787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14060975593715321052613049 10545731695286490789459787)
              ·
                refine ⟨15818597542929736184189681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10545731695286490789459787 15818597542929736184189681)
                ·
                  refine ⟨11863948157197302138142261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15818597542929736184189681 11863948157197302138142261)
                  ·
                    refine ⟨1112245139737247075450837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11863948157197302138142261 1112245139737247075450837)
                    ·
                      rfl

theorem cell23_6498269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 2, 1, 2, 5].length) (baseStart_6498269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6498269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6498269 prefixEnd_6498269 := by exact prefixLift 6498269
  have htrace : WordTrace (prefixWord ++ tailWord_6498269) baseStart_6498269 baseEnd_6498269 := by
    simpa [prefixWord, tailWord_6498269, baseEnd_6498269] using wordTrace_append hprefix tailTrace_6498269
  have hstable : (prefixWord ++ tailWord_6498269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6498269).length < 2 ^ (prefixWord ++ tailWord_6498269).sum := by decide
  have hdescent : baseEnd_6498269 < baseStart_6498269 := by decide
  rcases family_descends (prefixWord ++ tailWord_6498269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6498355 : List Nat := [1, 1, 1, 2, 4, 1, 2, 2, 3, 6]
def baseStart_6498355 : Nat := 118140960795 + 6498355 * 2 ^ 59
def prefixEnd_6498355 : Nat := 4983230072969 + 3 ^ 40 * 6498355 * 2
def baseEnd_6498355 : Nat := 1112259859516009296625705

theorem tailTrace_6498355 : CollatzResearch.WordTrace tailWord_6498355 prefixEnd_6498355 1112259859516009296625705 := by
  unfold tailWord_6498355
  simp only [CollatzResearch.WordTrace]
  refine ⟨237014478372577140520976519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158009652248384760347317679 237014478372577140520976519)
  ·
    refine ⟨355521717558865710781464779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237014478372577140520976519 355521717558865710781464779)
    ·
      refine ⟨533282576338298566172197169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 355521717558865710781464779 533282576338298566172197169)
      ·
        refine ⟨399961932253723924629147877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 533282576338298566172197169 399961932253723924629147877)
        ·
          refine ⟨74992862297573235867965227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 399961932253723924629147877 74992862297573235867965227)
          ·
            refine ⟨112489293446359853801947841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74992862297573235867965227 112489293446359853801947841)
            ·
              refine ⟨84366970084769890351460881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112489293446359853801947841 84366970084769890351460881)
              ·
                refine ⟨63275227563577417763595661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84366970084769890351460881 63275227563577417763595661)
                ·
                  refine ⟨23728210336341531661348373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63275227563577417763595661 23728210336341531661348373)
                  ·
                    refine ⟨1112259859516009296625705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23728210336341531661348373 1112259859516009296625705)
                    ·
                      rfl

theorem cell23_6498355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 2, 3, 6].length) (baseStart_6498355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6498355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6498355 prefixEnd_6498355 := by exact prefixLift 6498355
  have htrace : WordTrace (prefixWord ++ tailWord_6498355) baseStart_6498355 baseEnd_6498355 := by
    simpa [prefixWord, tailWord_6498355, baseEnd_6498355] using wordTrace_append hprefix tailTrace_6498355
  have hstable : (prefixWord ++ tailWord_6498355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6498355).length < 2 ^ (prefixWord ++ tailWord_6498355).sum := by decide
  have hdescent : baseEnd_6498355 < baseStart_6498355 := by decide
  rcases family_descends (prefixWord ++ tailWord_6498355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6498433 : List Nat := [1, 2, 4, 2, 3, 2, 1, 2, 1, 2, 3]
def baseStart_6498433 : Nat := 118140960795 + 6498433 * 2 ^ 59
def prefixEnd_6498433 : Nat := 4983230072969 + 3 ^ 40 * 6498433 * 2
def baseEnd_6498433 : Nat := 3336819630039078584701757

theorem tailTrace_6498433 : CollatzResearch.WordTrace tailWord_6498433 prefixEnd_6498433 3336819630039078584701757 := by
  unfold tailWord_6498433
  simp only [CollatzResearch.WordTrace]
  refine ⟨237017323266294559842315953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158011548844196373228210635 237017323266294559842315953)
  ·
    refine ⟨177762992449720919881736965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237017323266294559842315953 177762992449720919881736965)
    ·
      refine ⟨33330561084322672477825681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 177762992449720919881736965 33330561084322672477825681)
      ·
        refine ⟨24997920813242004358369261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33330561084322672477825681 24997920813242004358369261)
        ·
          refine ⟨9374220304965751634388473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24997920813242004358369261 9374220304965751634388473)
          ·
            refine ⟨7030665228724313725791355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9374220304965751634388473 7030665228724313725791355)
            ·
              refine ⟨10545997843086470588687033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7030665228724313725791355 10545997843086470588687033)
              ·
                refine ⟨7909498382314852941515275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10545997843086470588687033 7909498382314852941515275)
                ·
                  refine ⟨11864247573472279412272913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7909498382314852941515275 11864247573472279412272913)
                  ·
                    refine ⟨8898185680104209559204685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11864247573472279412272913 8898185680104209559204685)
                    ·
                      refine ⟨3336819630039078584701757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8898185680104209559204685 3336819630039078584701757)
                      ·
                        rfl

theorem cell23_6498433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 1, 2, 1, 2, 3].length) (baseStart_6498433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6498433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6498433 prefixEnd_6498433 := by exact prefixLift 6498433
  have htrace : WordTrace (prefixWord ++ tailWord_6498433) baseStart_6498433 baseEnd_6498433 := by
    simpa [prefixWord, tailWord_6498433, baseEnd_6498433] using wordTrace_append hprefix tailTrace_6498433
  have hstable : (prefixWord ++ tailWord_6498433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6498433).length < 2 ^ (prefixWord ++ tailWord_6498433).sum := by decide
  have hdescent : baseEnd_6498433 < baseStart_6498433 := by decide
  rcases family_descends (prefixWord ++ tailWord_6498433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6498446 : List Nat := [4, 1, 1, 3, 3, 1, 1, 2, 1, 3, 3]
def baseStart_6498446 : Nat := 118140960795 + 6498446 * 2 ^ 59
def prefixEnd_6498446 : Nat := 4983230072969 + 3 ^ 40 * 6498446 * 2
def baseEnd_6498446 : Nat := 3336826305287587033839197

theorem tailTrace_6498446 : CollatzResearch.WordTrace tailWord_6498446 prefixEnd_6498446 3336826305287587033839197 := by
  unfold tailWord_6498446
  simp only [CollatzResearch.WordTrace]
  refine ⟨29627224676905932882817399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 158011864943498308708359461 29627224676905932882817399)
  ·
    refine ⟨44440837015358899324226099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29627224676905932882817399 44440837015358899324226099)
    ·
      refine ⟨66661255523038348986339149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44440837015358899324226099 66661255523038348986339149)
      ·
        refine ⟨24997970821139380869877181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66661255523038348986339149 24997970821139380869877181)
        ·
          refine ⟨9374239057927267826203943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24997970821139380869877181 9374239057927267826203943)
          ·
            refine ⟨14061358586890901739305915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9374239057927267826203943 14061358586890901739305915)
            ·
              refine ⟨21092037880336352608958873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14061358586890901739305915 21092037880336352608958873)
              ·
                refine ⟨15819028410252264456719155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21092037880336352608958873 15819028410252264456719155)
                ·
                  refine ⟨23728542615378396685078733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15819028410252264456719155 23728542615378396685078733)
                  ·
                    refine ⟨8898203480766898756904525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23728542615378396685078733 8898203480766898756904525)
                    ·
                      refine ⟨3336826305287587033839197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8898203480766898756904525 3336826305287587033839197)
                      ·
                        rfl

theorem cell23_6498446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 2, 1, 3, 3].length) (baseStart_6498446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6498446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6498446 prefixEnd_6498446 := by exact prefixLift 6498446
  have htrace : WordTrace (prefixWord ++ tailWord_6498446) baseStart_6498446 baseEnd_6498446 := by
    simpa [prefixWord, tailWord_6498446, baseEnd_6498446] using wordTrace_append hprefix tailTrace_6498446
  have hstable : (prefixWord ++ tailWord_6498446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6498446).length < 2 ^ (prefixWord ++ tailWord_6498446).sum := by decide
  have hdescent : baseEnd_6498446 < baseStart_6498446 := by decide
  rcases family_descends (prefixWord ++ tailWord_6498446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6498463 : List Nat := [1, 1, 2, 6, 1, 2, 2, 2, 2, 1, 3]
def baseStart_6498463 : Nat := 118140960795 + 6498463 * 2 ^ 59
def prefixEnd_6498463 : Nat := 4983230072969 + 3 ^ 40 * 6498463 * 2
def baseEnd_6498463 : Nat := 3336835034458713467326619

theorem tailTrace_6498463 : CollatzResearch.WordTrace tailWord_6498463 prefixEnd_6498463 3336835034458713467326619 := by
  unfold tailWord_6498463
  simp only [CollatzResearch.WordTrace]
  refine ⟨237018417456185874965908043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158012278304123916643938695 237018417456185874965908043)
  ·
    refine ⟨355527626184278812448862065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237018417456185874965908043 355527626184278812448862065)
    ·
      refine ⟨266645719638209109336646549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 355527626184278812448862065 266645719638209109336646549)
      ·
        refine ⟨12499018108041052000155307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 266645719638209109336646549 12499018108041052000155307)
        ·
          refine ⟨18748527162061578000232961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12499018108041052000155307 18748527162061578000232961)
          ·
            refine ⟨14061395371546183500174721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18748527162061578000232961 14061395371546183500174721)
            ·
              refine ⟨10546046528659637625131041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14061395371546183500174721 10546046528659637625131041)
              ·
                refine ⟨7909534896494728218848281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10546046528659637625131041 7909534896494728218848281)
                ·
                  refine ⟨5932151172371046164136211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7909534896494728218848281 5932151172371046164136211)
                  ·
                    refine ⟨8898226758556569246204317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5932151172371046164136211 8898226758556569246204317)
                    ·
                      refine ⟨3336835034458713467326619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8898226758556569246204317 3336835034458713467326619)
                      ·
                        rfl

theorem cell23_6498463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_6498463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6498463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6498463 prefixEnd_6498463 := by exact prefixLift 6498463
  have htrace : WordTrace (prefixWord ++ tailWord_6498463) baseStart_6498463 baseEnd_6498463 := by
    simpa [prefixWord, tailWord_6498463, baseEnd_6498463] using wordTrace_append hprefix tailTrace_6498463
  have hstable : (prefixWord ++ tailWord_6498463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6498463).length < 2 ^ (prefixWord ++ tailWord_6498463).sum := by decide
  have hdescent : baseEnd_6498463 < baseStart_6498463 := by decide
  rcases family_descends (prefixWord ++ tailWord_6498463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6498469 : List Nat := [1, 3, 1, 2, 1, 3, 1, 2, 3, 4, 2]
def baseStart_6498469 : Nat := 118140960795 + 6498469 * 2 ^ 59
def prefixEnd_6498469 : Nat := 4983230072969 + 3 ^ 40 * 6498469 * 2
def baseEnd_6498469 : Nat := 3336838115342640443851591

theorem tailTrace_6498469 : CollatzResearch.WordTrace tailWord_6498469 prefixEnd_6498469 3336838115342640443851591 := by
  unfold tailWord_6498469
  simp only [CollatzResearch.WordTrace]
  refine ⟨237018636294164137990626461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158012424196109425327084307 237018636294164137990626461)
  ·
    refine ⟨88881988610311551746484923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 237018636294164137990626461 88881988610311551746484923)
    ·
      refine ⟨133322982915467327619727385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88881988610311551746484923 133322982915467327619727385)
      ·
        refine ⟨99992237186600495714795539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133322982915467327619727385 99992237186600495714795539)
        ·
          refine ⟨149988355779900743572193309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99992237186600495714795539 149988355779900743572193309)
          ·
            refine ⟨56245633417462778839572491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 149988355779900743572193309 56245633417462778839572491)
            ·
              refine ⟨84368450126194168259358737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56245633417462778839572491 84368450126194168259358737)
              ·
                refine ⟨63276337594645626194519053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84368450126194168259358737 63276337594645626194519053)
                ·
                  refine ⟨23728626597992109822944645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63276337594645626194519053 23728626597992109822944645)
                  ·
                    refine ⟨4449117487123520591802121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23728626597992109822944645 4449117487123520591802121)
                    ·
                      refine ⟨3336838115342640443851591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4449117487123520591802121 3336838115342640443851591)
                      ·
                        rfl

theorem cell23_6498469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 2, 3, 4, 2].length) (baseStart_6498469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6498469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6498469 prefixEnd_6498469 := by exact prefixLift 6498469
  have htrace : WordTrace (prefixWord ++ tailWord_6498469) baseStart_6498469 baseEnd_6498469 := by
    simpa [prefixWord, tailWord_6498469, baseEnd_6498469] using wordTrace_append hprefix tailTrace_6498469
  have hstable : (prefixWord ++ tailWord_6498469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6498469).length < 2 ^ (prefixWord ++ tailWord_6498469).sum := by decide
  have hdescent : baseEnd_6498469 < baseStart_6498469 := by decide
  rcases family_descends (prefixWord ++ tailWord_6498469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6498520 : List Nat := [2, 1, 2, 2, 4, 3, 1, 2, 2, 2, 2]
def baseStart_6498520 : Nat := 118140960795 + 6498520 * 2 ^ 59
def prefixEnd_6498520 : Nat := 4983230072969 + 3 ^ 40 * 6498520 * 2
def baseEnd_6498520 : Nat := 3336864302856019744313857

theorem tailTrace_6498520 : CollatzResearch.WordTrace tailWord_6498520 prefixEnd_6498520 3336864302856019744313857 := by
  unfold tailWord_6498520
  simp only [CollatzResearch.WordTrace]
  refine ⟨118510248208489686850366507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158013664277986249133822009 118510248208489686850366507)
  ·
    refine ⟨177765372312734530275549761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118510248208489686850366507 177765372312734530275549761)
    ·
      refine ⟨133324029234550897706662321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177765372312734530275549761 133324029234550897706662321)
      ·
        refine ⟨99993021925913173279996741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133324029234550897706662321 99993021925913173279996741)
        ·
          refine ⟨18748691611108719989999389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 99993021925913173279996741 18748691611108719989999389)
          ·
            refine ⟨7030759354165769996249771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18748691611108719989999389 7030759354165769996249771)
            ·
              refine ⟨10546139031248654994374657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7030759354165769996249771 10546139031248654994374657)
              ·
                refine ⟨7909604273436491245780993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10546139031248654994374657 7909604273436491245780993)
                ·
                  refine ⟨5932203205077368434335745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7909604273436491245780993 5932203205077368434335745)
                  ·
                    refine ⟨4449152403808026325751809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5932203205077368434335745 4449152403808026325751809)
                    ·
                      refine ⟨3336864302856019744313857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4449152403808026325751809 3336864302856019744313857)
                      ·
                        rfl

theorem cell23_6498520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 1, 2, 2, 2, 2].length) (baseStart_6498520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6498520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6498520 prefixEnd_6498520 := by exact prefixLift 6498520
  have htrace : WordTrace (prefixWord ++ tailWord_6498520) baseStart_6498520 baseEnd_6498520 := by
    simpa [prefixWord, tailWord_6498520, baseEnd_6498520] using wordTrace_append hprefix tailTrace_6498520
  have hstable : (prefixWord ++ tailWord_6498520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6498520).length < 2 ^ (prefixWord ++ tailWord_6498520).sum := by decide
  have hdescent : baseEnd_6498520 < baseStart_6498520 := by decide
  rcases family_descends (prefixWord ++ tailWord_6498520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6498532 : List Nat := [2, 3, 1, 1, 1, 2, 1, 3, 1, 1, 7]
def baseStart_6498532 : Nat := 118140960795 + 6498532 * 2 ^ 59
def prefixEnd_6498532 : Nat := 4983230072969 + 3 ^ 40 * 6498532 * 2
def baseEnd_6498532 : Nat := 3336870464623873697363801

theorem tailTrace_6498532 : CollatzResearch.WordTrace tailWord_6498532 prefixEnd_6498532 3336870464623873697363801 := by
  unfold tailWord_6498532
  simp only [CollatzResearch.WordTrace]
  refine ⟨118510467046467949875084925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158013956061957266500113233 118510467046467949875084925)
  ·
    refine ⟨44441425142425481203156847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118510467046467949875084925 44441425142425481203156847)
    ·
      refine ⟨66662137713638221804735271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44441425142425481203156847 66662137713638221804735271)
      ·
        refine ⟨99993206570457332707102907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66662137713638221804735271 99993206570457332707102907)
        ·
          refine ⟨149989809855685999060654361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99993206570457332707102907 149989809855685999060654361)
          ·
            refine ⟨112492357391764499295490771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149989809855685999060654361 112492357391764499295490771)
            ·
              refine ⟨168738536087646748943236157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112492357391764499295490771 168738536087646748943236157)
              ·
                refine ⟨63276951032867530853713559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 168738536087646748943236157 63276951032867530853713559)
                ·
                  refine ⟨94915426549301296280570339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63276951032867530853713559 94915426549301296280570339)
                  ·
                    refine ⟨142373139823951944420855509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 94915426549301296280570339 142373139823951944420855509)
                    ·
                      refine ⟨3336870464623873697363801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 142373139823951944420855509 3336870464623873697363801)
                      ·
                        rfl

theorem cell23_6498532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 3, 1, 1, 7].length) (baseStart_6498532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6498532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6498532 prefixEnd_6498532 := by exact prefixLift 6498532
  have htrace : WordTrace (prefixWord ++ tailWord_6498532) baseStart_6498532 baseEnd_6498532 := by
    simpa [prefixWord, tailWord_6498532, baseEnd_6498532] using wordTrace_append hprefix tailTrace_6498532
  have hstable : (prefixWord ++ tailWord_6498532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6498532).length < 2 ^ (prefixWord ++ tailWord_6498532).sum := by decide
  have hdescent : baseEnd_6498532 < baseStart_6498532 := by decide
  rcases family_descends (prefixWord ++ tailWord_6498532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6498559 : List Nat := [1, 1, 2, 2, 1, 4, 2, 3, 2, 1, 4]
def baseStart_6498559 : Nat := 118140960795 + 6498559 * 2 ^ 59
def prefixEnd_6498559 : Nat := 4983230072969 + 3 ^ 40 * 6498559 * 2
def baseEnd_6498559 : Nat := 3336884328601545091726177

theorem tailTrace_6498559 : CollatzResearch.WordTrace tailWord_6498559 prefixEnd_6498559 3336884328601545091726177 := by
  unfold tailWord_6498559
  simp only [CollatzResearch.WordTrace]
  refine ⟨237021918863838083361402731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158014612575892055574268487 237021918863838083361402731)
  ·
    refine ⟨355532878295757125042104097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237021918863838083361402731 355532878295757125042104097)
    ·
      refine ⟨266649658721817843781578073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 355532878295757125042104097 266649658721817843781578073)
      ·
        refine ⟨199987244041363382836183555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 266649658721817843781578073 199987244041363382836183555)
        ·
          refine ⟨299980866062045074254275333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199987244041363382836183555 299980866062045074254275333)
          ·
            refine ⟨56246412386633451422676625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 299980866062045074254275333 56246412386633451422676625)
            ·
              refine ⟨42184809289975088567007469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56246412386633451422676625 42184809289975088567007469)
              ·
                refine ⟨15819303483740658212627801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42184809289975088567007469 15819303483740658212627801)
                ·
                  refine ⟨11864477612805493659470851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15819303483740658212627801 11864477612805493659470851)
                  ·
                    refine ⟨17796716419208240489206277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11864477612805493659470851 17796716419208240489206277)
                    ·
                      refine ⟨3336884328601545091726177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17796716419208240489206277 3336884328601545091726177)
                      ·
                        rfl

theorem cell23_6498559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 3, 2, 1, 4].length) (baseStart_6498559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6498559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6498559 prefixEnd_6498559 := by exact prefixLift 6498559
  have htrace : WordTrace (prefixWord ++ tailWord_6498559) baseStart_6498559 baseEnd_6498559 := by
    simpa [prefixWord, tailWord_6498559, baseEnd_6498559] using wordTrace_append hprefix tailTrace_6498559
  have hstable : (prefixWord ++ tailWord_6498559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6498559).length < 2 ^ (prefixWord ++ tailWord_6498559).sum := by decide
  have hdescent : baseEnd_6498559 < baseStart_6498559 := by decide
  rcases family_descends (prefixWord ++ tailWord_6498559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6498654 : List Nat := [4, 4, 2, 1, 1, 1, 1, 2, 3, 4]
def baseStart_6498654 : Nat := 118140960795 + 6498654 * 2 ^ 59
def prefixEnd_6498654 : Nat := 4983230072969 + 3 ^ 40 * 6498654 * 2
def baseEnd_6498654 : Nat := 1112311036421240740012747

theorem tailTrace_6498654 : CollatzResearch.WordTrace tailWord_6498654 prefixEnd_6498654 1112311036421240740012747 := by
  unfold tailWord_6498654
  simp only [CollatzResearch.WordTrace]
  refine ⟨29628172974811739323263877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 158016922532329276390740677 29628172974811739323263877)
  ·
    refine ⟨5555282432777201123111977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29628172974811739323263877 5555282432777201123111977)
    ·
      refine ⟨4166461824582900842333983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5555282432777201123111977 4166461824582900842333983)
      ·
        refine ⟨6249692736874351263500975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4166461824582900842333983 6249692736874351263500975)
        ·
          refine ⟨9374539105311526895251463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6249692736874351263500975 9374539105311526895251463)
          ·
            refine ⟨14061808657967290342877195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9374539105311526895251463 14061808657967290342877195)
            ·
              refine ⟨21092712986950935514315793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14061808657967290342877195 21092712986950935514315793)
              ·
                refine ⟨15819534740213201635736845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21092712986950935514315793 15819534740213201635736845)
                ·
                  refine ⟨5932325527579950613401317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15819534740213201635736845 5932325527579950613401317)
                  ·
                    refine ⟨1112311036421240740012747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5932325527579950613401317 1112311036421240740012747)
                    ·
                      rfl

theorem cell23_6498654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_6498654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6498654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6498654 prefixEnd_6498654 := by exact prefixLift 6498654
  have htrace : WordTrace (prefixWord ++ tailWord_6498654) baseStart_6498654 baseEnd_6498654 := by
    simpa [prefixWord, tailWord_6498654, baseEnd_6498654] using wordTrace_append hprefix tailTrace_6498654
  have hstable : (prefixWord ++ tailWord_6498654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6498654).length < 2 ^ (prefixWord ++ tailWord_6498654).sum := by decide
  have hdescent : baseEnd_6498654 < baseStart_6498654 := by decide
  rcases family_descends (prefixWord ++ tailWord_6498654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6498677 : List Nat := [1, 3, 4, 1, 2, 2, 2, 3, 1, 1, 3]
def baseStart_6498677 : Nat := 118140960795 + 6498677 * 2 ^ 59
def prefixEnd_6498677 : Nat := 4983230072969 + 3 ^ 40 * 6498677 * 2
def baseEnd_6498677 : Nat := 3336944919318775630050635

theorem tailTrace_6498677 : CollatzResearch.WordTrace tailWord_6498677 prefixEnd_6498677 3336944919318775630050635 := by
  unfold tailWord_6498677
  simp only [CollatzResearch.WordTrace]
  refine ⟨237026222677410589514198285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158017481784940393009465523 237026222677410589514198285)
  ·
    refine ⟨88884833504028971067824357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 237026222677410589514198285 88884833504028971067824357)
    ·
      refine ⟨16665906282005432075217067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88884833504028971067824357 16665906282005432075217067)
      ·
        refine ⟨24998859423008148112825601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16665906282005432075217067 24998859423008148112825601)
        ·
          refine ⟨18749144567256111084619201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24998859423008148112825601 18749144567256111084619201)
          ·
            refine ⟨14061858425442083313464401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18749144567256111084619201 14061858425442083313464401)
            ·
              refine ⟨10546393819081562485098301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14061858425442083313464401 10546393819081562485098301)
              ·
                refine ⟨3954897682155585931911863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10546393819081562485098301 3954897682155585931911863)
                ·
                  refine ⟨5932346523233378897867795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3954897682155585931911863 5932346523233378897867795)
                  ·
                    refine ⟨8898519784850068346801693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5932346523233378897867795 8898519784850068346801693)
                    ·
                      refine ⟨3336944919318775630050635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8898519784850068346801693 3336944919318775630050635)
                      ·
                        rfl

theorem cell23_6498677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 2, 3, 1, 1, 3].length) (baseStart_6498677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6498677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6498677 prefixEnd_6498677 := by exact prefixLift 6498677
  have htrace : WordTrace (prefixWord ++ tailWord_6498677) baseStart_6498677 baseEnd_6498677 := by
    simpa [prefixWord, tailWord_6498677, baseEnd_6498677] using wordTrace_append hprefix tailTrace_6498677
  have hstable : (prefixWord ++ tailWord_6498677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6498677).length < 2 ^ (prefixWord ++ tailWord_6498677).sum := by decide
  have hdescent : baseEnd_6498677 < baseStart_6498677 := by decide
  rcases family_descends (prefixWord ++ tailWord_6498677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6498679 : List Nat := [1, 1, 3, 1, 1, 2, 2, 3, 3, 2, 4]
def baseStart_6498679 : Nat := 118140960795 + 6498679 * 2 ^ 59
def prefixEnd_6498679 : Nat := 4983230072969 + 3 ^ 40 * 6498679 * 2
def baseEnd_6498679 : Nat := 3336945946280084622225625

theorem tailTrace_6498679 : CollatzResearch.WordTrace tailWord_6498679 prefixEnd_6498679 3336945946280084622225625 := by
  unfold tailWord_6498679
  simp only [CollatzResearch.WordTrace]
  refine ⟨237026295623403343855771091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158017530415602229237180727 237026295623403343855771091)
  ·
    refine ⟨355539443435105015783656637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237026295623403343855771091 355539443435105015783656637)
    ·
      refine ⟨133327291288164380918871239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 355539443435105015783656637 133327291288164380918871239)
      ·
        refine ⟨199990936932246571378306859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133327291288164380918871239 199990936932246571378306859)
        ·
          refine ⟨299986405398369857067460289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199990936932246571378306859 299986405398369857067460289)
          ·
            refine ⟨224989804048777392800595217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 299986405398369857067460289 224989804048777392800595217)
            ·
              refine ⟨168742353036583044600446413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 224989804048777392800595217 168742353036583044600446413)
              ·
                refine ⟨63278382388718641725167405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 168742353036583044600446413 63278382388718641725167405)
                ·
                  refine ⟨23729393395769490646937777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63278382388718641725167405 23729393395769490646937777)
                  ·
                    refine ⟨17797045046827117985203333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23729393395769490646937777 17797045046827117985203333)
                    ·
                      refine ⟨3336945946280084622225625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17797045046827117985203333 3336945946280084622225625)
                      ·
                        rfl

theorem cell23_6498679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 3, 3, 2, 4].length) (baseStart_6498679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6498679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6498679 prefixEnd_6498679 := by exact prefixLift 6498679
  have htrace : WordTrace (prefixWord ++ tailWord_6498679) baseStart_6498679 baseEnd_6498679 := by
    simpa [prefixWord, tailWord_6498679, baseEnd_6498679] using wordTrace_append hprefix tailTrace_6498679
  have hstable : (prefixWord ++ tailWord_6498679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6498679).length < 2 ^ (prefixWord ++ tailWord_6498679).sum := by decide
  have hdescent : baseEnd_6498679 < baseStart_6498679 := by decide
  rcases family_descends (prefixWord ++ tailWord_6498679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6498683 : List Nat := [1, 1, 1, 1, 1, 7, 4, 1, 1, 1, 4]
def baseStart_6498683 : Nat := 118140960795 + 6498683 * 2 ^ 59
def prefixEnd_6498683 : Nat := 4983230072969 + 3 ^ 40 * 6498683 * 2
def baseEnd_6498683 : Nat := 3336948000202702606575607

theorem tailTrace_6498683 : CollatzResearch.WordTrace tailWord_6498683 prefixEnd_6498683 3336948000202702606575607 := by
  unfold tailWord_6498683
  simp only [CollatzResearch.WordTrace]
  refine ⟨237026441515388852538916703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158017627676925901692611135 237026441515388852538916703)
  ·
    refine ⟨355539662273083278808375055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237026441515388852538916703 355539662273083278808375055)
    ·
      refine ⟨533309493409624918212562583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 355539662273083278808375055 533309493409624918212562583)
      ·
        refine ⟨799964240114437377318843875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 533309493409624918212562583 799964240114437377318843875)
        ·
          refine ⟨1199946360171656065978265813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 799964240114437377318843875 1199946360171656065978265813)
          ·
            refine ⟨28123742816523189046365605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 1199946360171656065978265813 28123742816523189046365605)
            ·
              refine ⟨5273201778098097946193551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28123742816523189046365605 5273201778098097946193551)
              ·
                refine ⟨7909802667147146919290327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5273201778098097946193551 7909802667147146919290327)
                ·
                  refine ⟨11864704000720720378935491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7909802667147146919290327 11864704000720720378935491)
                  ·
                    refine ⟨17797056001081080568403237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11864704000720720378935491 17797056001081080568403237)
                    ·
                      refine ⟨3336948000202702606575607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17797056001081080568403237 3336948000202702606575607)
                      ·
                        rfl

theorem cell23_6498683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 4, 1, 1, 1, 4].length) (baseStart_6498683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6498683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6498683 prefixEnd_6498683 := by exact prefixLift 6498683
  have htrace : WordTrace (prefixWord ++ tailWord_6498683) baseStart_6498683 baseEnd_6498683 := by
    simpa [prefixWord, tailWord_6498683, baseEnd_6498683] using wordTrace_append hprefix tailTrace_6498683
  have hstable : (prefixWord ++ tailWord_6498683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6498683).length < 2 ^ (prefixWord ++ tailWord_6498683).sum := by decide
  have hdescent : baseEnd_6498683 < baseStart_6498683 := by decide
  rcases family_descends (prefixWord ++ tailWord_6498683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6498700 : List Nat := [2, 2, 1, 2, 1, 5, 2, 1, 3, 2, 2]
def baseStart_6498700 : Nat := 118140960795 + 6498700 * 2 ^ 59
def prefixEnd_6498700 : Nat := 4983230072969 + 3 ^ 40 * 6498700 * 2
def baseEnd_6498700 : Nat := 3336956729373829040063029

theorem tailTrace_6498700 : CollatzResearch.WordTrace tailWord_6498700 prefixEnd_6498700 3336956729373829040063029 := by
  unfold tailWord_6498700
  simp only [CollatzResearch.WordTrace]
  refine ⟨118513530778163632221142777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158018041037551509628190369 118513530778163632221142777)
  ·
    refine ⟨88885148083622724165857083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118513530778163632221142777 88885148083622724165857083)
    ·
      refine ⟨133327722125434086248785625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88885148083622724165857083 133327722125434086248785625)
      ·
        refine ⟨99995791594075564686589219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133327722125434086248785625 99995791594075564686589219)
        ·
          refine ⟨149993687391113347029883829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99995791594075564686589219 149993687391113347029883829)
          ·
            refine ⟨14061908192916876284051609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 149993687391113347029883829 14061908192916876284051609)
            ·
              refine ⟨10546431144687657213038707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14061908192916876284051609 10546431144687657213038707)
              ·
                refine ⟨15819646717031485819558061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10546431144687657213038707 15819646717031485819558061)
                ·
                  refine ⟨5932367518886807182334273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15819646717031485819558061 5932367518886807182334273)
                  ·
                    refine ⟨4449275639165105386750705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5932367518886807182334273 4449275639165105386750705)
                    ·
                      refine ⟨3336956729373829040063029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4449275639165105386750705 3336956729373829040063029)
                      ·
                        rfl

theorem cell23_6498700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 2, 1, 3, 2, 2].length) (baseStart_6498700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6498700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6498700 prefixEnd_6498700 := by exact prefixLift 6498700
  have htrace : WordTrace (prefixWord ++ tailWord_6498700) baseStart_6498700 baseEnd_6498700 := by
    simpa [prefixWord, tailWord_6498700, baseEnd_6498700] using wordTrace_append hprefix tailTrace_6498700
  have hstable : (prefixWord ++ tailWord_6498700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6498700).length < 2 ^ (prefixWord ++ tailWord_6498700).sum := by decide
  have hdescent : baseEnd_6498700 < baseStart_6498700 := by decide
  rcases family_descends (prefixWord ++ tailWord_6498700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6498739 : List Nat := [1, 1, 1, 2, 3, 1, 1, 1, 3, 5, 4]
def baseStart_6498739 : Nat := 118140960795 + 6498739 * 2 ^ 59
def prefixEnd_6498739 : Nat := 4983230072969 + 3 ^ 40 * 6498739 * 2
def baseEnd_6498739 : Nat := 3336976755119354387475349

theorem tailTrace_6498739 : CollatzResearch.WordTrace tailWord_6498739 prefixEnd_6498739 3336976755119354387475349 := by
  unfold tailWord_6498739
  simp only [CollatzResearch.WordTrace]
  refine ⟨237028484003185974102955271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158018989335457316068636847 237028484003185974102955271)
  ·
    refine ⟨355542726004778961154432907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237028484003185974102955271 355542726004778961154432907)
    ·
      refine ⟨533314089007168441731649361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 355542726004778961154432907 533314089007168441731649361)
      ·
        refine ⟨399985566755376331298737021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 533314089007168441731649361 399985566755376331298737021)
        ·
          refine ⟨149994587533266124237026383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 399985566755376331298737021 149994587533266124237026383)
          ·
            refine ⟨224991881299899186355539575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149994587533266124237026383 224991881299899186355539575)
            ·
              refine ⟨337487821949848779533309363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 224991881299899186355539575 337487821949848779533309363)
              ·
                refine ⟨506231732924773169299964045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 337487821949848779533309363 506231732924773169299964045)
                ·
                  refine ⟨189836899846789938487486517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 506231732924773169299964045 189836899846789938487486517)
                  ·
                    refine ⟨17797209360636556733201861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 189836899846789938487486517 17797209360636556733201861)
                    ·
                      refine ⟨3336976755119354387475349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17797209360636556733201861 3336976755119354387475349)
                      ·
                        rfl

theorem cell23_6498739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 3, 5, 4].length) (baseStart_6498739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6498739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6498739 prefixEnd_6498739 := by exact prefixLift 6498739
  have htrace : WordTrace (prefixWord ++ tailWord_6498739) baseStart_6498739 baseEnd_6498739 := by
    simpa [prefixWord, tailWord_6498739, baseEnd_6498739] using wordTrace_append hprefix tailTrace_6498739
  have hstable : (prefixWord ++ tailWord_6498739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6498739).length < 2 ^ (prefixWord ++ tailWord_6498739).sum := by decide
  have hdescent : baseEnd_6498739 < baseStart_6498739 := by decide
  rcases family_descends (prefixWord ++ tailWord_6498739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6498740 : List Nat := [2, 5, 2, 2, 1, 2, 9]
def baseStart_6498740 : Nat := 118140960795 + 6498740 * 2 ^ 59
def prefixEnd_6498740 : Nat := 4983230072969 + 3 ^ 40 * 6498740 * 2
def baseEnd_6498740 : Nat := 41197250229629739303245

theorem tailTrace_6498740 : CollatzResearch.WordTrace tailWord_6498740 prefixEnd_6498740 41197250229629739303245 := by
  unfold tailWord_6498740
  simp only [CollatzResearch.WordTrace]
  refine ⟨118514260238091175636870837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158019013650788234182494449 118514260238091175636870837)
  ·
    refine ⟨11110711897321047715956641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 118514260238091175636870837 11110711897321047715956641)
    ·
      refine ⟨8333033922990785786967481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11110711897321047715956641 8333033922990785786967481)
      ·
        refine ⟨6249775442243089340225611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8333033922990785786967481 6249775442243089340225611)
        ·
          refine ⟨9374663163364634010338417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6249775442243089340225611 9374663163364634010338417)
          ·
            refine ⟨7030997372523475507753813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9374663163364634010338417 7030997372523475507753813)
            ·
              refine ⟨41197250229629739303245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7030997372523475507753813 41197250229629739303245)
              ·
                rfl

theorem cell23_6498740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 9].length) (baseStart_6498740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6498740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6498740 prefixEnd_6498740 := by exact prefixLift 6498740
  have htrace : WordTrace (prefixWord ++ tailWord_6498740) baseStart_6498740 baseEnd_6498740 := by
    simpa [prefixWord, tailWord_6498740, baseEnd_6498740] using wordTrace_append hprefix tailTrace_6498740
  have hstable : (prefixWord ++ tailWord_6498740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6498740).length < 2 ^ (prefixWord ++ tailWord_6498740).sum := by decide
  have hdescent : baseEnd_6498740 < baseStart_6498740 := by decide
  rcases family_descends (prefixWord ++ tailWord_6498740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6498769 : List Nat := [1, 2, 2, 1, 2, 1, 1, 2, 2, 3, 6]
def baseStart_6498769 : Nat := 118140960795 + 6498769 * 2 ^ 59
def prefixEnd_6498769 : Nat := 4983230072969 + 3 ^ 40 * 6498769 * 2
def baseEnd_6498769 : Nat := 3336992159538989270100211

theorem tailTrace_6498769 : CollatzResearch.WordTrace tailWord_6498769 prefixEnd_6498769 3336992159538989270100211 := by
  unfold tailWord_6498769
  simp only [CollatzResearch.WordTrace]
  refine ⟨237029578193077289226547361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158019718795384859484364907 237029578193077289226547361)
  ·
    refine ⟨177772183644807966919910521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237029578193077289226547361 177772183644807966919910521)
    ·
      refine ⟨133329137733605975189932891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177772183644807966919910521 133329137733605975189932891)
      ·
        refine ⟨199993706600408962784899337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133329137733605975189932891 199993706600408962784899337)
        ·
          refine ⟨149995279950306722088674503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 199993706600408962784899337 149995279950306722088674503)
          ·
            refine ⟨224992919925460083133011755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149995279950306722088674503 224992919925460083133011755)
            ·
              refine ⟨337489379888190124699517633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 224992919925460083133011755 337489379888190124699517633)
              ·
                refine ⟨253117034916142593524638225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 337489379888190124699517633 253117034916142593524638225)
                ·
                  refine ⟨189837776187106945143478669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 253117034916142593524638225 189837776187106945143478669)
                  ·
                    refine ⟨71189166070165104428804501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 189837776187106945143478669 71189166070165104428804501)
                    ·
                      refine ⟨3336992159538989270100211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71189166070165104428804501 3336992159538989270100211)
                      ·
                        rfl

theorem cell23_6498769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 3, 6].length) (baseStart_6498769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6498769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6498769 prefixEnd_6498769 := by exact prefixLift 6498769
  have htrace : WordTrace (prefixWord ++ tailWord_6498769) baseStart_6498769 baseEnd_6498769 := by
    simpa [prefixWord, tailWord_6498769, baseEnd_6498769] using wordTrace_append hprefix tailTrace_6498769
  have hstable : (prefixWord ++ tailWord_6498769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6498769).length < 2 ^ (prefixWord ++ tailWord_6498769).sum := by decide
  have hdescent : baseEnd_6498769 < baseStart_6498769 := by decide
  rcases family_descends (prefixWord ++ tailWord_6498769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6498813 : List Nat := [1, 4, 1, 1, 1, 3, 3, 4, 5]
def baseStart_6498813 : Nat := 118140960795 + 6498813 * 2 ^ 59
def prefixEnd_6498813 : Nat := 4983230072969 + 3 ^ 40 * 6498813 * 2
def baseEnd_6498813 : Nat := 370779416965309677550001

theorem tailTrace_6498813 : CollatzResearch.WordTrace tailWord_6498813 prefixEnd_6498813 370779416965309677550001 := by
  unfold tailWord_6498813
  simp only [CollatzResearch.WordTrace]
  refine ⟨237031183004917884741149093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158020788669945256494099395 237031183004917884741149093)
  ·
    refine ⟨44443346813422103388965455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 237031183004917884741149093 44443346813422103388965455)
    ·
      refine ⟨66665020220133155083448183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44443346813422103388965455 66665020220133155083448183)
      ·
        refine ⟨99997530330199732625172275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66665020220133155083448183 99997530330199732625172275)
        ·
          refine ⟨149996295495299598937758413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99997530330199732625172275 149996295495299598937758413)
          ·
            refine ⟨56248610810737349601659405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 149996295495299598937758413 56248610810737349601659405)
            ·
              refine ⟨21093229054026506100622277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56248610810737349601659405 21093229054026506100622277)
              ·
                refine ⟨3954980447629969893866677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21093229054026506100622277 3954980447629969893866677)
                ·
                  refine ⟨370779416965309677550001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3954980447629969893866677 370779416965309677550001)
                  ·
                    rfl

theorem cell23_6498813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 4, 5].length) (baseStart_6498813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6498813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6498813 prefixEnd_6498813 := by exact prefixLift 6498813
  have htrace : WordTrace (prefixWord ++ tailWord_6498813) baseStart_6498813 baseEnd_6498813 := by
    simpa [prefixWord, tailWord_6498813, baseEnd_6498813] using wordTrace_append hprefix tailTrace_6498813
  have hstable : (prefixWord ++ tailWord_6498813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6498813).length < 2 ^ (prefixWord ++ tailWord_6498813).sum := by decide
  have hdescent : baseEnd_6498813 < baseStart_6498813 := by decide
  rcases family_descends (prefixWord ++ tailWord_6498813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6498826 : List Nat := [3, 1, 2, 2, 2, 1, 2, 2, 1, 7]
def baseStart_6498826 : Nat := 118140960795 + 6498826 * 2 ^ 59
def prefixEnd_6498826 : Nat := 4983230072969 + 3 ^ 40 * 6498826 * 2
def baseEnd_6498826 : Nat := 1112340475978765182362483

theorem tailTrace_6498826 : CollatzResearch.WordTrace tailWord_6498826 prefixEnd_6498826 1112340475978765182362483 := by
  unfold tailWord_6498826
  simp only [CollatzResearch.WordTrace]
  refine ⟨59257914288467696990343083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158021104769247191974248221 59257914288467696990343083)
  ·
    refine ⟨88886871432701545485514625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59257914288467696990343083 88886871432701545485514625)
    ·
      refine ⟨66665153574526159114135969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88886871432701545485514625 66665153574526159114135969)
      ·
        refine ⟨49998865180894619335601977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66665153574526159114135969 49998865180894619335601977)
        ·
          refine ⟨37499148885670964501701483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49998865180894619335601977 37499148885670964501701483)
          ·
            refine ⟨56248723328506446752552225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37499148885670964501701483 56248723328506446752552225)
            ·
              refine ⟨42186542496379835064414169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56248723328506446752552225 42186542496379835064414169)
              ·
                refine ⟨31639906872284876298310627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42186542496379835064414169 31639906872284876298310627)
                ·
                  refine ⟨47459860308427314447465941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31639906872284876298310627 47459860308427314447465941)
                  ·
                    refine ⟨1112340475978765182362483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47459860308427314447465941 1112340475978765182362483)
                    ·
                      rfl

theorem cell23_6498826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 2, 1, 7].length) (baseStart_6498826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6498826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6498826 prefixEnd_6498826 := by exact prefixLift 6498826
  have htrace : WordTrace (prefixWord ++ tailWord_6498826) baseStart_6498826 baseEnd_6498826 := by
    simpa [prefixWord, tailWord_6498826, baseEnd_6498826] using wordTrace_append hprefix tailTrace_6498826
  have hstable : (prefixWord ++ tailWord_6498826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6498826).length < 2 ^ (prefixWord ++ tailWord_6498826).sum := by decide
  have hdescent : baseEnd_6498826 < baseStart_6498826 := by decide
  rcases family_descends (prefixWord ++ tailWord_6498826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6498866 : List Nat := [3, 2, 1, 1, 2, 1, 2, 1, 2, 3, 5]
def baseStart_6498866 : Nat := 118140960795 + 6498866 * 2 ^ 59
def prefixEnd_6498866 : Nat := 4983230072969 + 3 ^ 40 * 6498866 * 2
def baseEnd_6498866 : Nat := 3337041967162475390587265

theorem tailTrace_6498866 : CollatzResearch.WordTrace tailWord_6498866 prefixEnd_6498866 3337041967162475390587265 := by
  unfold tailWord_6498866
  simp only [CollatzResearch.WordTrace]
  refine ⟨59258279018431468698207113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158022077382483916528552301 59258279018431468698207113)
  ·
    refine ⟨44443709263823601523655335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59258279018431468698207113 44443709263823601523655335)
    ·
      refine ⟨66665563895735402285483003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44443709263823601523655335 66665563895735402285483003)
      ·
        refine ⟨99998345843603103428224505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66665563895735402285483003 99998345843603103428224505)
        ·
          refine ⟨74998759382702327571168379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99998345843603103428224505 74998759382702327571168379)
          ·
            refine ⟨112498139074053491356752569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74998759382702327571168379 112498139074053491356752569)
            ·
              refine ⟨84373604305540118517564427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112498139074053491356752569 84373604305540118517564427)
              ·
                refine ⟨126560406458310177776346641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84373604305540118517564427 126560406458310177776346641)
                ·
                  refine ⟨94920304843732633332259981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 126560406458310177776346641 94920304843732633332259981)
                  ·
                    refine ⟨35595114316399737499597493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 94920304843732633332259981 35595114316399737499597493)
                    ·
                      refine ⟨3337041967162475390587265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35595114316399737499597493 3337041967162475390587265)
                      ·
                        rfl

theorem cell23_6498866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 1, 2, 3, 5].length) (baseStart_6498866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6498866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6498866 prefixEnd_6498866 := by exact prefixLift 6498866
  have htrace : WordTrace (prefixWord ++ tailWord_6498866) baseStart_6498866 baseEnd_6498866 := by
    simpa [prefixWord, tailWord_6498866, baseEnd_6498866] using wordTrace_append hprefix tailTrace_6498866
  have hstable : (prefixWord ++ tailWord_6498866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6498866).length < 2 ^ (prefixWord ++ tailWord_6498866).sum := by decide
  have hdescent : baseEnd_6498866 < baseStart_6498866 := by decide
  rcases family_descends (prefixWord ++ tailWord_6498866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6498923 : List Nat := [1, 1, 1, 1, 2, 2, 1, 4, 3, 5, 2]
def baseStart_6498923 : Nat := 118140960795 + 6498923 * 2 ^ 59
def prefixEnd_6498923 : Nat := 4983230072969 + 3 ^ 40 * 6498923 * 2
def baseEnd_6498923 : Nat := 3337071235559781667574503

theorem tailTrace_6498923 : CollatzResearch.WordTrace tailWord_6498923 prefixEnd_6498923 3337071235559781667574503 := by
  unfold tailWord_6498923
  simp only [CollatzResearch.WordTrace]
  refine ⟨237035195034519373527653423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158023463356346249018435615 237035195034519373527653423)
  ·
    refine ⟨355552792551779060291480135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237035195034519373527653423 355552792551779060291480135)
    ·
      refine ⟨533329188827668590437220203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 355552792551779060291480135 533329188827668590437220203)
      ·
        refine ⟨799993783241502885655830305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 533329188827668590437220203 799993783241502885655830305)
        ·
          refine ⟨599995337431127164241872729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 799993783241502885655830305 599995337431127164241872729)
          ·
            refine ⟨449996503073345373181404547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 599995337431127164241872729 449996503073345373181404547)
            ·
              refine ⟨674994754610018059772106821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 449996503073345373181404547 674994754610018059772106821)
              ·
                refine ⟨126561516489378386207270029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 674994754610018059772106821 126561516489378386207270029)
                ·
                  refine ⟨47460568683516894827726261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 126561516489378386207270029 47460568683516894827726261)
                  ·
                    refine ⟨4449428314079708890099337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47460568683516894827726261 4449428314079708890099337)
                    ·
                      refine ⟨3337071235559781667574503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4449428314079708890099337 3337071235559781667574503)
                      ·
                        rfl

theorem cell23_6498923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 4, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 4, 3, 5, 2].length) (baseStart_6498923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6498923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6498923 prefixEnd_6498923 := by exact prefixLift 6498923
  have htrace : WordTrace (prefixWord ++ tailWord_6498923) baseStart_6498923 baseEnd_6498923 := by
    simpa [prefixWord, tailWord_6498923, baseEnd_6498923] using wordTrace_append hprefix tailTrace_6498923
  have hstable : (prefixWord ++ tailWord_6498923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6498923).length < 2 ^ (prefixWord ++ tailWord_6498923).sum := by decide
  have hdescent : baseEnd_6498923 < baseStart_6498923 := by decide
  rcases family_descends (prefixWord ++ tailWord_6498923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6498976 : List Nat := [2, 1, 1, 4, 15]
def baseStart_6498976 : Nat := 118140960795 + 6498976 * 2 ^ 59
def prefixEnd_6498976 : Nat := 4983230072969 + 3 ^ 40 * 6498976 * 2
def baseEnd_6498976 : Nat := 4577638477413539040071

theorem tailTrace_6498976 : CollatzResearch.WordTrace tailWord_6498976 prefixEnd_6498976 4577638477413539040071 := by
  unfold tailWord_6498976
  simp only [CollatzResearch.WordTrace]
  refine ⟨118518564051663681789666391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158024752068884909052888521 118518564051663681789666391)
  ·
    refine ⟨177777846077495522684499587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118518564051663681789666391 177777846077495522684499587)
    ·
      refine ⟨266666769116243284026749381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177777846077495522684499587 266666769116243284026749381)
      ·
        refine ⟨50000019209295615755015509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 266666769116243284026749381 50000019209295615755015509)
        ·
          refine ⟨4577638477413539040071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 15 50000019209295615755015509 4577638477413539040071)
          ·
            rfl

theorem cell23_6498976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 15].length) (baseStart_6498976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6498976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6498976 prefixEnd_6498976 := by exact prefixLift 6498976
  have htrace : WordTrace (prefixWord ++ tailWord_6498976) baseStart_6498976 baseEnd_6498976 := by
    simpa [prefixWord, tailWord_6498976, baseEnd_6498976] using wordTrace_append hprefix tailTrace_6498976
  have hstable : (prefixWord ++ tailWord_6498976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6498976).length < 2 ^ (prefixWord ++ tailWord_6498976).sum := by decide
  have hdescent : baseEnd_6498976 < baseStart_6498976 := by decide
  rcases family_descends (prefixWord ++ tailWord_6498976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6498997 : List Nat := [1, 3, 3, 3, 1, 1, 2, 3, 2, 4]
def baseStart_6498997 : Nat := 118140960795 + 6498997 * 2 ^ 59
def prefixEnd_6498997 : Nat := 4983230072969 + 3 ^ 40 * 6498997 * 2
def baseEnd_6498997 : Nat := 1112369744376071459349721

theorem tailTrace_6498997 : CollatzResearch.WordTrace tailWord_6498997 prefixEnd_6498997 1112369744376071459349721 := by
  unfold tailWord_6498997
  simp only [CollatzResearch.WordTrace]
  refine ⟨237037894036251284165847245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158025262690834189443898163 237037894036251284165847245)
  ·
    refine ⟨88889210263594231562192717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 237037894036251284165847245 88889210263594231562192717)
    ·
      refine ⟨33333453848847836835822269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88889210263594231562192717 33333453848847836835822269)
      ·
        refine ⟨12500045193317938813433351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33333453848847836835822269 12500045193317938813433351)
        ·
          refine ⟨18750067789976908220150027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12500045193317938813433351 18750067789976908220150027)
          ·
            refine ⟨28125101684965362330225041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18750067789976908220150027 28125101684965362330225041)
            ·
              refine ⟨21093826263724021747668781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28125101684965362330225041 21093826263724021747668781)
              ·
                refine ⟨7910184848896508155375793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21093826263724021747668781 7910184848896508155375793)
                ·
                  refine ⟨5932638636672381116531845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7910184848896508155375793 5932638636672381116531845)
                  ·
                    refine ⟨1112369744376071459349721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5932638636672381116531845 1112369744376071459349721)
                    ·
                      rfl

theorem cell23_6498997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 3, 2, 4].length) (baseStart_6498997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6498997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6498997 prefixEnd_6498997 := by exact prefixLift 6498997
  have htrace : WordTrace (prefixWord ++ tailWord_6498997) baseStart_6498997 baseEnd_6498997 := by
    simpa [prefixWord, tailWord_6498997, baseEnd_6498997] using wordTrace_append hprefix tailTrace_6498997
  have hstable : (prefixWord ++ tailWord_6498997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6498997).length < 2 ^ (prefixWord ++ tailWord_6498997).sum := by decide
  have hdescent : baseEnd_6498997 < baseStart_6498997 := by decide
  rcases family_descends (prefixWord ++ tailWord_6498997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6499061 : List Nat := [1, 3, 6, 1, 1, 2, 2, 7]
def baseStart_6499061 : Nat := 118140960795 + 6499061 * 2 ^ 59
def prefixEnd_6499061 : Nat := 4983230072969 + 3 ^ 40 * 6499061 * 2
def baseEnd_6499061 : Nat := 123597855403337115838847

theorem tailTrace_6499061 : CollatzResearch.WordTrace tailWord_6499061 prefixEnd_6499061 123597855403337115838847 := by
  unfold tailWord_6499061
  simp only [CollatzResearch.WordTrace]
  refine ⟨237040228308019423096177037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158026818872012948730784691 237040228308019423096177037)
  ·
    refine ⟨88890085615507283661066389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 237040228308019423096177037 88890085615507283661066389)
    ·
      refine ⟨4166722763226903921612487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 88890085615507283661066389 4166722763226903921612487)
      ·
        refine ⟨6250084144840355882418731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4166722763226903921612487 6250084144840355882418731)
        ·
          refine ⟨9375126217260533823628097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6250084144840355882418731 9375126217260533823628097)
          ·
            refine ⟨7031344662945400367721073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9375126217260533823628097 7031344662945400367721073)
            ·
              refine ⟨5273508497209050275790805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7031344662945400367721073 5273508497209050275790805)
              ·
                refine ⟨123597855403337115838847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5273508497209050275790805 123597855403337115838847)
                ·
                  rfl

theorem cell23_6499061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 2, 7].length) (baseStart_6499061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6499061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6499061 prefixEnd_6499061 := by exact prefixLift 6499061
  have htrace : WordTrace (prefixWord ++ tailWord_6499061) baseStart_6499061 baseEnd_6499061 := by
    simpa [prefixWord, tailWord_6499061, baseEnd_6499061] using wordTrace_append hprefix tailTrace_6499061
  have hstable : (prefixWord ++ tailWord_6499061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6499061).length < 2 ^ (prefixWord ++ tailWord_6499061).sum := by decide
  have hdescent : baseEnd_6499061 < baseStart_6499061 := by decide
  rcases family_descends (prefixWord ++ tailWord_6499061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6499063 : List Nat := [1, 1, 3, 1, 1, 1, 3, 4, 2, 1, 5]
def baseStart_6499063 : Nat := 118140960795 + 6499063 * 2 ^ 59
def prefixEnd_6499063 : Nat := 4983230072969 + 3 ^ 40 * 6499063 * 2
def baseEnd_6499063 : Nat := 3337143122851411119823859

theorem tailTrace_6499063 : CollatzResearch.WordTrace tailWord_6499063 prefixEnd_6499063 3337143122851411119823859 := by
  unfold tailWord_6499063
  simp only [CollatzResearch.WordTrace]
  refine ⟨237040301254012177437749843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158026867502674784958499895 237040301254012177437749843)
  ·
    refine ⟨355560451881018266156624765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237040301254012177437749843 355560451881018266156624765)
    ·
      refine ⟨133335169455381849808734287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 355560451881018266156624765 133335169455381849808734287)
      ·
        refine ⟨200002754183072774713101431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133335169455381849808734287 200002754183072774713101431)
        ·
          refine ⟨300004131274609162069652147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200002754183072774713101431 300004131274609162069652147)
          ·
            refine ⟨450006196911913743104478221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 300004131274609162069652147 450006196911913743104478221)
            ·
              refine ⟨168752323841967653664179333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 450006196911913743104478221 168752323841967653664179333)
              ·
                refine ⟨31641060720368935062033625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 168752323841967653664179333 31641060720368935062033625)
                ·
                  refine ⟨23730795540276701296525219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31641060720368935062033625 23730795540276701296525219)
                  ·
                    refine ⟨35596193310415051944787829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23730795540276701296525219 35596193310415051944787829)
                    ·
                      refine ⟨3337143122851411119823859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35596193310415051944787829 3337143122851411119823859)
                      ·
                        rfl

theorem cell23_6499063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 4, 2, 1, 5].length) (baseStart_6499063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6499063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6499063 prefixEnd_6499063 := by exact prefixLift 6499063
  have htrace : WordTrace (prefixWord ++ tailWord_6499063) baseStart_6499063 baseEnd_6499063 := by
    simpa [prefixWord, tailWord_6499063, baseEnd_6499063] using wordTrace_append hprefix tailTrace_6499063
  have hstable : (prefixWord ++ tailWord_6499063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6499063).length < 2 ^ (prefixWord ++ tailWord_6499063).sum := by decide
  have hdescent : baseEnd_6499063 < baseStart_6499063 := by decide
  rcases family_descends (prefixWord ++ tailWord_6499063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6499080 : List Nat := [2, 1, 3, 2, 2, 3, 1, 1, 2, 1, 5]
def baseStart_6499080 : Nat := 118140960795 + 6499080 * 2 ^ 59
def prefixEnd_6499080 : Nat := 4983230072969 + 3 ^ 40 * 6499080 * 2
def baseEnd_6499080 : Nat := 3337151852022537553311281

theorem tailTrace_6499080 : CollatzResearch.WordTrace tailWord_6499080 prefixEnd_6499080 3337151852022537553311281 := by
  unfold tailWord_6499080
  simp only [CollatzResearch.WordTrace]
  refine ⟨118520460647475294670559347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158027280863300392894079129 118520460647475294670559347)
  ·
    refine ⟨177780690971212942005839021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118520460647475294670559347 177780690971212942005839021)
    ·
      refine ⟨66667759114204853252189633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177780690971212942005839021 66667759114204853252189633)
      ·
        refine ⟨50000819335653639939142225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66667759114204853252189633 50000819335653639939142225)
        ·
          refine ⟨37500614501740229954356669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50000819335653639939142225 37500614501740229954356669)
          ·
            refine ⟨14062730438152586232883751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37500614501740229954356669 14062730438152586232883751)
            ·
              refine ⟨21094095657228879349325627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14062730438152586232883751 21094095657228879349325627)
              ·
                refine ⟨31641143485843319023988441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21094095657228879349325627 31641143485843319023988441)
                ·
                  refine ⟨23730857614382489267991331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31641143485843319023988441 23730857614382489267991331)
                  ·
                    refine ⟨35596286421573733901986997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23730857614382489267991331 35596286421573733901986997)
                    ·
                      refine ⟨3337151852022537553311281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35596286421573733901986997 3337151852022537553311281)
                      ·
                        rfl

theorem cell23_6499080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 1, 2, 1, 5].length) (baseStart_6499080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6499080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6499080 prefixEnd_6499080 := by exact prefixLift 6499080
  have htrace : WordTrace (prefixWord ++ tailWord_6499080) baseStart_6499080 baseEnd_6499080 := by
    simpa [prefixWord, tailWord_6499080, baseEnd_6499080] using wordTrace_append hprefix tailTrace_6499080
  have hstable : (prefixWord ++ tailWord_6499080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6499080).length < 2 ^ (prefixWord ++ tailWord_6499080).sum := by decide
  have hdescent : baseEnd_6499080 < baseStart_6499080 := by decide
  rcases family_descends (prefixWord ++ tailWord_6499080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6499093 : List Nat := [1, 3, 2, 1, 2, 2, 1, 1, 1, 2, 7]
def baseStart_6499093 : Nat := 118140960795 + 6499093 * 2 ^ 59
def prefixEnd_6499093 : Nat := 4983230072969 + 3 ^ 40 * 6499093 * 2
def baseEnd_6499093 : Nat := 3337158527271046002448721

theorem tailTrace_6499093 : CollatzResearch.WordTrace tailWord_6499093 prefixEnd_6499093 3337158527271046002448721 := by
  unfold tailWord_6499093
  simp only [CollatzResearch.WordTrace]
  refine ⟨237041395443903492561341933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158027596962602328374227955 237041395443903492561341933)
  ·
    refine ⟨88890523291463809710503225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 237041395443903492561341933 88890523291463809710503225)
    ·
      refine ⟨66667892468597857282877419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88890523291463809710503225 66667892468597857282877419)
      ·
        refine ⟨100001838702896785924316129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66667892468597857282877419 100001838702896785924316129)
        ·
          refine ⟨75001379027172589443237097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100001838702896785924316129 75001379027172589443237097)
          ·
            refine ⟨56251034270379442082427823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75001379027172589443237097 56251034270379442082427823)
            ·
              refine ⟨84376551405569163123641735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56251034270379442082427823 84376551405569163123641735)
              ·
                refine ⟨126564827108353744685462603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84376551405569163123641735 126564827108353744685462603)
                ·
                  refine ⟨189847240662530617028193905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 126564827108353744685462603 189847240662530617028193905)
                  ·
                    refine ⟨142385430496897962771145429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 189847240662530617028193905 142385430496897962771145429)
                    ·
                      refine ⟨3337158527271046002448721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 142385430496897962771145429 3337158527271046002448721)
                      ·
                        rfl

theorem cell23_6499093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 1, 1, 2, 7].length) (baseStart_6499093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6499093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6499093 prefixEnd_6499093 := by exact prefixLift 6499093
  have htrace : WordTrace (prefixWord ++ tailWord_6499093) baseStart_6499093 baseEnd_6499093 := by
    simpa [prefixWord, tailWord_6499093, baseEnd_6499093] using wordTrace_append hprefix tailTrace_6499093
  have hstable : (prefixWord ++ tailWord_6499093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6499093).length < 2 ^ (prefixWord ++ tailWord_6499093).sum := by decide
  have hdescent : baseEnd_6499093 < baseStart_6499093 := by decide
  rcases family_descends (prefixWord ++ tailWord_6499093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6499100 : List Nat := [2, 2, 3, 1, 1, 3, 3, 1, 7]
def baseStart_6499100 : Nat := 118140960795 + 6499100 * 2 ^ 59
def prefixEnd_6499100 : Nat := 4983230072969 + 3 ^ 40 * 6499100 * 2
def baseEnd_6499100 : Nat := 370795791292847497229021

theorem tailTrace_6499100 : CollatzResearch.WordTrace tailWord_6499100 prefixEnd_6499100 370795791292847497229021 := by
  unfold tailWord_6499100
  simp only [CollatzResearch.WordTrace]
  refine ⟨118520825377439066378423377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158027767169918755171231169 118520825377439066378423377)
  ·
    refine ⟨88890619033079299783817533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118520825377439066378423377 88890619033079299783817533)
    ·
      refine ⟨33333982137404737418931575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88890619033079299783817533 33333982137404737418931575)
      ·
        refine ⟨50000973206107106128397363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33333982137404737418931575 50000973206107106128397363)
        ·
          refine ⟨75001459809160659192596045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50000973206107106128397363 75001459809160659192596045)
          ·
            refine ⟨28125547428435247197223517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75001459809160659192596045 28125547428435247197223517)
            ·
              refine ⟨10547080285663217698958819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28125547428435247197223517 10547080285663217698958819)
              ·
                refine ⟨15820620428494826548438229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10547080285663217698958819 15820620428494826548438229)
                ·
                  refine ⟨370795791292847497229021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15820620428494826548438229 370795791292847497229021)
                  ·
                    rfl

theorem cell23_6499100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 3, 1, 7].length) (baseStart_6499100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6499100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6499100 prefixEnd_6499100 := by exact prefixLift 6499100
  have htrace : WordTrace (prefixWord ++ tailWord_6499100) baseStart_6499100 baseEnd_6499100 := by
    simpa [prefixWord, tailWord_6499100, baseEnd_6499100] using wordTrace_append hprefix tailTrace_6499100
  have hstable : (prefixWord ++ tailWord_6499100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6499100).length < 2 ^ (prefixWord ++ tailWord_6499100).sum := by decide
  have hdescent : baseEnd_6499100 < baseStart_6499100 := by decide
  rcases family_descends (prefixWord ++ tailWord_6499100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6499160 : List Nat := [2, 1, 2, 2, 1, 1, 1, 2, 7, 4]
def baseStart_6499160 : Nat := 118140960795 + 6499160 * 2 ^ 59
def prefixEnd_6499160 : Nat := 4983230072969 + 3 ^ 40 * 6499160 * 2
def baseEnd_6499160 : Nat := 1112397643491632413436971

theorem tailTrace_6499160 : CollatzResearch.WordTrace tailWord_6499160 prefixEnd_6499160 1112397643491632413436971 := by
  unfold tailWord_6499160
  simp only [CollatzResearch.WordTrace]
  refine ⟨118521919567330381502015467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158029226089773842002687289 118521919567330381502015467)
  ·
    refine ⟨177782879350995572253023201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118521919567330381502015467 177782879350995572253023201)
    ·
      refine ⟨133337159513246679189767401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177782879350995572253023201 133337159513246679189767401)
      ·
        refine ⟨100002869634935009392325551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133337159513246679189767401 100002869634935009392325551)
        ·
          refine ⟨150004304452402514088488327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100002869634935009392325551 150004304452402514088488327)
          ·
            refine ⟨225006456678603771132732491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150004304452402514088488327 225006456678603771132732491)
            ·
              refine ⟨337509685017905656699098737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 225006456678603771132732491 337509685017905656699098737)
              ·
                refine ⟨253132263763429242524324053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 337509685017905656699098737 253132263763429242524324053)
                ·
                  refine ⟨5932787431955372871663845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 253132263763429242524324053 5932787431955372871663845)
                  ·
                    refine ⟨1112397643491632413436971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5932787431955372871663845 1112397643491632413436971)
                    ·
                      rfl

theorem cell23_6499160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 7, 4].length) (baseStart_6499160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6499160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6499160 prefixEnd_6499160 := by exact prefixLift 6499160
  have htrace : WordTrace (prefixWord ++ tailWord_6499160) baseStart_6499160 baseEnd_6499160 := by
    simpa [prefixWord, tailWord_6499160, baseEnd_6499160] using wordTrace_append hprefix tailTrace_6499160
  have hstable : (prefixWord ++ tailWord_6499160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6499160).length < 2 ^ (prefixWord ++ tailWord_6499160).sum := by decide
  have hdescent : baseEnd_6499160 < baseStart_6499160 := by decide
  rcases family_descends (prefixWord ++ tailWord_6499160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6499167 : List Nat := [1, 1, 2, 3, 1, 3, 3, 1, 2, 4, 2]
def baseStart_6499167 : Nat := 118140960795 + 6499167 * 2 ^ 59
def prefixEnd_6499167 : Nat := 4983230072969 + 3 ^ 40 * 6499167 * 2
def baseEnd_6499167 : Nat := 3337196524839478712923381

theorem tailTrace_6499167 : CollatzResearch.WordTrace tailWord_6499167 prefixEnd_6499167 3337196524839478712923381 := by
  unfold tailWord_6499167
  simp only [CollatzResearch.WordTrace]
  refine ⟨237044094445635403199535755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158029396297090268799690503 237044094445635403199535755)
  ·
    refine ⟨355566141668453104799303633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237044094445635403199535755 355566141668453104799303633)
    ·
      refine ⟨266674606251339828599477725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 355566141668453104799303633 266674606251339828599477725)
      ·
        refine ⟨100002977344252435724804147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 266674606251339828599477725 100002977344252435724804147)
        ·
          refine ⟨150004466016378653587206221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100002977344252435724804147 150004466016378653587206221)
          ·
            refine ⟨56251674756141995095202333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 150004466016378653587206221 56251674756141995095202333)
            ·
              refine ⟨21094378033553248160700875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56251674756141995095202333 21094378033553248160700875)
              ·
                refine ⟨31641567050329872241051313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21094378033553248160700875 31641567050329872241051313)
                ·
                  refine ⟨23731175287747404180788485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31641567050329872241051313 23731175287747404180788485)
                  ·
                    refine ⟨4449595366452638283897841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23731175287747404180788485 4449595366452638283897841)
                    ·
                      refine ⟨3337196524839478712923381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4449595366452638283897841 3337196524839478712923381)
                      ·
                        rfl

theorem cell23_6499167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 1, 2, 4, 2].length) (baseStart_6499167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6499167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6499167 prefixEnd_6499167 := by exact prefixLift 6499167
  have htrace : WordTrace (prefixWord ++ tailWord_6499167) baseStart_6499167 baseEnd_6499167 := by
    simpa [prefixWord, tailWord_6499167, baseEnd_6499167] using wordTrace_append hprefix tailTrace_6499167
  have hstable : (prefixWord ++ tailWord_6499167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6499167).length < 2 ^ (prefixWord ++ tailWord_6499167).sum := by decide
  have hdescent : baseEnd_6499167 < baseStart_6499167 := by decide
  rcases family_descends (prefixWord ++ tailWord_6499167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6499187 : List Nat := [1, 1, 1, 2, 2, 1, 7, 1, 2, 2, 3]
def baseStart_6499187 : Nat := 118140960795 + 6499187 * 2 ^ 59
def prefixEnd_6499187 : Nat := 4983230072969 + 3 ^ 40 * 6499187 * 2
def baseEnd_6499187 : Nat := 3337206794452568634673289

theorem tailTrace_6499187 : CollatzResearch.WordTrace tailWord_6499187 prefixEnd_6499187 3337206794452568634673289 := by
  unfold tailWord_6499187
  simp only [CollatzResearch.WordTrace]
  refine ⟨237044823905562946615263815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158029882603708631076842543 237044823905562946615263815)
  ·
    refine ⟨355567235858344419922895723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237044823905562946615263815 355567235858344419922895723)
    ·
      refine ⟨533350853787516629884343585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 355567235858344419922895723 533350853787516629884343585)
      ·
        refine ⟨400013140340637472413257689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 533350853787516629884343585 400013140340637472413257689)
        ·
          refine ⟨300009855255478104309943267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 400013140340637472413257689 300009855255478104309943267)
          ·
            refine ⟨450014782883217156464914901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 300009855255478104309943267 450014782883217156464914901)
            ·
              refine ⟨10547221473825402104646443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 450014782883217156464914901 10547221473825402104646443)
              ·
                refine ⟨15820832210738103156969665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10547221473825402104646443 15820832210738103156969665)
                ·
                  refine ⟨11865624158053577367727249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15820832210738103156969665 11865624158053577367727249)
                  ·
                    refine ⟨8899218118540183025795437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11865624158053577367727249 8899218118540183025795437)
                    ·
                      refine ⟨3337206794452568634673289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8899218118540183025795437 3337206794452568634673289)
                      ·
                        rfl

theorem cell23_6499187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 7, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 7, 1, 2, 2, 3].length) (baseStart_6499187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6499187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6499187 prefixEnd_6499187 := by exact prefixLift 6499187
  have htrace : WordTrace (prefixWord ++ tailWord_6499187) baseStart_6499187 baseEnd_6499187 := by
    simpa [prefixWord, tailWord_6499187, baseEnd_6499187] using wordTrace_append hprefix tailTrace_6499187
  have hstable : (prefixWord ++ tailWord_6499187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6499187).length < 2 ^ (prefixWord ++ tailWord_6499187).sum := by decide
  have hdescent : baseEnd_6499187 < baseStart_6499187 := by decide
  rcases family_descends (prefixWord ++ tailWord_6499187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6499207 : List Nat := [1, 1, 4, 2, 3, 1, 3, 2, 6]
def baseStart_6499207 : Nat := 118140960795 + 6499207 * 2 ^ 59
def prefixEnd_6499207 : Nat := 4983230072969 + 3 ^ 40 * 6499207 * 2
def baseEnd_6499207 : Nat := 370801896007295395158133

theorem tailTrace_6499207 : CollatzResearch.WordTrace tailWord_6499207 prefixEnd_6499207 370801896007295395158133 := by
  unfold tailWord_6499207
  simp only [CollatzResearch.WordTrace]
  refine ⟨237045553365490490030991875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158030368910326993353994583 237045553365490490030991875)
  ·
    refine ⟨355568330048235735046487813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237045553365490490030991875 355568330048235735046487813)
    ·
      refine ⟨66669061884044200321216465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 355568330048235735046487813 66669061884044200321216465)
      ·
        refine ⟨50001796413033150240912349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66669061884044200321216465 50001796413033150240912349)
        ·
          refine ⟨18750673654887431340342131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50001796413033150240912349 18750673654887431340342131)
          ·
            refine ⟨28126010482331147010513197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18750673654887431340342131 28126010482331147010513197)
            ·
              refine ⟨10547253930874180128942449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28126010482331147010513197 10547253930874180128942449)
              ·
                refine ⟨7910440448155635096706837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10547253930874180128942449 7910440448155635096706837)
                ·
                  refine ⟨370801896007295395158133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7910440448155635096706837 370801896007295395158133)
                  ·
                    rfl

theorem cell23_6499207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 3, 2, 6].length) (baseStart_6499207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6499207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6499207 prefixEnd_6499207 := by exact prefixLift 6499207
  have htrace : WordTrace (prefixWord ++ tailWord_6499207) baseStart_6499207 baseEnd_6499207 := by
    simpa [prefixWord, tailWord_6499207, baseEnd_6499207] using wordTrace_append hprefix tailTrace_6499207
  have hstable : (prefixWord ++ tailWord_6499207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6499207).length < 2 ^ (prefixWord ++ tailWord_6499207).sum := by decide
  have hdescent : baseEnd_6499207 < baseStart_6499207 := by decide
  rcases family_descends (prefixWord ++ tailWord_6499207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6499245 : List Nat := [1, 5, 2, 3, 1, 2, 1, 3, 1, 4]
def baseStart_6499245 : Nat := 118140960795 + 6499245 * 2 ^ 59
def prefixEnd_6499245 : Nat := 4983230072969 + 3 ^ 40 * 6499245 * 2
def baseEnd_6499245 : Nat := 1112412192110176469249341

theorem tailTrace_6499245 : CollatzResearch.WordTrace tailWord_6499245 prefixEnd_6499245 1112412192110176469249341 := by
  unfold tailWord_6499245
  simp only [CollatzResearch.WordTrace]
  refine ⟨237046939339352822520875189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158031292892901881680583459 237046939339352822520875189)
  ·
    refine ⟨22223150563064327111332049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 237046939339352822520875189 22223150563064327111332049)
    ·
      refine ⟨16667362922298245333499037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22223150563064327111332049 16667362922298245333499037)
      ·
        refine ⟨6250261095861842000062139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16667362922298245333499037 6250261095861842000062139)
        ·
          refine ⟨9375391643792763000093209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6250261095861842000062139 9375391643792763000093209)
          ·
            refine ⟨7031543732844572250069907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9375391643792763000093209 7031543732844572250069907)
            ·
              refine ⟨10547315599266858375104861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7031543732844572250069907 10547315599266858375104861)
              ·
                refine ⟨3955243349725071890664323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10547315599266858375104861 3955243349725071890664323)
                ·
                  refine ⟨5932865024587607835996485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3955243349725071890664323 5932865024587607835996485)
                  ·
                    refine ⟨1112412192110176469249341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5932865024587607835996485 1112412192110176469249341)
                    ·
                      rfl

theorem cell23_6499245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 1, 3, 1, 4].length) (baseStart_6499245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6499245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6499245 prefixEnd_6499245 := by exact prefixLift 6499245
  have htrace : WordTrace (prefixWord ++ tailWord_6499245) baseStart_6499245 baseEnd_6499245 := by
    simpa [prefixWord, tailWord_6499245, baseEnd_6499245] using wordTrace_append hprefix tailTrace_6499245
  have hstable : (prefixWord ++ tailWord_6499245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6499245).length < 2 ^ (prefixWord ++ tailWord_6499245).sum := by decide
  have hdescent : baseEnd_6499245 < baseStart_6499245 := by decide
  rcases family_descends (prefixWord ++ tailWord_6499245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6499261 : List Nat := [1, 4, 1, 2, 4, 1, 1, 2, 2, 3, 2]
def baseStart_6499261 : Nat := 118140960795 + 6499261 * 2 ^ 59
def prefixEnd_6499261 : Nat := 4983230072969 + 3 ^ 40 * 6499261 * 2
def baseEnd_6499261 : Nat := 3337244792021001345147949

theorem tailTrace_6499261 : CollatzResearch.WordTrace tailWord_6499261 prefixEnd_6499261 3337244792021001345147949 := by
  unfold tailWord_6499261
  simp only [CollatzResearch.WordTrace]
  refine ⟨237047522907294857253457637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158031681938196571502305091 237047522907294857253457637)
  ·
    refine ⟨44446410545117785735023307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 237047522907294857253457637 44446410545117785735023307)
    ·
      refine ⟨66669615817676678602534961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44446410545117785735023307 66669615817676678602534961)
      ·
        refine ⟨50002211863257508951901221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66669615817676678602534961 50002211863257508951901221)
        ·
          refine ⟨9375414724360782928481479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50002211863257508951901221 9375414724360782928481479)
          ·
            refine ⟨14063122086541174392722219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9375414724360782928481479 14063122086541174392722219)
            ·
              refine ⟨21094683129811761589083329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14063122086541174392722219 21094683129811761589083329)
              ·
                refine ⟨15821012347358821191812497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21094683129811761589083329 15821012347358821191812497)
                ·
                  refine ⟨11865759260519115893859373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15821012347358821191812497 11865759260519115893859373)
                  ·
                    refine ⟨4449659722694668460197265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11865759260519115893859373 4449659722694668460197265)
                    ·
                      refine ⟨3337244792021001345147949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4449659722694668460197265 3337244792021001345147949)
                      ·
                        rfl

theorem cell23_6499261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 2, 2, 3, 2].length) (baseStart_6499261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6499261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6499261 prefixEnd_6499261 := by exact prefixLift 6499261
  have htrace : WordTrace (prefixWord ++ tailWord_6499261) baseStart_6499261 baseEnd_6499261 := by
    simpa [prefixWord, tailWord_6499261, baseEnd_6499261] using wordTrace_append hprefix tailTrace_6499261
  have hstable : (prefixWord ++ tailWord_6499261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6499261).length < 2 ^ (prefixWord ++ tailWord_6499261).sum := by decide
  have hdescent : baseEnd_6499261 < baseStart_6499261 := by decide
  rcases family_descends (prefixWord ++ tailWord_6499261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6499311 : List Nat := [1, 1, 2, 1, 4, 4, 3, 1, 1, 2, 3]
def baseStart_6499311 : Nat := 118140960795 + 6499311 * 2 ^ 59
def prefixEnd_6499311 : Nat := 4983230072969 + 3 ^ 40 * 6499311 * 2
def baseEnd_6499311 : Nat := 3337270466053726149522719

theorem tailTrace_6499311 : CollatzResearch.WordTrace tailWord_6499311 prefixEnd_6499311 3337270466053726149522719 := by
  unfold tailWord_6499311
  simp only [CollatzResearch.WordTrace]
  refine ⟨237049346557113715792777787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158032897704742477195185191 237049346557113715792777787)
  ·
    refine ⟨355574019835670573689166681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237049346557113715792777787 355574019835670573689166681)
    ·
      refine ⟨266680514876752930266875011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 355574019835670573689166681 266680514876752930266875011)
      ·
        refine ⟨400020772315129395400312517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266680514876752930266875011 400020772315129395400312517)
        ·
          refine ⟨75003894809086761637558597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 400020772315129395400312517 75003894809086761637558597)
          ·
            refine ⟨14063230276703767807042237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75003894809086761637558597 14063230276703767807042237)
            ·
              refine ⟨5273711353763912927640839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14063230276703767807042237 5273711353763912927640839)
              ·
                refine ⟨7910567030645869391461259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5273711353763912927640839 7910567030645869391461259)
                ·
                  refine ⟨11865850545968804087191889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7910567030645869391461259 11865850545968804087191889)
                  ·
                    refine ⟨8899387909476603065393917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11865850545968804087191889 8899387909476603065393917)
                    ·
                      refine ⟨3337270466053726149522719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8899387909476603065393917 3337270466053726149522719)
                      ·
                        rfl

theorem cell23_6499311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 3, 1, 1, 2, 3].length) (baseStart_6499311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6499311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6499311 prefixEnd_6499311 := by exact prefixLift 6499311
  have htrace : WordTrace (prefixWord ++ tailWord_6499311) baseStart_6499311 baseEnd_6499311 := by
    simpa [prefixWord, tailWord_6499311, baseEnd_6499311] using wordTrace_append hprefix tailTrace_6499311
  have hstable : (prefixWord ++ tailWord_6499311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6499311).length < 2 ^ (prefixWord ++ tailWord_6499311).sum := by decide
  have hdescent : baseEnd_6499311 < baseStart_6499311 := by decide
  rcases family_descends (prefixWord ++ tailWord_6499311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6499314 : List Nat := [3, 2, 1, 5, 2, 10]
def baseStart_6499314 : Nat := 118140960795 + 6499314 * 2 ^ 59
def prefixEnd_6499314 : Nat := 4983230072969 + 3 ^ 40 * 6499314 * 2
def baseEnd_6499314 : Nat := 13733629656360862706935

theorem tailTrace_6499314 : CollatzResearch.WordTrace tailWord_6499314 prefixEnd_6499314 13733629656360862706935 := by
  unfold tailWord_6499314
  simp only [CollatzResearch.WordTrace]
  refine ⟨59262363994025711826284249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158032970650735231536757997 59262363994025711826284249)
  ·
    refine ⟨44446772995519283869713187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59262363994025711826284249 44446772995519283869713187)
    ·
      refine ⟨66670159493278925804569781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44446772995519283869713187 66670159493278925804569781)
      ·
        refine ⟨6250327452494899294178417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 66670159493278925804569781 6250327452494899294178417)
        ·
          refine ⟨4687745589371174470633813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6250327452494899294178417 4687745589371174470633813)
          ·
            refine ⟨13733629656360862706935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4687745589371174470633813 13733629656360862706935)
            ·
              rfl

theorem cell23_6499314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 10].length) (baseStart_6499314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6499314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6499314 prefixEnd_6499314 := by exact prefixLift 6499314
  have htrace : WordTrace (prefixWord ++ tailWord_6499314) baseStart_6499314 baseEnd_6499314 := by
    simpa [prefixWord, tailWord_6499314, baseEnd_6499314] using wordTrace_append hprefix tailTrace_6499314
  have hstable : (prefixWord ++ tailWord_6499314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6499314).length < 2 ^ (prefixWord ++ tailWord_6499314).sum := by decide
  have hdescent : baseEnd_6499314 < baseStart_6499314 := by decide
  rcases family_descends (prefixWord ++ tailWord_6499314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6499351 : List Nat := [1, 1, 3, 5, 1, 1, 2, 1, 3, 3, 2]
def baseStart_6499351 : Nat := 118140960795 + 6499351 * 2 ^ 59
def prefixEnd_6499351 : Nat := 4983230072969 + 3 ^ 40 * 6499351 * 2
def baseEnd_6499351 : Nat := 3337291005279905993022535

theorem tailTrace_6499351 : CollatzResearch.WordTrace tailWord_6499351 prefixEnd_6499351 3337291005279905993022535 := by
  unfold tailWord_6499351
  simp only [CollatzResearch.WordTrace]
  refine ⟨237050805476968802624233907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158033870317979201749489271 237050805476968802624233907)
  ·
    refine ⟨355576208215453203936350861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237050805476968802624233907 355576208215453203936350861)
    ·
      refine ⟨133341078080794951476131573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 355576208215453203936350861 133341078080794951476131573)
      ·
        refine ⟨12500726070074526700887335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 133341078080794951476131573 12500726070074526700887335)
        ·
          refine ⟨18751089105111790051331003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12500726070074526700887335 18751089105111790051331003)
          ·
            refine ⟨28126633657667685076996505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18751089105111790051331003 28126633657667685076996505)
            ·
              refine ⟨21094975243250763807747379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28126633657667685076996505 21094975243250763807747379)
              ·
                refine ⟨31642462864876145711621069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21094975243250763807747379 31642462864876145711621069)
                ·
                  refine ⟨11865923574328554641857901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31642462864876145711621069 11865923574328554641857901)
                  ·
                    refine ⟨4449721340373207990696713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11865923574328554641857901 4449721340373207990696713)
                    ·
                      refine ⟨3337291005279905993022535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4449721340373207990696713 3337291005279905993022535)
                      ·
                        rfl

theorem cell23_6499351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 1, 3, 3, 2].length) (baseStart_6499351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6499351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6499351 prefixEnd_6499351 := by exact prefixLift 6499351
  have htrace : WordTrace (prefixWord ++ tailWord_6499351) baseStart_6499351 baseEnd_6499351 := by
    simpa [prefixWord, tailWord_6499351, baseEnd_6499351] using wordTrace_append hprefix tailTrace_6499351
  have hstable : (prefixWord ++ tailWord_6499351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6499351).length < 2 ^ (prefixWord ++ tailWord_6499351).sum := by decide
  have hdescent : baseEnd_6499351 < baseStart_6499351 := by decide
  rcases family_descends (prefixWord ++ tailWord_6499351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6499377 : List Nat := [1, 2, 2, 3, 1, 2, 1, 1, 4, 2, 4]
def baseStart_6499377 : Nat := 118140960795 + 6499377 * 2 ^ 59
def prefixEnd_6499377 : Nat := 4983230072969 + 3 ^ 40 * 6499377 * 2
def baseEnd_6499377 : Nat := 3337304355776922891297415

theorem tailTrace_6499377 : CollatzResearch.WordTrace tailWord_6499377 prefixEnd_6499377 3337304355776922891297415 := by
  unfold tailWord_6499377
  simp only [CollatzResearch.WordTrace]
  refine ⟨237051753774874609064680385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158034502516583072709786923 237051753774874609064680385)
  ·
    refine ⟨177788815331155956798510289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237051753774874609064680385 177788815331155956798510289)
    ·
      refine ⟨133341611498366967598882717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177788815331155956798510289 133341611498366967598882717)
      ·
        refine ⟨50003104311887612849581019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133341611498366967598882717 50003104311887612849581019)
        ·
          refine ⟨75004656467831419274371529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50003104311887612849581019 75004656467831419274371529)
          ·
            refine ⟨56253492350873564455778647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75004656467831419274371529 56253492350873564455778647)
            ·
              refine ⟨84380238526310346683667971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56253492350873564455778647 84380238526310346683667971)
              ·
                refine ⟨126570357789465520025501957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84380238526310346683667971 126570357789465520025501957)
                ·
                  refine ⟨23731942085524785004781617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 126570357789465520025501957 23731942085524785004781617)
                  ·
                    refine ⟨17798956564143588753586213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23731942085524785004781617 17798956564143588753586213)
                    ·
                      refine ⟨3337304355776922891297415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17798956564143588753586213 3337304355776922891297415)
                      ·
                        rfl

theorem cell23_6499377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 1, 4, 2, 4].length) (baseStart_6499377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6499377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6499377 prefixEnd_6499377 := by exact prefixLift 6499377
  have htrace : WordTrace (prefixWord ++ tailWord_6499377) baseStart_6499377 baseEnd_6499377 := by
    simpa [prefixWord, tailWord_6499377, baseEnd_6499377] using wordTrace_append hprefix tailTrace_6499377
  have hstable : (prefixWord ++ tailWord_6499377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6499377).length < 2 ^ (prefixWord ++ tailWord_6499377).sum := by decide
  have hdescent : baseEnd_6499377 < baseStart_6499377 := by decide
  rcases family_descends (prefixWord ++ tailWord_6499377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6499427 : List Nat := [1, 1, 1, 5, 1, 1, 1, 4, 1, 2, 5]
def baseStart_6499427 : Nat := 118140960795 + 6499427 * 2 ^ 59
def prefixEnd_6499427 : Nat := 4983230072969 + 3 ^ 40 * 6499427 * 2
def baseEnd_6499427 : Nat := 3337330029809647695672185

theorem tailTrace_6499427 : CollatzResearch.WordTrace tailWord_6499427 prefixEnd_6499427 3337330029809647695672185 := by
  unfold tailWord_6499427
  simp only [CollatzResearch.WordTrace]
  refine ⟨237053577424693467604000535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158035718283128978402667023 237053577424693467604000535)
  ·
    refine ⟨355580366137040201406000803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237053577424693467604000535 355580366137040201406000803)
    ·
      refine ⟨533370549205560302109001205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 355580366137040201406000803 533370549205560302109001205)
      ·
        refine ⟨50003488988021278322718863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 533370549205560302109001205 50003488988021278322718863)
        ·
          refine ⟨75005233482031917484078295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50003488988021278322718863 75005233482031917484078295)
          ·
            refine ⟨112507850223047876226117443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75005233482031917484078295 112507850223047876226117443)
            ·
              refine ⟨168761775334571814339176165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112507850223047876226117443 168761775334571814339176165)
              ·
                refine ⟨31642832875232215188595531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 168761775334571814339176165 31642832875232215188595531)
                ·
                  refine ⟨47464249312848322782893297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31642832875232215188595531 47464249312848322782893297)
                  ·
                    refine ⟨35598186984636242087169973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47464249312848322782893297 35598186984636242087169973)
                    ·
                      refine ⟨3337330029809647695672185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35598186984636242087169973 3337330029809647695672185)
                      ·
                        rfl

theorem cell23_6499427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 4, 1, 2, 5].length) (baseStart_6499427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6499427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6499427 prefixEnd_6499427 := by exact prefixLift 6499427
  have htrace : WordTrace (prefixWord ++ tailWord_6499427) baseStart_6499427 baseEnd_6499427 := by
    simpa [prefixWord, tailWord_6499427, baseEnd_6499427] using wordTrace_append hprefix tailTrace_6499427
  have hstable : (prefixWord ++ tailWord_6499427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6499427).length < 2 ^ (prefixWord ++ tailWord_6499427).sum := by decide
  have hdescent : baseEnd_6499427 < baseStart_6499427 := by decide
  rcases family_descends (prefixWord ++ tailWord_6499427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6499434 : List Nat := [3, 1, 3, 2, 2, 1, 1, 1, 4, 5]
def baseStart_6499434 : Nat := 118140960795 + 6499434 * 2 ^ 59
def prefixEnd_6499434 : Nat := 4983230072969 + 3 ^ 40 * 6499434 * 2
def baseEnd_6499434 : Nat := 1112444541391409722761551

theorem tailTrace_6499434 : CollatzResearch.WordTrace tailWord_6499434 prefixEnd_6499434 1112444541391409722761551 := by
  unfold tailWord_6499434
  simp only [CollatzResearch.WordTrace]
  refine ⟨59263458183917026949876339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158035888490445405199670237 59263458183917026949876339)
  ·
    refine ⟨88895187275875540424814509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59263458183917026949876339 88895187275875540424814509)
    ·
      refine ⟨33335695228453327659305441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88895187275875540424814509 33335695228453327659305441)
      ·
        refine ⟨25001771421339995744479081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33335695228453327659305441 25001771421339995744479081)
        ·
          refine ⟨18751328566004996808359311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25001771421339995744479081 18751328566004996808359311)
          ·
            refine ⟨28126992849007495212538967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18751328566004996808359311 28126992849007495212538967)
            ·
              refine ⟨42190489273511242818808451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28126992849007495212538967 42190489273511242818808451)
              ·
                refine ⟨63285733910266864228212677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42190489273511242818808451 63285733910266864228212677)
                ·
                  refine ⟨11866075108175037042789877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63285733910266864228212677 11866075108175037042789877)
                  ·
                    refine ⟨1112444541391409722761551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11866075108175037042789877 1112444541391409722761551)
                    ·
                      rfl

theorem cell23_6499434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 1, 4, 5].length) (baseStart_6499434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6499434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6499434 prefixEnd_6499434 := by exact prefixLift 6499434
  have htrace : WordTrace (prefixWord ++ tailWord_6499434) baseStart_6499434 baseEnd_6499434 := by
    simpa [prefixWord, tailWord_6499434, baseEnd_6499434] using wordTrace_append hprefix tailTrace_6499434
  have hstable : (prefixWord ++ tailWord_6499434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6499434).length < 2 ^ (prefixWord ++ tailWord_6499434).sum := by decide
  have hdescent : baseEnd_6499434 < baseStart_6499434 := by decide
  rcases family_descends (prefixWord ++ tailWord_6499434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6499438 : List Nat := [4, 1, 2, 2, 1, 3, 3, 2, 5]
def baseStart_6499438 : Nat := 118140960795 + 6499438 * 2 ^ 59
def prefixEnd_6499438 : Nat := 4983230072969 + 3 ^ 40 * 6499438 * 2
def baseEnd_6499438 : Nat := 370815075344094128070515

theorem tailTrace_6499438 : CollatzResearch.WordTrace tailWord_6499438 prefixEnd_6499438 370815075344094128070515 := by
  unfold tailWord_6499438
  simp only [CollatzResearch.WordTrace]
  refine ⟨29631747328456702060331371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 158035985751769077655100645 29631747328456702060331371)
  ·
    refine ⟨44447620992685053090497057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29631747328456702060331371 44447620992685053090497057)
    ·
      refine ⟨33335715744513789817872793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44447620992685053090497057 33335715744513789817872793)
      ·
        refine ⟨25001786808385342363404595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33335715744513789817872793 25001786808385342363404595)
        ·
          refine ⟨37502680212578013545106893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25001786808385342363404595 37502680212578013545106893)
          ·
            refine ⟨14063505079716755079415085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37502680212578013545106893 14063505079716755079415085)
            ·
              refine ⟨5273814404893783154780657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14063505079716755079415085 5273814404893783154780657)
              ·
                refine ⟨3955360803670337366085493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5273814404893783154780657 3955360803670337366085493)
                ·
                  refine ⟨370815075344094128070515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3955360803670337366085493 370815075344094128070515)
                  ·
                    rfl

theorem cell23_6499438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 3, 2, 5].length) (baseStart_6499438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6499438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6499438 prefixEnd_6499438 := by exact prefixLift 6499438
  have htrace : WordTrace (prefixWord ++ tailWord_6499438) baseStart_6499438 baseEnd_6499438 := by
    simpa [prefixWord, tailWord_6499438, baseEnd_6499438] using wordTrace_append hprefix tailTrace_6499438
  have hstable : (prefixWord ++ tailWord_6499438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6499438).length < 2 ^ (prefixWord ++ tailWord_6499438).sum := by decide
  have hdescent : baseEnd_6499438 < baseStart_6499438 := by decide
  rcases family_descends (prefixWord ++ tailWord_6499438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6499467 : List Nat := [1, 1, 1, 1, 4, 1, 1, 3, 2, 4, 4]
def baseStart_6499467 : Nat := 118140960795 + 6499467 * 2 ^ 59
def prefixEnd_6499467 : Nat := 4983230072969 + 3 ^ 40 * 6499467 * 2
def baseEnd_6499467 : Nat := 3337350569035827539172001

theorem tailTrace_6499467 : CollatzResearch.WordTrace tailWord_6499467 prefixEnd_6499467 3337350569035827539172001 := by
  unfold tailWord_6499467
  simp only [CollatzResearch.WordTrace]
  refine ⟨237055036344548554435456655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158036690896365702956971103 237055036344548554435456655)
  ·
    refine ⟨355582554516822831653184983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237055036344548554435456655 355582554516822831653184983)
    ·
      refine ⟨533373831775234247479777475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 355582554516822831653184983 533373831775234247479777475)
      ·
        refine ⟨800060747662851371219666213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 533373831775234247479777475 800060747662851371219666213)
        ·
          refine ⟨150011390186784632103687415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 800060747662851371219666213 150011390186784632103687415)
          ·
            refine ⟨225017085280176948155531123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150011390186784632103687415 225017085280176948155531123)
            ·
              refine ⟨337525627920265422233296685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 225017085280176948155531123 337525627920265422233296685)
              ·
                refine ⟨126572110470099533337486257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 337525627920265422233296685 126572110470099533337486257)
                ·
                  refine ⟨94929082852574650003114693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 126572110470099533337486257 94929082852574650003114693)
                  ·
                    refine ⟨17799203034857746875584005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 94929082852574650003114693 17799203034857746875584005)
                    ·
                      refine ⟨3337350569035827539172001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17799203034857746875584005 3337350569035827539172001)
                      ·
                        rfl

theorem cell23_6499467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 3, 2, 4, 4].length) (baseStart_6499467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6499467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6499467 prefixEnd_6499467 := by exact prefixLift 6499467
  have htrace : WordTrace (prefixWord ++ tailWord_6499467) baseStart_6499467 baseEnd_6499467 := by
    simpa [prefixWord, tailWord_6499467, baseEnd_6499467] using wordTrace_append hprefix tailTrace_6499467
  have hstable : (prefixWord ++ tailWord_6499467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6499467).length < 2 ^ (prefixWord ++ tailWord_6499467).sum := by decide
  have hdescent : baseEnd_6499467 < baseStart_6499467 := by decide
  rcases family_descends (prefixWord ++ tailWord_6499467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6499477 : List Nat := [1, 3, 2, 1, 1, 1, 2, 4, 8]
def baseStart_6499477 : Nat := 118140960795 + 6499477 * 2 ^ 59
def prefixEnd_6499477 : Nat := 4983230072969 + 3 ^ 40 * 6499477 * 2
def baseEnd_6499477 : Nat := 370817300426930277782995

theorem tailTrace_6499477 : CollatzResearch.WordTrace tailWord_6499477 prefixEnd_6499477 370817300426930277782995 := by
  unfold tailWord_6499477
  simp only [CollatzResearch.WordTrace]
  refine ⟨237055401074512326143320685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158036934049674884095547123 237055401074512326143320685)
  ·
    refine ⟨88895775402942122303745257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 237055401074512326143320685 88895775402942122303745257)
    ·
      refine ⟨66671831552206591727808943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88895775402942122303745257 66671831552206591727808943)
      ·
        refine ⟨100007747328309887591713415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66671831552206591727808943 100007747328309887591713415)
        ·
          refine ⟨150011620992464831387570123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100007747328309887591713415 150011620992464831387570123)
          ·
            refine ⟨225017431488697247081355185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150011620992464831387570123 225017431488697247081355185)
            ·
              refine ⟨168763073616522935311016389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 225017431488697247081355185 168763073616522935311016389)
              ·
                refine ⟨31643076303098050370815573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 168763073616522935311016389 31643076303098050370815573)
                ·
                  refine ⟨370817300426930277782995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31643076303098050370815573 370817300426930277782995)
                  ·
                    rfl

theorem cell23_6499477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 4, 8].length) (baseStart_6499477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6499477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6499477 prefixEnd_6499477 := by exact prefixLift 6499477
  have htrace : WordTrace (prefixWord ++ tailWord_6499477) baseStart_6499477 baseEnd_6499477 := by
    simpa [prefixWord, tailWord_6499477, baseEnd_6499477] using wordTrace_append hprefix tailTrace_6499477
  have hstable : (prefixWord ++ tailWord_6499477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6499477).length < 2 ^ (prefixWord ++ tailWord_6499477).sum := by decide
  have hdescent : baseEnd_6499477 < baseStart_6499477 := by decide
  rcases family_descends (prefixWord ++ tailWord_6499477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6499522 : List Nat := [3, 5, 1, 1, 2, 2, 1, 1, 2, 1, 4]
def baseStart_6499522 : Nat := 118140960795 + 6499522 * 2 ^ 59
def prefixEnd_6499522 : Nat := 4983230072969 + 3 ^ 40 * 6499522 * 2
def baseEnd_6499522 : Nat := 3337378810471824823984249

theorem tailTrace_6499522 : CollatzResearch.WordTrace tailWord_6499522 prefixEnd_6499522 3337378810471824823984249 := by
  unfold tailWord_6499522
  simp only [CollatzResearch.WordTrace]
  refine ⟨59264260589837324707177205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158038028239566199219139213 59264260589837324707177205)
  ·
    refine ⟨5556024430297249191297863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 59264260589837324707177205 5556024430297249191297863)
    ·
      refine ⟨8334036645445873786946795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5556024430297249191297863 8334036645445873786946795)
      ·
        refine ⟨12501054968168810680420193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8334036645445873786946795 12501054968168810680420193)
        ·
          refine ⟨9375791226126608010315145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12501054968168810680420193 9375791226126608010315145)
          ·
            refine ⟨7031843419594956007736359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9375791226126608010315145 7031843419594956007736359)
            ·
              refine ⟨10547765129392434011604539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7031843419594956007736359 10547765129392434011604539)
              ·
                refine ⟨15821647694088651017406809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10547765129392434011604539 15821647694088651017406809)
                ·
                  refine ⟨11866235770566488263055107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15821647694088651017406809 11866235770566488263055107)
                  ·
                    refine ⟨17799353655849732394582661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11866235770566488263055107 17799353655849732394582661)
                    ·
                      refine ⟨3337378810471824823984249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17799353655849732394582661 3337378810471824823984249)
                      ·
                        rfl

theorem cell23_6499522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_6499522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6499522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6499522 prefixEnd_6499522 := by exact prefixLift 6499522
  have htrace : WordTrace (prefixWord ++ tailWord_6499522) baseStart_6499522 baseEnd_6499522 := by
    simpa [prefixWord, tailWord_6499522, baseEnd_6499522] using wordTrace_append hprefix tailTrace_6499522
  have hstable : (prefixWord ++ tailWord_6499522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6499522).length < 2 ^ (prefixWord ++ tailWord_6499522).sum := by decide
  have hdescent : baseEnd_6499522 < baseStart_6499522 := by decide
  rcases family_descends (prefixWord ++ tailWord_6499522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6499531 : List Nat := [1, 1, 1, 1, 3, 2, 2, 5, 2, 3, 2]
def baseStart_6499531 : Nat := 118140960795 + 6499531 * 2 ^ 59
def prefixEnd_6499531 : Nat := 4983230072969 + 3 ^ 40 * 6499531 * 2
def baseEnd_6499531 : Nat := 3337383431797715288771707

theorem tailTrace_6499531 : CollatzResearch.WordTrace tailWord_6499531 prefixEnd_6499531 3337383431797715288771707 := by
  unfold tailWord_6499531
  simp only [CollatzResearch.WordTrace]
  refine ⟨237057370616316693365786447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158038247077544462243857631 237057370616316693365786447)
  ·
    refine ⟨355586055924475040048679671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237057370616316693365786447 355586055924475040048679671)
    ·
      refine ⟨533379083886712560073019507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 355586055924475040048679671 533379083886712560073019507)
      ·
        refine ⟨800068625830068840109529261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 533379083886712560073019507 800068625830068840109529261)
        ·
          refine ⟨300025734686275815041073473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 800068625830068840109529261 300025734686275815041073473)
          ·
            refine ⟨225019301014706861280805105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 300025734686275815041073473 225019301014706861280805105)
            ·
              refine ⟨168764475761030145960603829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 225019301014706861280805105 168764475761030145960603829)
              ·
                refine ⟨15821669602596576183806609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 168764475761030145960603829 15821669602596576183806609)
                ·
                  refine ⟨11866252201947432137854957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15821669602596576183806609 11866252201947432137854957)
                  ·
                    refine ⟨4449844575730287051695609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11866252201947432137854957 4449844575730287051695609)
                    ·
                      refine ⟨3337383431797715288771707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4449844575730287051695609 3337383431797715288771707)
                      ·
                        rfl

theorem cell23_6499531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 5, 2, 3, 2].length) (baseStart_6499531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6499531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6499531 prefixEnd_6499531 := by exact prefixLift 6499531
  have htrace : WordTrace (prefixWord ++ tailWord_6499531) baseStart_6499531 baseEnd_6499531 := by
    simpa [prefixWord, tailWord_6499531, baseEnd_6499531] using wordTrace_append hprefix tailTrace_6499531
  have hstable : (prefixWord ++ tailWord_6499531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6499531).length < 2 ^ (prefixWord ++ tailWord_6499531).sum := by decide
  have hdescent : baseEnd_6499531 < baseStart_6499531 := by decide
  rcases family_descends (prefixWord ++ tailWord_6499531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6499564 : List Nat := [2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 5]
def baseStart_6499564 : Nat := 118140960795 + 6499564 * 2 ^ 59
def prefixEnd_6499564 : Nat := 4983230072969 + 3 ^ 40 * 6499564 * 2
def baseEnd_6499564 : Nat := 3337400376659313659659055

theorem tailTrace_6499564 : CollatzResearch.WordTrace tailWord_6499564 prefixEnd_6499564 3337400376659313659659055 := by
  unfold tailWord_6499564
  simp only [CollatzResearch.WordTrace]
  refine ⟨118529287112598570000868873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158039049483464760001158497 118529287112598570000868873)
  ·
    refine ⟨88896965334448927500651655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118529287112598570000868873 88896965334448927500651655)
    ·
      refine ⟨133345448001673391250977483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88896965334448927500651655 133345448001673391250977483)
      ·
        refine ⟨200018172002510086876466225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133345448001673391250977483 200018172002510086876466225)
        ·
          refine ⟨150013629001882565157349669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 200018172002510086876466225 150013629001882565157349669)
          ·
            refine ⟨28127555437852980967003063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 150013629001882565157349669 28127555437852980967003063)
            ·
              refine ⟨42191333156779471450504595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28127555437852980967003063 42191333156779471450504595)
              ·
                refine ⟨63286999735169207175756893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42191333156779471450504595 63286999735169207175756893)
                ·
                  refine ⟨23732624900688452690908835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63286999735169207175756893 23732624900688452690908835)
                  ·
                    refine ⟨35598937351032679036363253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23732624900688452690908835 35598937351032679036363253)
                    ·
                      refine ⟨3337400376659313659659055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35598937351032679036363253 3337400376659313659659055)
                      ·
                        rfl

theorem cell23_6499564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 5].length) (baseStart_6499564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6499564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6499564 prefixEnd_6499564 := by exact prefixLift 6499564
  have htrace : WordTrace (prefixWord ++ tailWord_6499564) baseStart_6499564 baseEnd_6499564 := by
    simpa [prefixWord, tailWord_6499564, baseEnd_6499564] using wordTrace_append hprefix tailTrace_6499564
  have hstable : (prefixWord ++ tailWord_6499564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6499564).length < 2 ^ (prefixWord ++ tailWord_6499564).sum := by decide
  have hdescent : baseEnd_6499564 < baseStart_6499564 := by decide
  rcases family_descends (prefixWord ++ tailWord_6499564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6499571 : List Nat := [1, 1, 1, 2, 2, 7, 1, 1, 1, 6]
def baseStart_6499571 : Nat := 118140960795 + 6499571 * 2 ^ 59
def prefixEnd_6499571 : Nat := 4983230072969 + 3 ^ 40 * 6499571 * 2
def baseEnd_6499571 : Nat := 1112467990341298377423841

theorem tailTrace_6499571 : CollatzResearch.WordTrace tailWord_6499571 prefixEnd_6499571 1112467990341298377423841 := by
  unfold tailWord_6499571
  simp only [CollatzResearch.WordTrace]
  refine ⟨237058829536171780197242567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158039219690781186798161711 237058829536171780197242567)
  ·
    refine ⟨355588244304257670295863851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237058829536171780197242567 355588244304257670295863851)
    ·
      refine ⟨533382366456386505443795777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 355588244304257670295863851 533382366456386505443795777)
      ·
        refine ⟨400036774842289879082846833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 533382366456386505443795777 400036774842289879082846833)
        ·
          refine ⟨300027581131717409312135125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 400036774842289879082846833 300027581131717409312135125)
          ·
            refine ⟨7031896432774626780753167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 300027581131717409312135125 7031896432774626780753167)
            ·
              refine ⟨10547844649161940171129751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7031896432774626780753167 10547844649161940171129751)
              ·
                refine ⟨15821766973742910256694627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10547844649161940171129751 15821766973742910256694627)
                ·
                  refine ⟨23732650460614365385041941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15821766973742910256694627 23732650460614365385041941)
                  ·
                    refine ⟨1112467990341298377423841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23732650460614365385041941 1112467990341298377423841)
                    ·
                      rfl

theorem cell23_6499571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 1, 1, 1, 6].length) (baseStart_6499571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6499571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6499571 prefixEnd_6499571 := by exact prefixLift 6499571
  have htrace : WordTrace (prefixWord ++ tailWord_6499571) baseStart_6499571 baseEnd_6499571 := by
    simpa [prefixWord, tailWord_6499571, baseEnd_6499571] using wordTrace_append hprefix tailTrace_6499571
  have hstable : (prefixWord ++ tailWord_6499571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6499571).length < 2 ^ (prefixWord ++ tailWord_6499571).sum := by decide
  have hdescent : baseEnd_6499571 < baseStart_6499571 := by decide
  rcases family_descends (prefixWord ++ tailWord_6499571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6499578 : List Nat := [3, 1, 1, 1, 1, 4, 1, 4, 3, 2, 2]
def baseStart_6499578 : Nat := 118140960795 + 6499578 * 2 ^ 59
def prefixEnd_6499578 : Nat := 4983230072969 + 3 ^ 40 * 6499578 * 2
def baseEnd_6499578 : Nat := 3337407565388476604883991

theorem tailTrace_6499578 : CollatzResearch.WordTrace tailWord_6499578 prefixEnd_6499578 3337407565388476604883991 := by
  unfold tailWord_6499578
  simp only [CollatzResearch.WordTrace]
  refine ⟨59264771211786605098186847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158039389898097613595164925 59264771211786605098186847)
  ·
    refine ⟨88897156817679907647280271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59264771211786605098186847 88897156817679907647280271)
    ·
      refine ⟨133345735226519861470920407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88897156817679907647280271 133345735226519861470920407)
      ·
        refine ⟨200018602839779792206380611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133345735226519861470920407 200018602839779792206380611)
        ·
          refine ⟨300027904259669688309570917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200018602839779792206380611 300027904259669688309570917)
          ·
            refine ⟨56255232048688066558044547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 300027904259669688309570917 56255232048688066558044547)
            ·
              refine ⟨84382848073032099837066821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56255232048688066558044547 84382848073032099837066821)
              ·
                refine ⟨15821784013693518719450029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 84382848073032099837066821 15821784013693518719450029)
                ·
                  refine ⟨5933169005135069519793761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15821784013693518719450029 5933169005135069519793761)
                  ·
                    refine ⟨4449876753851302139845321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5933169005135069519793761 4449876753851302139845321)
                    ·
                      refine ⟨3337407565388476604883991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4449876753851302139845321 3337407565388476604883991)
                      ·
                        rfl

theorem cell23_6499578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 4, 3, 2, 2].length) (baseStart_6499578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6499578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6499578 prefixEnd_6499578 := by exact prefixLift 6499578
  have htrace : WordTrace (prefixWord ++ tailWord_6499578) baseStart_6499578 baseEnd_6499578 := by
    simpa [prefixWord, tailWord_6499578, baseEnd_6499578] using wordTrace_append hprefix tailTrace_6499578
  have hstable : (prefixWord ++ tailWord_6499578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6499578).length < 2 ^ (prefixWord ++ tailWord_6499578).sum := by decide
  have hdescent : baseEnd_6499578 < baseStart_6499578 := by decide
  rcases family_descends (prefixWord ++ tailWord_6499578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6499598 : List Nat := [4, 1, 1, 2, 1, 3, 2, 3, 1, 2, 3]
def baseStart_6499598 : Nat := 118140960795 + 6499598 * 2 ^ 59
def prefixEnd_6499598 : Nat := 4983230072969 + 3 ^ 40 * 6499598 * 2
def baseEnd_6499598 : Nat := 3337417835001566526633899

theorem tailTrace_6499598 : CollatzResearch.WordTrace tailWord_6499598 prefixEnd_6499598 3337417835001566526633899 := by
  unfold tailWord_6499598
  simp only [CollatzResearch.WordTrace]
  refine ⟨29632476788384245476059431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 158039876204715975872316965 29632476788384245476059431)
  ·
    refine ⟨44448715182576368214089147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29632476788384245476059431 44448715182576368214089147)
    ·
      refine ⟨66673072773864552321133721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44448715182576368214089147 66673072773864552321133721)
      ·
        refine ⟨50004804580398414240850291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66673072773864552321133721 50004804580398414240850291)
        ·
          refine ⟨75007206870597621361275437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50004804580398414240850291 75007206870597621361275437)
          ·
            refine ⟨28127702576474108010478289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75007206870597621361275437 28127702576474108010478289)
            ·
              refine ⟨21095776932355581007858717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28127702576474108010478289 21095776932355581007858717)
              ·
                refine ⟨7910916349633342877947019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21095776932355581007858717 7910916349633342877947019)
                ·
                  refine ⟨11866374524450014316920529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7910916349633342877947019 11866374524450014316920529)
                  ·
                    refine ⟨8899780893337510737690397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11866374524450014316920529 8899780893337510737690397)
                    ·
                      refine ⟨3337417835001566526633899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8899780893337510737690397 3337417835001566526633899)
                      ·
                        rfl

theorem cell23_6499598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 3, 1, 2, 3].length) (baseStart_6499598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6499598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6499598 prefixEnd_6499598 := by exact prefixLift 6499598
  have htrace : WordTrace (prefixWord ++ tailWord_6499598) baseStart_6499598 baseEnd_6499598 := by
    simpa [prefixWord, tailWord_6499598, baseEnd_6499598] using wordTrace_append hprefix tailTrace_6499598
  have hstable : (prefixWord ++ tailWord_6499598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6499598).length < 2 ^ (prefixWord ++ tailWord_6499598).sum := by decide
  have hdescent : baseEnd_6499598 < baseStart_6499598 := by decide
  rcases family_descends (prefixWord ++ tailWord_6499598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6499645 : List Nat := [1, 4, 1, 5, 1, 1, 1, 2, 1, 3, 3]
def baseStart_6499645 : Nat := 118140960795 + 6499645 * 2 ^ 59
def prefixEnd_6499645 : Nat := 4983230072969 + 3 ^ 40 * 6499645 * 2
def baseEnd_6499645 : Nat := 3337441968592327842746183

theorem tailTrace_6499645 : CollatzResearch.WordTrace tailWord_6499645 prefixEnd_6499645 3337441968592327842746183 := by
  unfold tailWord_6499645
  simp only [CollatzResearch.WordTrace]
  refine ⟨237061528537903690835436389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158041019025269127223624259 237061528537903690835436389)
  ·
    refine ⟨44449036600856942031644323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 237061528537903690835436389 44449036600856942031644323)
    ·
      refine ⟨66673554901285413047466485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44449036600856942031644323 66673554901285413047466485)
      ·
        refine ⟨6250645771995507473199983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 66673554901285413047466485 6250645771995507473199983)
        ·
          refine ⟨9375968657993261209799975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6250645771995507473199983 9375968657993261209799975)
          ·
            refine ⟨14063952986989891814699963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9375968657993261209799975 14063952986989891814699963)
            ·
              refine ⟨21095929480484837722049945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14063952986989891814699963 21095929480484837722049945)
              ·
                refine ⟨15821947110363628291537459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21095929480484837722049945 15821947110363628291537459)
                ·
                  refine ⟨23732920665545442437306189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15821947110363628291537459 23732920665545442437306189)
                  ·
                    refine ⟨8899845249579540913989821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23732920665545442437306189 8899845249579540913989821)
                    ·
                      refine ⟨3337441968592327842746183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8899845249579540913989821 3337441968592327842746183)
                      ·
                        rfl

theorem cell23_6499645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_6499645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6499645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6499645 prefixEnd_6499645 := by exact prefixLift 6499645
  have htrace : WordTrace (prefixWord ++ tailWord_6499645) baseStart_6499645 baseEnd_6499645 := by
    simpa [prefixWord, tailWord_6499645, baseEnd_6499645] using wordTrace_append hprefix tailTrace_6499645
  have hstable : (prefixWord ++ tailWord_6499645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6499645).length < 2 ^ (prefixWord ++ tailWord_6499645).sum := by decide
  have hdescent : baseEnd_6499645 < baseStart_6499645 := by decide
  rcases family_descends (prefixWord ++ tailWord_6499645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6499668 : List Nat := [2, 4, 1, 1, 2, 1, 1, 2, 3, 4, 2]
def baseStart_6499668 : Nat := 118140960795 + 6499668 * 2 ^ 59
def prefixEnd_6499668 : Nat := 4983230072969 + 3 ^ 40 * 6499668 * 2
def baseEnd_6499668 : Nat := 3337453778647381252758577

theorem tailTrace_6499668 : CollatzResearch.WordTrace tailWord_6499668 prefixEnd_6499668 3337453778647381252758577 := by
  unfold tailWord_6499668
  simp only [CollatzResearch.WordTrace]
  refine ⟨118531183708410182881761829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158041578277880243842349105 118531183708410182881761829)
  ·
    refine ⟨22224596945326909290330343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 118531183708410182881761829 22224596945326909290330343)
    ·
      refine ⟨33336895417990363935495515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22224596945326909290330343 33336895417990363935495515)
      ·
        refine ⟨50005343126985545903243273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33336895417990363935495515 50005343126985545903243273)
        ·
          refine ⟨37504007345239159427432455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50005343126985545903243273 37504007345239159427432455)
          ·
            refine ⟨56256011017858739141148683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37504007345239159427432455 56256011017858739141148683)
            ·
              refine ⟨84384016526788108711723025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56256011017858739141148683 84384016526788108711723025)
              ·
                refine ⟨63288012395091081533792269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84384016526788108711723025 63288012395091081533792269)
                ·
                  refine ⟨23733004648159155575172101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63288012395091081533792269 23733004648159155575172101)
                  ·
                    refine ⟨4449938371529841670344769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23733004648159155575172101 4449938371529841670344769)
                    ·
                      refine ⟨3337453778647381252758577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4449938371529841670344769 3337453778647381252758577)
                      ·
                        rfl

theorem cell23_6499668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 3, 4, 2].length) (baseStart_6499668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6499668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6499668 prefixEnd_6499668 := by exact prefixLift 6499668
  have htrace : WordTrace (prefixWord ++ tailWord_6499668) baseStart_6499668 baseEnd_6499668 := by
    simpa [prefixWord, tailWord_6499668, baseEnd_6499668] using wordTrace_append hprefix tailTrace_6499668
  have hstable : (prefixWord ++ tailWord_6499668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6499668).length < 2 ^ (prefixWord ++ tailWord_6499668).sum := by decide
  have hdescent : baseEnd_6499668 < baseStart_6499668 := by decide
  rcases family_descends (prefixWord ++ tailWord_6499668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6499671 : List Nat := [1, 1, 3, 2, 3, 2, 1, 1, 2, 4, 3]
def baseStart_6499671 : Nat := 118140960795 + 6499671 * 2 ^ 59
def prefixEnd_6499671 : Nat := 4983230072969 + 3 ^ 40 * 6499671 * 2
def baseEnd_6499671 : Nat := 3337455319089344741021063

theorem tailTrace_6499671 : CollatzResearch.WordTrace tailWord_6499671 prefixEnd_6499671 3337455319089344741021063 := by
  unfold tailWord_6499671
  simp only [CollatzResearch.WordTrace]
  refine ⟨237062476835809497275882867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158041651223872998183921911 237062476835809497275882867)
  ·
    refine ⟨355593715253714245913824301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237062476835809497275882867 355593715253714245913824301)
    ·
      refine ⟨133347643220142842217684113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 355593715253714245913824301 133347643220142842217684113)
      ·
        refine ⟨100010732415107131663263085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133347643220142842217684113 100010732415107131663263085)
        ·
          refine ⟨37504024655665174373723657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100010732415107131663263085 37504024655665174373723657)
          ·
            refine ⟨28128018491748880780292743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37504024655665174373723657 28128018491748880780292743)
            ·
              refine ⟨42192027737623321170439115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28128018491748880780292743 42192027737623321170439115)
              ·
                refine ⟨63288041606434981755658673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42192027737623321170439115 63288041606434981755658673)
                ·
                  refine ⟨47466031204826236316744005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63288041606434981755658673 47466031204826236316744005)
                  ·
                    refine ⟨8899880850904919309389501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47466031204826236316744005 8899880850904919309389501)
                    ·
                      refine ⟨3337455319089344741021063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8899880850904919309389501 3337455319089344741021063)
                      ·
                        rfl

theorem cell23_6499671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 1, 2, 4, 3].length) (baseStart_6499671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6499671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6499671 prefixEnd_6499671 := by exact prefixLift 6499671
  have htrace : WordTrace (prefixWord ++ tailWord_6499671) baseStart_6499671 baseEnd_6499671 := by
    simpa [prefixWord, tailWord_6499671, baseEnd_6499671] using wordTrace_append hprefix tailTrace_6499671
  have hstable : (prefixWord ++ tailWord_6499671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6499671).length < 2 ^ (prefixWord ++ tailWord_6499671).sum := by decide
  have hdescent : baseEnd_6499671 < baseStart_6499671 := by decide
  rcases family_descends (prefixWord ++ tailWord_6499671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6499685 : List Nat := [1, 3, 1, 3, 1, 2, 1, 5, 2, 2, 2]
def baseStart_6499685 : Nat := 118140960795 + 6499685 * 2 ^ 59
def prefixEnd_6499685 : Nat := 4983230072969 + 3 ^ 40 * 6499685 * 2
def baseEnd_6499685 : Nat := 3337462507818507686245999

theorem tailTrace_6499685 : CollatzResearch.WordTrace tailWord_6499685 prefixEnd_6499685 3337462507818507686245999 := by
  unfold tailWord_6499685
  simp only [CollatzResearch.WordTrace]
  refine ⟨237062987457758777666892509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158041991638505851777928339 237062987457758777666892509)
  ·
    refine ⟨88898620296659541625084691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 237062987457758777666892509 88898620296659541625084691)
    ·
      refine ⟨133347930444989312437627037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88898620296659541625084691 133347930444989312437627037)
      ·
        refine ⟨50005473916870992164110139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133347930444989312437627037 50005473916870992164110139)
        ·
          refine ⟨75008210875306488246165209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50005473916870992164110139 75008210875306488246165209)
          ·
            refine ⟨56256158156479866184623907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75008210875306488246165209 56256158156479866184623907)
            ·
              refine ⟨84384237234719799276935861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56256158156479866184623907 84384237234719799276935861)
              ·
                refine ⟨7911022240754981182212737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 84384237234719799276935861 7911022240754981182212737)
                ·
                  refine ⟨5933266680566235886659553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7911022240754981182212737 5933266680566235886659553)
                  ·
                    refine ⟨4449950010424676914994665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5933266680566235886659553 4449950010424676914994665)
                    ·
                      refine ⟨3337462507818507686245999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4449950010424676914994665 3337462507818507686245999)
                      ·
                        rfl

theorem cell23_6499685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 5, 2, 2, 2].length) (baseStart_6499685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6499685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6499685 prefixEnd_6499685 := by exact prefixLift 6499685
  have htrace : WordTrace (prefixWord ++ tailWord_6499685) baseStart_6499685 baseEnd_6499685 := by
    simpa [prefixWord, tailWord_6499685, baseEnd_6499685] using wordTrace_append hprefix tailTrace_6499685
  have hstable : (prefixWord ++ tailWord_6499685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6499685).length < 2 ^ (prefixWord ++ tailWord_6499685).sum := by decide
  have hdescent : baseEnd_6499685 < baseStart_6499685 := by decide
  rcases family_descends (prefixWord ++ tailWord_6499685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6499708 : List Nat := [2, 2, 2, 1, 1, 1, 6, 3, 5]
def baseStart_6499708 : Nat := 118140960795 + 6499708 * 2 ^ 59
def prefixEnd_6499708 : Nat := 4983230072969 + 3 ^ 40 * 6499708 * 2
def baseEnd_6499708 : Nat := 370830479763729010695377

theorem tailTrace_6499708 : CollatzResearch.WordTrace tailWord_6499708 prefixEnd_6499708 370830479763729010695377 := by
  unfold tailWord_6499708
  simp only [CollatzResearch.WordTrace]
  refine ⟨118531913168337726297489889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158042550891116968396653185 118531913168337726297489889)
  ·
    refine ⟨88898934876253294723117417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118531913168337726297489889 88898934876253294723117417)
    ·
      refine ⟨66674201157189971042338063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88898934876253294723117417 66674201157189971042338063)
      ·
        refine ⟨100011301735784956563507095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66674201157189971042338063 100011301735784956563507095)
        ·
          refine ⟨150016952603677434845260643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100011301735784956563507095 150016952603677434845260643)
          ·
            refine ⟨225025428905516152267890965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150016952603677434845260643 225025428905516152267890965)
            ·
              refine ⟨10548066979946069637557389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 225025428905516152267890965 10548066979946069637557389)
              ·
                refine ⟨3955525117479776114084021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10548066979946069637557389 3955525117479776114084021)
                ·
                  refine ⟨370830479763729010695377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3955525117479776114084021 370830479763729010695377)
                  ·
                    rfl

theorem cell23_6499708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 6, 3, 5].length) (baseStart_6499708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6499708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6499708 prefixEnd_6499708 := by exact prefixLift 6499708
  have htrace : WordTrace (prefixWord ++ tailWord_6499708) baseStart_6499708 baseEnd_6499708 := by
    simpa [prefixWord, tailWord_6499708, baseEnd_6499708] using wordTrace_append hprefix tailTrace_6499708
  have hstable : (prefixWord ++ tailWord_6499708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6499708).length < 2 ^ (prefixWord ++ tailWord_6499708).sum := by decide
  have hdescent : baseEnd_6499708 < baseStart_6499708 := by decide
  rcases family_descends (prefixWord ++ tailWord_6499708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6499751 : List Nat := [1, 1, 6, 1, 1, 1, 1, 1, 2, 8]
def baseStart_6499751 : Nat := 118140960795 + 6499751 * 2 ^ 59
def prefixEnd_6499751 : Nat := 4983230072969 + 3 ^ 40 * 6499751 * 2
def baseEnd_6499751 : Nat := 1112498799180568142673565

theorem tailTrace_6499751 : CollatzResearch.WordTrace tailWord_6499751 prefixEnd_6499751 1112498799180568142673565 := by
  unfold tailWord_6499751
  simp only [CollatzResearch.WordTrace]
  refine ⟨237065394675519670938795107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158043596450346447292530071 237065394675519670938795107)
  ·
    refine ⟨355598092013279506408192661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237065394675519670938795107 355598092013279506408192661)
    ·
      refine ⟨16668660563122476862884031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 355598092013279506408192661 16668660563122476862884031)
      ·
        refine ⟨25002990844683715294326047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16668660563122476862884031 25002990844683715294326047)
        ·
          refine ⟨37504486267025572941489071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25002990844683715294326047 37504486267025572941489071)
          ·
            refine ⟨56256729400538359412233607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37504486267025572941489071 56256729400538359412233607)
            ·
              refine ⟨84385094100807539118350411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56256729400538359412233607 84385094100807539118350411)
              ·
                refine ⟨126577641151211308677525617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84385094100807539118350411 126577641151211308677525617)
                ·
                  refine ⟨94933230863408481508144213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 126577641151211308677525617 94933230863408481508144213)
                  ·
                    refine ⟨1112498799180568142673565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 94933230863408481508144213 1112498799180568142673565)
                    ·
                      rfl

theorem cell23_6499751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 1, 2, 8].length) (baseStart_6499751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6499751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6499751 prefixEnd_6499751 := by exact prefixLift 6499751
  have htrace : WordTrace (prefixWord ++ tailWord_6499751) baseStart_6499751 baseEnd_6499751 := by
    simpa [prefixWord, tailWord_6499751, baseEnd_6499751] using wordTrace_append hprefix tailTrace_6499751
  have hstable : (prefixWord ++ tailWord_6499751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6499751).length < 2 ^ (prefixWord ++ tailWord_6499751).sum := by decide
  have hdescent : baseEnd_6499751 < baseStart_6499751 := by decide
  rcases family_descends (prefixWord ++ tailWord_6499751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6499848 : List Nat := [2, 1, 3, 2, 1, 1, 3, 2, 3, 1, 4]
def baseStart_6499848 : Nat := 118140960795 + 6499848 * 2 ^ 59
def prefixEnd_6499848 : Nat := 4983230072969 + 3 ^ 40 * 6499848 * 2
def baseEnd_6499848 : Nat := 3337546205165190548507749

theorem tailTrace_6499848 : CollatzResearch.WordTrace tailWord_6499848 prefixEnd_6499848 3337546205165190548507749 := by
  unfold tailWord_6499848
  simp only [CollatzResearch.WordTrace]
  refine ⟨118534466278084128252538099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158045955037445504336717465 118534466278084128252538099)
  ·
    refine ⟨177801699417126192378807149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118534466278084128252538099 177801699417126192378807149)
    ·
      refine ⟨66675637281422322142052681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177801699417126192378807149 66675637281422322142052681)
      ·
        refine ⟨50006727961066741606539511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66675637281422322142052681 50006727961066741606539511)
        ·
          refine ⟨75010091941600112409809267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50006727961066741606539511 75010091941600112409809267)
          ·
            refine ⟨112515137912400168614713901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75010091941600112409809267 112515137912400168614713901)
            ·
              refine ⟨42193176717150063230517713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112515137912400168614713901 42193176717150063230517713)
              ·
                refine ⟨31644882537862547422888285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42193176717150063230517713 31644882537862547422888285)
                ·
                  refine ⟨11866830951698455283583107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31644882537862547422888285 11866830951698455283583107)
                  ·
                    refine ⟨17800246427547682925374661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11866830951698455283583107 17800246427547682925374661)
                    ·
                      refine ⟨3337546205165190548507749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17800246427547682925374661 3337546205165190548507749)
                      ·
                        rfl

theorem cell23_6499848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 2, 3, 1, 4].length) (baseStart_6499848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6499848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6499848 prefixEnd_6499848 := by exact prefixLift 6499848
  have htrace : WordTrace (prefixWord ++ tailWord_6499848) baseStart_6499848 baseEnd_6499848 := by
    simpa [prefixWord, tailWord_6499848, baseEnd_6499848] using wordTrace_append hprefix tailTrace_6499848
  have hstable : (prefixWord ++ tailWord_6499848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6499848).length < 2 ^ (prefixWord ++ tailWord_6499848).sum := by decide
  have hdescent : baseEnd_6499848 < baseStart_6499848 := by decide
  rcases family_descends (prefixWord ++ tailWord_6499848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6499871 : List Nat := [1, 1, 2, 4, 1, 1, 2, 11]
def baseStart_6499871 : Nat := 118140960795 + 6499871 * 2 ^ 59
def prefixEnd_6499871 : Nat := 4983230072969 + 3 ^ 40 * 6499871 * 2
def baseEnd_6499871 : Nat := 123613259822971998463709

theorem tailTrace_6499871 : CollatzResearch.WordTrace tailWord_6499871 prefixEnd_6499871 123613259822971998463709 := by
  unfold tailWord_6499871
  simp only [CollatzResearch.WordTrace]
  refine ⟨237069771435084931433163467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158046514290056620955442311 237069771435084931433163467)
  ·
    refine ⟨355604657152627397149745201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237069771435084931433163467 355604657152627397149745201)
    ·
      refine ⟨266703492864470547862308901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 355604657152627397149745201 266703492864470547862308901)
      ·
        refine ⟨50006904912088227724182919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 266703492864470547862308901 50006904912088227724182919)
        ·
          refine ⟨75010357368132341586274379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50006904912088227724182919 75010357368132341586274379)
          ·
            refine ⟨112515536052198512379411569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75010357368132341586274379 112515536052198512379411569)
            ·
              refine ⟨84386652039148884284558677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112515536052198512379411569 84386652039148884284558677)
              ·
                refine ⟨123613259822971998463709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 84386652039148884284558677 123613259822971998463709)
                ·
                  rfl

theorem cell23_6499871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 11].length) (baseStart_6499871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6499871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6499871 prefixEnd_6499871 := by exact prefixLift 6499871
  have htrace : WordTrace (prefixWord ++ tailWord_6499871) baseStart_6499871 baseEnd_6499871 := by
    simpa [prefixWord, tailWord_6499871, baseEnd_6499871] using wordTrace_append hprefix tailTrace_6499871
  have hstable : (prefixWord ++ tailWord_6499871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6499871).length < 2 ^ (prefixWord ++ tailWord_6499871).sum := by decide
  have hdescent : baseEnd_6499871 < baseStart_6499871 := by decide
  rcases family_descends (prefixWord ++ tailWord_6499871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6499882 : List Nat := [3, 1, 4, 1, 1, 1, 1, 2, 5, 2, 2]
def baseStart_6499882 : Nat := 118140960795 + 6499882 * 2 ^ 59
def prefixEnd_6499882 : Nat := 4983230072969 + 3 ^ 40 * 6499882 * 2
def baseEnd_6499882 : Nat := 3337563663507443415482593

theorem tailTrace_6499882 : CollatzResearch.WordTrace tailWord_6499882 prefixEnd_6499882 3337563663507443415482593 := by
  unfold tailWord_6499882
  simp only [CollatzResearch.WordTrace]
  refine ⟨59267543159511270077953475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158046781758696720207875933 59267543159511270077953475)
  ·
    refine ⟨88901314739266905116930213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59267543159511270077953475 88901314739266905116930213)
    ·
      refine ⟨16668996513612544709424415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88901314739266905116930213 16668996513612544709424415)
      ·
        refine ⟨25003494770418817064136623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16668996513612544709424415 25003494770418817064136623)
        ·
          refine ⟨37505242155628225596204935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25003494770418817064136623 37505242155628225596204935)
          ·
            refine ⟨56257863233442338394307403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37505242155628225596204935 56257863233442338394307403)
            ·
              refine ⟨84386794850163507591461105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56257863233442338394307403 84386794850163507591461105)
              ·
                refine ⟨63290096137622630693595829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84386794850163507591461105 63290096137622630693595829)
                ·
                  refine ⟨5933446512902121627524609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 63290096137622630693595829 5933446512902121627524609)
                  ·
                    refine ⟨4450084884676591220643457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5933446512902121627524609 4450084884676591220643457)
                    ·
                      refine ⟨3337563663507443415482593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4450084884676591220643457 3337563663507443415482593)
                      ·
                        rfl

theorem cell23_6499882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 2, 5, 2, 2].length) (baseStart_6499882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6499882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6499882 prefixEnd_6499882 := by exact prefixLift 6499882
  have htrace : WordTrace (prefixWord ++ tailWord_6499882) baseStart_6499882 baseEnd_6499882 := by
    simpa [prefixWord, tailWord_6499882, baseEnd_6499882] using wordTrace_append hprefix tailTrace_6499882
  have hstable : (prefixWord ++ tailWord_6499882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6499882).length < 2 ^ (prefixWord ++ tailWord_6499882).sum := by decide
  have hdescent : baseEnd_6499882 < baseStart_6499882 := by decide
  rcases family_descends (prefixWord ++ tailWord_6499882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6499932 : List Nat := [2, 2, 4, 1, 2, 1, 1, 2, 4, 1, 3]
def baseStart_6499932 : Nat := 118140960795 + 6499932 * 2 ^ 59
def prefixEnd_6499932 : Nat := 4983230072969 + 3 ^ 40 * 6499932 * 2
def baseEnd_6499932 : Nat := 3337589337540168219857363

theorem tailTrace_6499932 : CollatzResearch.WordTrace tailWord_6499932 prefixEnd_6499932 3337589337540168219857363 := by
  unfold tailWord_6499932
  simp only [CollatzResearch.WordTrace]
  refine ⟨118535998143931969425567025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158047997525242625900756033 118535998143931969425567025)
  ·
    refine ⟨88901998607948977069175269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118535998143931969425567025 88901998607948977069175269)
    ·
      refine ⟨16669124738990433200470363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88901998607948977069175269 16669124738990433200470363)
      ·
        refine ⟨25003687108485649800705545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16669124738990433200470363 25003687108485649800705545)
        ·
          refine ⟨18752765331364237350529159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25003687108485649800705545 18752765331364237350529159)
          ·
            refine ⟨28129147997046356025793739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18752765331364237350529159 28129147997046356025793739)
            ·
              refine ⟨42193721995569534038690609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28129147997046356025793739 42193721995569534038690609)
              ·
                refine ⟨31645291496677150529017957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42193721995569534038690609 31645291496677150529017957)
                ·
                  refine ⟨5933492155626965724190867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31645291496677150529017957 5933492155626965724190867)
                  ·
                    refine ⟨8900238233440448586286301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5933492155626965724190867 8900238233440448586286301)
                    ·
                      refine ⟨3337589337540168219857363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8900238233440448586286301 3337589337540168219857363)
                      ·
                        rfl

theorem cell23_6499932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 2, 4, 1, 3].length) (baseStart_6499932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6499932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6499932 prefixEnd_6499932 := by exact prefixLift 6499932
  have htrace : WordTrace (prefixWord ++ tailWord_6499932) baseStart_6499932 baseEnd_6499932 := by
    simpa [prefixWord, tailWord_6499932, baseEnd_6499932] using wordTrace_append hprefix tailTrace_6499932
  have hstable : (prefixWord ++ tailWord_6499932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6499932).length < 2 ^ (prefixWord ++ tailWord_6499932).sum := by decide
  have hdescent : baseEnd_6499932 < baseStart_6499932 := by decide
  rcases family_descends (prefixWord ++ tailWord_6499932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6499968 : List Nat := [2, 1, 1, 2, 1, 4, 2, 1, 1, 4, 4]
def baseStart_6499968 : Nat := 118140960795 + 6499968 * 2 ^ 59
def prefixEnd_6499968 : Nat := 4983230072969 + 3 ^ 40 * 6499968 * 2
def baseEnd_6499968 : Nat := 3337607822843730079007197

theorem tailTrace_6499968 : CollatzResearch.WordTrace tailWord_6499968 prefixEnd_6499968 3337607822843730079007197 := by
  unfold tailWord_6499968
  simp only [CollatzResearch.WordTrace]
  refine ⟨118536654657866758499722279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158048872877155677999629705 118536654657866758499722279)
  ·
    refine ⟨177804981986800137749583419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118536654657866758499722279 177804981986800137749583419)
    ·
      refine ⟨266707472980200206624375129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177804981986800137749583419 266707472980200206624375129)
      ·
        refine ⟨200030604735150154968281347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 266707472980200206624375129 200030604735150154968281347)
        ·
          refine ⟨300045907102725232452422021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200030604735150154968281347 300045907102725232452422021)
          ·
            refine ⟨56258607581760981084829129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 300045907102725232452422021 56258607581760981084829129)
            ·
              refine ⟨42193955686320735813621847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56258607581760981084829129 42193955686320735813621847)
              ·
                refine ⟨63290933529481103720432771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42193955686320735813621847 63290933529481103720432771)
                ·
                  refine ⟨94936400294221655580649157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63290933529481103720432771 94936400294221655580649157)
                  ·
                    refine ⟨17800575055166560421371717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 94936400294221655580649157 17800575055166560421371717)
                    ·
                      refine ⟨3337607822843730079007197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17800575055166560421371717 3337607822843730079007197)
                      ·
                        rfl

theorem cell23_6499968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 1, 1, 4, 4].length) (baseStart_6499968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6499968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6499968 prefixEnd_6499968 := by exact prefixLift 6499968
  have htrace : WordTrace (prefixWord ++ tailWord_6499968) baseStart_6499968 baseEnd_6499968 := by
    simpa [prefixWord, tailWord_6499968, baseEnd_6499968] using wordTrace_append hprefix tailTrace_6499968
  have hstable : (prefixWord ++ tailWord_6499968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6499968).length < 2 ^ (prefixWord ++ tailWord_6499968).sum := by decide
  have hdescent : baseEnd_6499968 < baseStart_6499968 := by decide
  rcases family_descends (prefixWord ++ tailWord_6499968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6500015 : List Nat := [1, 1, 2, 1, 2, 4, 1, 1, 1, 7, 2]
def baseStart_6500015 : Nat := 118140960795 + 6500015 * 2 ^ 59
def prefixEnd_6500015 : Nat := 4983230072969 + 3 ^ 40 * 6500015 * 2
def baseEnd_6500015 : Nat := 3337631956434491395119481

theorem tailTrace_6500015 : CollatzResearch.WordTrace tailWord_6500015 prefixEnd_6500015 3337631956434491395119481 := by
  unfold tailWord_6500015
  simp only [CollatzResearch.WordTrace]
  refine ⟨237075023546563244026405499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158050015697708829350936999 237075023546563244026405499)
  ·
    refine ⟨355612535319844866039608249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237075023546563244026405499 355612535319844866039608249)
    ·
      refine ⟨266709401489883649529706187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 355612535319844866039608249 266709401489883649529706187)
      ·
        refine ⟨400064102234825474294559281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266709401489883649529706187 400064102234825474294559281)
        ·
          refine ⟨300048076676119105720919461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 400064102234825474294559281 300048076676119105720919461)
          ·
            refine ⟨56259014376772332322672399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 300048076676119105720919461 56259014376772332322672399)
            ·
              refine ⟨84388521565158498484008599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56259014376772332322672399 84388521565158498484008599)
              ·
                refine ⟨126582782347737747726012899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84388521565158498484008599 126582782347737747726012899)
                ·
                  refine ⟨189874173521606621589019349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 126582782347737747726012899 189874173521606621589019349)
                  ·
                    refine ⟨4450175941912655193492641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 189874173521606621589019349 4450175941912655193492641)
                    ·
                      refine ⟨3337631956434491395119481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4450175941912655193492641 3337631956434491395119481)
                      ·
                        rfl

theorem cell23_6500015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 1, 1, 7, 2].length) (baseStart_6500015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6500015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6500015 prefixEnd_6500015 := by exact prefixLift 6500015
  have htrace : WordTrace (prefixWord ++ tailWord_6500015) baseStart_6500015 baseEnd_6500015 := by
    simpa [prefixWord, tailWord_6500015, baseEnd_6500015] using wordTrace_append hprefix tailTrace_6500015
  have hstable : (prefixWord ++ tailWord_6500015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6500015).length < 2 ^ (prefixWord ++ tailWord_6500015).sum := by decide
  have hdescent : baseEnd_6500015 < baseStart_6500015 := by decide
  rcases family_descends (prefixWord ++ tailWord_6500015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6500048 : List Nat := [2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 5]
def baseStart_6500048 : Nat := 118140960795 + 6500048 * 2 ^ 59
def prefixEnd_6500048 : Nat := 4983230072969 + 3 ^ 40 * 6500048 * 2
def baseEnd_6500048 : Nat := 3337648901296089766006829

theorem tailTrace_6500048 : CollatzResearch.WordTrace tailWord_6500048 prefixEnd_6500048 3337648901296089766006829 := by
  unfold tailWord_6500048
  simp only [CollatzResearch.WordTrace]
  refine ⟨118538113577721845331178399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158050818103629127108237865 118538113577721845331178399)
  ·
    refine ⟨177807170366582767996767599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118538113577721845331178399 177807170366582767996767599)
    ·
      refine ⟨266710755549874151995151399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177807170366582767996767599 266710755549874151995151399)
      ·
        refine ⟨400066133324811227992727099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266710755549874151995151399 400066133324811227992727099)
        ·
          refine ⟨600099199987216841989090649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 400066133324811227992727099 600099199987216841989090649)
          ·
            refine ⟨450074399990412631491817987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 600099199987216841989090649 450074399990412631491817987)
            ·
              refine ⟨675111599985618947237726981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 450074399990412631491817987 675111599985618947237726981)
              ·
                refine ⟨126583424997303552607073809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 675111599985618947237726981 126583424997303552607073809)
                ·
                  refine ⟨94937568747977664455305357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 126583424997303552607073809 94937568747977664455305357)
                  ·
                    refine ⟨35601588280491624170739509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 94937568747977664455305357 35601588280491624170739509)
                    ·
                      refine ⟨3337648901296089766006829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35601588280491624170739509 3337648901296089766006829)
                      ·
                        rfl

theorem cell23_6500048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 5].length) (baseStart_6500048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6500048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6500048 prefixEnd_6500048 := by exact prefixLift 6500048
  have htrace : WordTrace (prefixWord ++ tailWord_6500048) baseStart_6500048 baseEnd_6500048 := by
    simpa [prefixWord, tailWord_6500048, baseEnd_6500048] using wordTrace_append hprefix tailTrace_6500048
  have hstable : (prefixWord ++ tailWord_6500048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6500048).length < 2 ^ (prefixWord ++ tailWord_6500048).sum := by decide
  have hdescent : baseEnd_6500048 < baseStart_6500048 := by decide
  rcases family_descends (prefixWord ++ tailWord_6500048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6500055 : List Nat := [1, 1, 3, 2, 1, 3, 1, 2, 5, 4]
def baseStart_6500055 : Nat := 118140960795 + 6500055 * 2 ^ 59
def prefixEnd_6500055 : Nat := 4983230072969 + 3 ^ 40 * 6500055 * 2
def baseEnd_6500055 : Nat := 1112550831886890412873099

theorem tailTrace_6500055 : CollatzResearch.WordTrace tailWord_6500055 prefixEnd_6500055 1112550831886890412873099 := by
  unfold tailWord_6500055
  simp only [CollatzResearch.WordTrace]
  refine ⟨237076482466418330857861619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158050988310945553905241079 237076482466418330857861619)
  ·
    refine ⟨355614723699627496286792429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237076482466418330857861619 355614723699627496286792429)
    ·
      refine ⟨133355521387360311107547161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 355614723699627496286792429 133355521387360311107547161)
      ·
        refine ⟨100016641040520233330660371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133355521387360311107547161 100016641040520233330660371)
        ·
          refine ⟨150024961560780349995990557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100016641040520233330660371 150024961560780349995990557)
          ·
            refine ⟨56259360585292631248496459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 150024961560780349995990557 56259360585292631248496459)
            ·
              refine ⟨84389040877938946872744689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56259360585292631248496459 84389040877938946872744689)
              ·
                refine ⟨63291780658454210154558517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84389040877938946872744689 63291780658454210154558517)
                ·
                  refine ⟨5933604436730082201989861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 63291780658454210154558517 5933604436730082201989861)
                  ·
                    refine ⟨1112550831886890412873099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5933604436730082201989861 1112550831886890412873099)
                    ·
                      rfl

theorem cell23_6500055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 2, 5, 4].length) (baseStart_6500055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6500055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6500055 prefixEnd_6500055 := by exact prefixLift 6500055
  have htrace : WordTrace (prefixWord ++ tailWord_6500055) baseStart_6500055 baseEnd_6500055 := by
    simpa [prefixWord, tailWord_6500055, baseEnd_6500055] using wordTrace_append hprefix tailTrace_6500055
  have hstable : (prefixWord ++ tailWord_6500055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6500055).length < 2 ^ (prefixWord ++ tailWord_6500055).sum := by decide
  have hdescent : baseEnd_6500055 < baseStart_6500055 := by decide
  rcases family_descends (prefixWord ++ tailWord_6500055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6500072 : List Nat := [2, 1, 4, 1, 3, 1, 1, 3, 3, 4]
def baseStart_6500072 : Nat := 118140960795 + 6500072 * 2 ^ 59
def prefixEnd_6500072 : Nat := 4983230072969 + 3 ^ 40 * 6500072 * 2
def baseEnd_6500072 : Nat := 1112553741610599224035573

theorem tailTrace_6500072 : CollatzResearch.WordTrace tailWord_6500072 prefixEnd_6500072 1112553741610599224035573 := by
  unfold tailWord_6500072
  simp only [CollatzResearch.WordTrace]
  refine ⟨118538551253678371380615235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158051401671571161840820313 118538551253678371380615235)
  ·
    refine ⟨177807826880517557070922853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118538551253678371380615235 177807826880517557070922853)
    ·
      refine ⟨33338967540097041950798035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 177807826880517557070922853 33338967540097041950798035)
      ·
        refine ⟨50008451310145562926197053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33338967540097041950798035 50008451310145562926197053)
        ·
          refine ⟨18753169241304586097323895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50008451310145562926197053 18753169241304586097323895)
          ·
            refine ⟨28129753861956879145985843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18753169241304586097323895 28129753861956879145985843)
            ·
              refine ⟨42194630792935318718978765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28129753861956879145985843 42194630792935318718978765)
              ·
                refine ⟨15822986547350744519617037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42194630792935318718978765 15822986547350744519617037)
                ·
                  refine ⟨5933619955256529194856389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15822986547350744519617037 5933619955256529194856389)
                  ·
                    refine ⟨1112553741610599224035573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5933619955256529194856389 1112553741610599224035573)
                    ·
                      rfl

theorem cell23_6500072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 3, 3, 4].length) (baseStart_6500072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6500072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6500072 prefixEnd_6500072 := by exact prefixLift 6500072
  have htrace : WordTrace (prefixWord ++ tailWord_6500072) baseStart_6500072 baseEnd_6500072 := by
    simpa [prefixWord, tailWord_6500072, baseEnd_6500072] using wordTrace_append hprefix tailTrace_6500072
  have hstable : (prefixWord ++ tailWord_6500072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6500072).length < 2 ^ (prefixWord ++ tailWord_6500072).sum := by decide
  have hdescent : baseEnd_6500072 < baseStart_6500072 := by decide
  rcases family_descends (prefixWord ++ tailWord_6500072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6500106 : List Nat := [3, 1, 2, 2, 1, 5, 1, 3, 1, 4]
def baseStart_6500106 : Nat := 118140960795 + 6500106 * 2 ^ 59
def prefixEnd_6500106 : Nat := 4983230072969 + 3 ^ 40 * 6500106 * 2
def baseEnd_6500106 : Nat := 1112559561058016846360521

theorem tailTrace_6500106 : CollatzResearch.WordTrace tailWord_6500106 prefixEnd_6500106 1112559561058016846360521 := by
  unfold tailWord_6500106
  simp only [CollatzResearch.WordTrace]
  refine ⟨59269585647308391641992043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158052228392822377711978781 59269585647308391641992043)
  ·
    refine ⟨88904378470962587462988065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59269585647308391641992043 88904378470962587462988065)
    ·
      refine ⟨66678283853221940597241049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88904378470962587462988065 66678283853221940597241049)
      ·
        refine ⟨50008712889916455447930787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66678283853221940597241049 50008712889916455447930787)
        ·
          refine ⟨75013069334874683171896181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50008712889916455447930787 75013069334874683171896181)
          ·
            refine ⟨7032475250144501547365267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 75013069334874683171896181 7032475250144501547365267)
            ·
              refine ⟨10548712875216752321047901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7032475250144501547365267 10548712875216752321047901)
              ·
                refine ⟨3955767328206282120392963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10548712875216752321047901 3955767328206282120392963)
                ·
                  refine ⟨5933650992309423180589445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3955767328206282120392963 5933650992309423180589445)
                  ·
                    refine ⟨1112559561058016846360521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5933650992309423180589445 1112559561058016846360521)
                    ·
                      rfl

theorem cell23_6500106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 1, 3, 1, 4].length) (baseStart_6500106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6500106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6500106 prefixEnd_6500106 := by exact prefixLift 6500106
  have htrace : WordTrace (prefixWord ++ tailWord_6500106) baseStart_6500106 baseEnd_6500106 := by
    simpa [prefixWord, tailWord_6500106, baseEnd_6500106] using wordTrace_append hprefix tailTrace_6500106
  have hstable : (prefixWord ++ tailWord_6500106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6500106).length < 2 ^ (prefixWord ++ tailWord_6500106).sum := by decide
  have hdescent : baseEnd_6500106 < baseStart_6500106 := by decide
  rcases family_descends (prefixWord ++ tailWord_6500106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6500129 : List Nat := [1, 2, 3, 2, 1, 3, 3, 1, 3, 1, 3]
def baseStart_6500129 : Nat := 118140960795 + 6500129 * 2 ^ 59
def prefixEnd_6500129 : Nat := 4983230072969 + 3 ^ 40 * 6500129 * 2
def baseEnd_6500129 : Nat := 3337690493229103949093957

theorem tailTrace_6500129 : CollatzResearch.WordTrace tailWord_6500129 prefixEnd_6500129 3337690493229103949093957 := by
  unfold tailWord_6500129
  simp only [CollatzResearch.WordTrace]
  refine ⟨237079181468150241496055441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158052787645433494330703627 237079181468150241496055441)
  ·
    refine ⟨177809386101112681122041581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237079181468150241496055441 177809386101112681122041581)
    ·
      refine ⟨66678519787917255420765593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177809386101112681122041581 66678519787917255420765593)
      ·
        refine ⟨50008889840937941565574195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66678519787917255420765593 50008889840937941565574195)
        ·
          refine ⟨75013334761406912348361293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50008889840937941565574195 75013334761406912348361293)
          ·
            refine ⟨28130000535527592130635485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75013334761406912348361293 28130000535527592130635485)
            ·
              refine ⟨10548750200822847048988307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28130000535527592130635485 10548750200822847048988307)
              ·
                refine ⟨15823125301234270573482461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10548750200822847048988307 15823125301234270573482461)
                ·
                  refine ⟨5933671987962851465055923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15823125301234270573482461 5933671987962851465055923)
                  ·
                    refine ⟨8900507981944277197583885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5933671987962851465055923 8900507981944277197583885)
                    ·
                      refine ⟨3337690493229103949093957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8900507981944277197583885 3337690493229103949093957)
                      ·
                        rfl

theorem cell23_6500129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 3, 1, 3, 1, 3].length) (baseStart_6500129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6500129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6500129 prefixEnd_6500129 := by exact prefixLift 6500129
  have htrace : WordTrace (prefixWord ++ tailWord_6500129) baseStart_6500129 baseEnd_6500129 := by
    simpa [prefixWord, tailWord_6500129, baseEnd_6500129] using wordTrace_append hprefix tailTrace_6500129
  have hstable : (prefixWord ++ tailWord_6500129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6500129).length < 2 ^ (prefixWord ++ tailWord_6500129).sum := by decide
  have hdescent : baseEnd_6500129 < baseStart_6500129 := by decide
  rcases family_descends (prefixWord ++ tailWord_6500129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6500152 : List Nat := [2, 1, 2, 1, 3, 4, 1, 1, 3, 1, 4]
def baseStart_6500152 : Nat := 118140960795 + 6500152 * 2 ^ 59
def prefixEnd_6500152 : Nat := 4983230072969 + 3 ^ 40 * 6500152 * 2
def baseEnd_6500152 : Nat := 3337702303284157359106351

theorem tailTrace_6500152 : CollatzResearch.WordTrace tailWord_6500152 prefixEnd_6500152 3337702303284157359106351 := by
  unfold tailWord_6500152
  simp only [CollatzResearch.WordTrace]
  refine ⟨118540010173533458212071355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158053346898044610949428473 118540010173533458212071355)
  ·
    refine ⟨177810015260300187318107033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118540010173533458212071355 177810015260300187318107033)
    ·
      refine ⟨133357511445225140488580275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177810015260300187318107033 133357511445225140488580275)
      ·
        refine ⟨200036267167837710732870413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133357511445225140488580275 200036267167837710732870413)
        ·
          refine ⟨75013600187939141524826405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 200036267167837710732870413 75013600187939141524826405)
          ·
            refine ⟨14065050035238589035904951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75013600187939141524826405 14065050035238589035904951)
            ·
              refine ⟨21097575052857883553857427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14065050035238589035904951 21097575052857883553857427)
              ·
                refine ⟨31646362579286825330786141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21097575052857883553857427 31646362579286825330786141)
                ·
                  refine ⟨11867385967232559499044803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31646362579286825330786141 11867385967232559499044803)
                  ·
                    refine ⟨17801078950848839248567205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11867385967232559499044803 17801078950848839248567205)
                    ·
                      refine ⟨3337702303284157359106351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17801078950848839248567205 3337702303284157359106351)
                      ·
                        rfl

theorem cell23_6500152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 1, 3, 1, 4].length) (baseStart_6500152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6500152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6500152 prefixEnd_6500152 := by exact prefixLift 6500152
  have htrace : WordTrace (prefixWord ++ tailWord_6500152) baseStart_6500152 baseEnd_6500152 := by
    simpa [prefixWord, tailWord_6500152, baseEnd_6500152] using wordTrace_append hprefix tailTrace_6500152
  have hstable : (prefixWord ++ tailWord_6500152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6500152).length < 2 ^ (prefixWord ++ tailWord_6500152).sum := by decide
  have hdescent : baseEnd_6500152 < baseStart_6500152 := by decide
  rcases family_descends (prefixWord ++ tailWord_6500152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6500169 : List Nat := [1, 2, 1, 1, 2, 4, 5, 1, 1, 1, 4]
def baseStart_6500169 : Nat := 118140960795 + 6500169 * 2 ^ 59
def prefixEnd_6500169 : Nat := 4983230072969 + 3 ^ 40 * 6500169 * 2
def baseEnd_6500169 : Nat := 3337711032455283792593773

theorem tailTrace_6500169 : CollatzResearch.WordTrace tailWord_6500169 prefixEnd_6500169 3337711032455283792593773 := by
  unfold tailWord_6500169
  simp only [CollatzResearch.WordTrace]
  refine ⟨237080640388005328327511561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158053760258670218885007707 237080640388005328327511561)
  ·
    refine ⟨177810480291003996245633671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237080640388005328327511561 177810480291003996245633671)
    ·
      refine ⟨266715720436505994368450507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177810480291003996245633671 266715720436505994368450507)
      ·
        refine ⟨400073580654758991552675761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266715720436505994368450507 400073580654758991552675761)
        ·
          refine ⟨300055185491069243664506821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 400073580654758991552675761 300055185491069243664506821)
          ·
            refine ⟨56260347279575483187095029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 300055185491069243664506821 56260347279575483187095029)
            ·
              refine ⟨5274407557460201548790159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56260347279575483187095029 5274407557460201548790159)
              ·
                refine ⟨7911611336190302323185239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5274407557460201548790159 7911611336190302323185239)
                ·
                  refine ⟨11867417004285453484777859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7911611336190302323185239 11867417004285453484777859)
                  ·
                    refine ⟨17801125506428180227166789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11867417004285453484777859 17801125506428180227166789)
                    ·
                      refine ⟨3337711032455283792593773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17801125506428180227166789 3337711032455283792593773)
                      ·
                        rfl

theorem cell23_6500169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 5, 1, 1, 1, 4].length) (baseStart_6500169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6500169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6500169 prefixEnd_6500169 := by exact prefixLift 6500169
  have htrace : WordTrace (prefixWord ++ tailWord_6500169) baseStart_6500169 baseEnd_6500169 := by
    simpa [prefixWord, tailWord_6500169, baseEnd_6500169] using wordTrace_append hprefix tailTrace_6500169
  have hstable : (prefixWord ++ tailWord_6500169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6500169).length < 2 ^ (prefixWord ++ tailWord_6500169).sum := by decide
  have hdescent : baseEnd_6500169 < baseStart_6500169 := by decide
  rcases family_descends (prefixWord ++ tailWord_6500169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6500180 : List Nat := [2, 4, 1, 1, 3, 3, 2, 2, 1, 1, 3]
def baseStart_6500180 : Nat := 118140960795 + 6500180 * 2 ^ 59
def prefixEnd_6500180 : Nat := 4983230072969 + 3 ^ 40 * 6500180 * 2
def baseEnd_6500180 : Nat := 3337716680742483249556223

theorem tailTrace_6500180 : CollatzResearch.WordTrace tailWord_6500180 prefixEnd_6500180 3337716680742483249556223 := by
  unfold tailWord_6500180
  simp only [CollatzResearch.WordTrace]
  refine ⟨118540520795482738603080997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158054027727310318137441329 118540520795482738603080997)
  ·
    refine ⟨22226347649153013488077687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 118540520795482738603080997 22226347649153013488077687)
    ·
      refine ⟨33339521473729520232116531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22226347649153013488077687 33339521473729520232116531)
      ·
        refine ⟨50009282210594280348174797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33339521473729520232116531 50009282210594280348174797)
        ·
          refine ⟨18753480828972855130565549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50009282210594280348174797 18753480828972855130565549)
          ·
            refine ⟨7032555310864820673962081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18753480828972855130565549 7032555310864820673962081)
            ·
              refine ⟨5274416483148615505471561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7032555310864820673962081 5274416483148615505471561)
              ·
                refine ⟨3955812362361461629103671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5274416483148615505471561 3955812362361461629103671)
                ·
                  refine ⟨5933718543542192443655507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3955812362361461629103671 5933718543542192443655507)
                  ·
                    refine ⟨8900577815313288665483261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5933718543542192443655507 8900577815313288665483261)
                    ·
                      refine ⟨3337716680742483249556223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8900577815313288665483261 3337716680742483249556223)
                      ·
                        rfl

theorem cell23_6500180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 2, 2, 1, 1, 3].length) (baseStart_6500180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6500180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6500180 prefixEnd_6500180 := by exact prefixLift 6500180
  have htrace : WordTrace (prefixWord ++ tailWord_6500180) baseStart_6500180 baseEnd_6500180 := by
    simpa [prefixWord, tailWord_6500180, baseEnd_6500180] using wordTrace_append hprefix tailTrace_6500180
  have hstable : (prefixWord ++ tailWord_6500180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6500180).length < 2 ^ (prefixWord ++ tailWord_6500180).sum := by decide
  have hdescent : baseEnd_6500180 < baseStart_6500180 := by decide
  rcases family_descends (prefixWord ++ tailWord_6500180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6500192 : List Nat := [2, 1, 1, 3, 3, 4, 1, 8]
def baseStart_6500192 : Nat := 118140960795 + 6500192 * 2 ^ 59
def prefixEnd_6500192 : Nat := 4983230072969 + 3 ^ 40 * 6500192 * 2
def baseEnd_6500192 : Nat := 123619364537419896392821

theorem tailTrace_6500192 : CollatzResearch.WordTrace tailWord_6500192 prefixEnd_6500192 123619364537419896392821 := by
  unfold tailWord_6500192
  simp only [CollatzResearch.WordTrace]
  refine ⟨118540739633461001627799415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158054319511281335503732553 118540739633461001627799415)
  ·
    refine ⟨177811109450191502441699123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118540739633461001627799415 177811109450191502441699123)
    ·
      refine ⟨266716664175287253662548685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177811109450191502441699123 266716664175287253662548685)
      ·
        refine ⟨100018749065732720123455757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 266716664175287253662548685 100018749065732720123455757)
        ·
          refine ⟨37507030899649770046295909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100018749065732720123455757 37507030899649770046295909)
          ·
            refine ⟨7032568293684331883680483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37507030899649770046295909 7032568293684331883680483)
            ·
              refine ⟨10548852440526497825520725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7032568293684331883680483 10548852440526497825520725)
              ·
                refine ⟨123619364537419896392821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10548852440526497825520725 123619364537419896392821)
                ·
                  rfl

theorem cell23_6500192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 1, 8].length) (baseStart_6500192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6500192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6500192 prefixEnd_6500192 := by exact prefixLift 6500192
  have htrace : WordTrace (prefixWord ++ tailWord_6500192) baseStart_6500192 baseEnd_6500192 := by
    simpa [prefixWord, tailWord_6500192, baseEnd_6500192] using wordTrace_append hprefix tailTrace_6500192
  have hstable : (prefixWord ++ tailWord_6500192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6500192).length < 2 ^ (prefixWord ++ tailWord_6500192).sum := by decide
  have hdescent : baseEnd_6500192 < baseStart_6500192 := by decide
  rcases family_descends (prefixWord ++ tailWord_6500192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6500253 : List Nat := [1, 4, 2, 1, 2, 3, 3, 1, 2, 1, 3]
def baseStart_6500253 : Nat := 118140960795 + 6500253 * 2 ^ 59
def prefixEnd_6500253 : Nat := 4983230072969 + 3 ^ 40 * 6500253 * 2
def baseEnd_6500253 : Nat := 3337754164830261463943387

theorem tailTrace_6500253 : CollatzResearch.WordTrace tailWord_6500253 prefixEnd_6500253 3337754164830261463943387 := by
  unfold tailWord_6500253
  simp only [CollatzResearch.WordTrace]
  refine ⟨237083704119701010673569413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158055802746467340449046275 237083704119701010673569413)
  ·
    refine ⟨44453194522443939501294265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 237083704119701010673569413 44453194522443939501294265)
    ·
      refine ⟨33339895891832954625970699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44453194522443939501294265 33339895891832954625970699)
      ·
        refine ⟨50009843837749431938956049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33339895891832954625970699 50009843837749431938956049)
        ·
          refine ⟨37507382878312073954217037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50009843837749431938956049 37507382878312073954217037)
          ·
            refine ⟨14065268579367027732831389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37507382878312073954217037 14065268579367027732831389)
            ·
              refine ⟨5274475717262635399811771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14065268579367027732831389 5274475717262635399811771)
              ·
                refine ⟨7911713575893953099717657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5274475717262635399811771 7911713575893953099717657)
                ·
                  refine ⟨5933785181920464824788243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7911713575893953099717657 5933785181920464824788243)
                  ·
                    refine ⟨8900677772880697237182365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5933785181920464824788243 8900677772880697237182365)
                    ·
                      refine ⟨3337754164830261463943387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8900677772880697237182365 3337754164830261463943387)
                      ·
                        rfl

theorem cell23_6500253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 3, 1, 2, 1, 3].length) (baseStart_6500253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6500253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6500253 prefixEnd_6500253 := by exact prefixLift 6500253
  have htrace : WordTrace (prefixWord ++ tailWord_6500253) baseStart_6500253 baseEnd_6500253 := by
    simpa [prefixWord, tailWord_6500253, baseEnd_6500253] using wordTrace_append hprefix tailTrace_6500253
  have hstable : (prefixWord ++ tailWord_6500253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6500253).length < 2 ^ (prefixWord ++ tailWord_6500253).sum := by decide
  have hdescent : baseEnd_6500253 < baseStart_6500253 := by decide
  rcases family_descends (prefixWord ++ tailWord_6500253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6500263 : List Nat := [1, 1, 6, 1, 2, 2, 2, 2, 1, 3, 2]
def baseStart_6500263 : Nat := 118140960795 + 6500263 * 2 ^ 59
def prefixEnd_6500263 : Nat := 4983230072969 + 3 ^ 40 * 6500263 * 2
def baseEnd_6500263 : Nat := 3337759299636806424818341

theorem tailTrace_6500263 : CollatzResearch.WordTrace tailWord_6500263 prefixEnd_6500263 3337759299636806424818341 := by
  unfold tailWord_6500263
  simp only [CollatzResearch.WordTrace]
  refine ⟨237084068849664782381433443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158056045899776521587622295 237084068849664782381433443)
  ·
    refine ⟨355626103274497173572150165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237084068849664782381433443 355626103274497173572150165)
    ·
      refine ⟨16669973590992055011194539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 355626103274497173572150165 16669973590992055011194539)
      ·
        refine ⟨25004960386488082516791809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16669973590992055011194539 25004960386488082516791809)
        ·
          refine ⟨18753720289866061887593857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25004960386488082516791809 18753720289866061887593857)
          ·
            refine ⟨14065290217399546415695393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18753720289866061887593857 14065290217399546415695393)
            ·
              refine ⟨10548967663049659811771545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14065290217399546415695393 10548967663049659811771545)
              ·
                refine ⟨7911725747287244858828659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10548967663049659811771545 7911725747287244858828659)
                ·
                  refine ⟨11867588620930867288242989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7911725747287244858828659 11867588620930867288242989)
                  ·
                    refine ⟨4450345732849075233091121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11867588620930867288242989 4450345732849075233091121)
                    ·
                      refine ⟨3337759299636806424818341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4450345732849075233091121 3337759299636806424818341)
                      ·
                        rfl

theorem cell23_6500263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 2, 2, 1, 3, 2].length) (baseStart_6500263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6500263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6500263 prefixEnd_6500263 := by exact prefixLift 6500263
  have htrace : WordTrace (prefixWord ++ tailWord_6500263) baseStart_6500263 baseEnd_6500263 := by
    simpa [prefixWord, tailWord_6500263, baseEnd_6500263] using wordTrace_append hprefix tailTrace_6500263
  have hstable : (prefixWord ++ tailWord_6500263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6500263).length < 2 ^ (prefixWord ++ tailWord_6500263).sum := by decide
  have hdescent : baseEnd_6500263 < baseStart_6500263 := by decide
  rcases family_descends (prefixWord ++ tailWord_6500263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6500265 : List Nat := [1, 2, 1, 1, 1, 1, 4, 3, 9]
def baseStart_6500265 : Nat := 118140960795 + 6500265 * 2 ^ 59
def prefixEnd_6500265 : Nat := 4983230072969 + 3 ^ 40 * 6500265 * 2
def baseEnd_6500265 : Nat := 370862258510901712999259

theorem tailTrace_6500265 : CollatzResearch.WordTrace tailWord_6500265 prefixEnd_6500265 370862258510901712999259 := by
  unfold tailWord_6500265
  simp only [CollatzResearch.WordTrace]
  refine ⟨237084141795657536723006249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158056094530438357815337499 237084141795657536723006249)
  ·
    refine ⟨177813106346743152542254687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237084141795657536723006249 177813106346743152542254687)
    ·
      refine ⟨266719659520114728813382031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177813106346743152542254687 266719659520114728813382031)
      ·
        refine ⟨400079489280172093220073047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266719659520114728813382031 400079489280172093220073047)
        ·
          refine ⟨600119233920258139830109571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 400079489280172093220073047 600119233920258139830109571)
          ·
            refine ⟨900178850880387209745164357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 600119233920258139830109571 900178850880387209745164357)
            ·
              refine ⟨168783534540072601827218317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 900178850880387209745164357 168783534540072601827218317)
              ·
                refine ⟨63293825452527225685206869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 168783534540072601827218317 63293825452527225685206869)
                ·
                  refine ⟨370862258510901712999259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 63293825452527225685206869 370862258510901712999259)
                  ·
                    rfl

theorem cell23_6500265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 3, 9].length) (baseStart_6500265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6500265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6500265 prefixEnd_6500265 := by exact prefixLift 6500265
  have htrace : WordTrace (prefixWord ++ tailWord_6500265) baseStart_6500265 baseEnd_6500265 := by
    simpa [prefixWord, tailWord_6500265, baseEnd_6500265] using wordTrace_append hprefix tailTrace_6500265
  have hstable : (prefixWord ++ tailWord_6500265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6500265).length < 2 ^ (prefixWord ++ tailWord_6500265).sum := by decide
  have hdescent : baseEnd_6500265 < baseStart_6500265 := by decide
  rcases family_descends (prefixWord ++ tailWord_6500265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6500312 : List Nat := [2, 1, 2, 2, 2, 2, 1, 2, 4, 5]
def baseStart_6500312 : Nat := 118140960795 + 6500312 * 2 ^ 59
def prefixEnd_6500312 : Nat := 4983230072969 + 3 ^ 40 * 6500312 * 2
def baseEnd_6500312 : Nat := 1112594820062958911035205

theorem tailTrace_6500312 : CollatzResearch.WordTrace tailWord_6500312 prefixEnd_6500312 1112594820062958911035205 := by
  unfold tailWord_6500312
  simp only [CollatzResearch.WordTrace]
  refine ⟨118542928013243631874983595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158057237350991509166644793 118542928013243631874983595)
  ·
    refine ⟨177814392019865447812475393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118542928013243631874983595 177814392019865447812475393)
    ·
      refine ⟨133360794014899085859356545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177814392019865447812475393 133360794014899085859356545)
      ·
        refine ⟨100020595511174314394517409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133360794014899085859356545 100020595511174314394517409)
        ·
          refine ⟨75015446633380735795888057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100020595511174314394517409 75015446633380735795888057)
          ·
            refine ⟨56261584975035551846916043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75015446633380735795888057 56261584975035551846916043)
            ·
              refine ⟨84392377462553327770374065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56261584975035551846916043 84392377462553327770374065)
              ·
                refine ⟨63294283096914995827780549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84392377462553327770374065 63294283096914995827780549)
                ·
                  refine ⟨11867678080671561717708853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63294283096914995827780549 11867678080671561717708853)
                  ·
                    refine ⟨1112594820062958911035205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11867678080671561717708853 1112594820062958911035205)
                    ·
                      rfl

theorem cell23_6500312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 2, 4, 5].length) (baseStart_6500312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6500312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6500312 prefixEnd_6500312 := by exact prefixLift 6500312
  have htrace : WordTrace (prefixWord ++ tailWord_6500312) baseStart_6500312 baseEnd_6500312 := by
    simpa [prefixWord, tailWord_6500312, baseEnd_6500312] using wordTrace_append hprefix tailTrace_6500312
  have hstable : (prefixWord ++ tailWord_6500312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6500312).length < 2 ^ (prefixWord ++ tailWord_6500312).sum := by decide
  have hdescent : baseEnd_6500312 < baseStart_6500312 := by decide
  rcases family_descends (prefixWord ++ tailWord_6500312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6500332 : List Nat := [2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 4]
def baseStart_6500332 : Nat := 118140960795 + 6500332 * 2 ^ 59
def prefixEnd_6500332 : Nat := 4983230072969 + 3 ^ 40 * 6500332 * 2
def baseEnd_6500332 : Nat := 3337794729801966654855523

theorem tailTrace_6500332 : CollatzResearch.WordTrace tailWord_6500332 prefixEnd_6500332 3337794729801966654855523 := by
  unfold tailWord_6500332
  simp only [CollatzResearch.WordTrace]
  refine ⟨118543292743207403582847625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158057723657609871443796833 118543292743207403582847625)
  ·
    refine ⟨88907469557405552687135719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118543292743207403582847625 88907469557405552687135719)
    ·
      refine ⟨133361204336108329030703579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88907469557405552687135719 133361204336108329030703579)
      ·
        refine ⟨200041806504162493546055369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133361204336108329030703579 200041806504162493546055369)
        ·
          refine ⟨150031354878121870159541527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 200041806504162493546055369 150031354878121870159541527)
          ·
            refine ⟨225047032317182805239312291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150031354878121870159541527 225047032317182805239312291)
            ·
              refine ⟨337570548475774207858968437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 225047032317182805239312291 337570548475774207858968437)
              ·
                refine ⟨31647238919603831986778291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 337570548475774207858968437 31647238919603831986778291)
                ·
                  refine ⟨47470858379405747980167437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31647238919603831986778291 47470858379405747980167437)
                  ·
                    refine ⟨17801571892277155492562789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47470858379405747980167437 17801571892277155492562789)
                    ·
                      refine ⟨3337794729801966654855523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17801571892277155492562789 3337794729801966654855523)
                      ·
                        rfl

theorem cell23_6500332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 4].length) (baseStart_6500332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6500332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6500332 prefixEnd_6500332 := by exact prefixLift 6500332
  have htrace : WordTrace (prefixWord ++ tailWord_6500332) baseStart_6500332 baseEnd_6500332 := by
    simpa [prefixWord, tailWord_6500332, baseEnd_6500332] using wordTrace_append hprefix tailTrace_6500332
  have hstable : (prefixWord ++ tailWord_6500332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6500332).length < 2 ^ (prefixWord ++ tailWord_6500332).sum := by decide
  have hdescent : baseEnd_6500332 < baseStart_6500332 := by decide
  rcases family_descends (prefixWord ++ tailWord_6500332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6500349 : List Nat := [1, 4, 1, 1, 1, 2, 4, 2, 2, 1, 4]
def baseStart_6500349 : Nat := 118140960795 + 6500349 * 2 ^ 59
def prefixEnd_6500349 : Nat := 4983230072969 + 3 ^ 40 * 6500349 * 2
def baseEnd_6500349 : Nat := 3337803458973093088342945

theorem tailTrace_6500349 : CollatzResearch.WordTrace tailWord_6500349 prefixEnd_6500349 3337803458973093088342945 := by
  unfold tailWord_6500349
  simp only [CollatzResearch.WordTrace]
  refine ⟨237087205527353219069064101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158058137018235479379376067 237087205527353219069064101)
  ·
    refine ⟨44453851036378728575449519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 237087205527353219069064101 44453851036378728575449519)
    ·
      refine ⟨66680776554568092863174279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44453851036378728575449519 66680776554568092863174279)
      ·
        refine ⟨100021164831852139294761419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66680776554568092863174279 100021164831852139294761419)
        ·
          refine ⟨150031747247778208942142129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100021164831852139294761419 150031747247778208942142129)
          ·
            refine ⟨112523810435833656706606597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150031747247778208942142129 112523810435833656706606597)
            ·
              refine ⟨21098214456718810632488737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 112523810435833656706606597 21098214456718810632488737)
              ·
                refine ⟨15823660842539107974366553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21098214456718810632488737 15823660842539107974366553)
                ·
                  refine ⟨11867745631904330980774915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15823660842539107974366553 11867745631904330980774915)
                  ·
                    refine ⟨17801618447856496471162373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11867745631904330980774915 17801618447856496471162373)
                    ·
                      refine ⟨3337803458973093088342945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17801618447856496471162373 3337803458973093088342945)
                      ·
                        rfl

theorem cell23_6500349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 2, 2, 1, 4].length) (baseStart_6500349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6500349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6500349 prefixEnd_6500349 := by exact prefixLift 6500349
  have htrace : WordTrace (prefixWord ++ tailWord_6500349) baseStart_6500349 baseEnd_6500349 := by
    simpa [prefixWord, tailWord_6500349, baseEnd_6500349] using wordTrace_append hprefix tailTrace_6500349
  have hstable : (prefixWord ++ tailWord_6500349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6500349).length < 2 ^ (prefixWord ++ tailWord_6500349).sum := by decide
  have hdescent : baseEnd_6500349 < baseStart_6500349 := by decide
  rcases family_descends (prefixWord ++ tailWord_6500349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6500350 : List Nat := [4, 2, 2, 2, 1, 3, 2, 2, 5]
def baseStart_6500350 : Nat := 118140960795 + 6500350 * 2 ^ 59
def prefixEnd_6500350 : Nat := 4983230072969 + 3 ^ 40 * 6500350 * 2
def baseEnd_6500350 : Nat := 370867108050416398270049

theorem tailTrace_6500350 : CollatzResearch.WordTrace tailWord_6500350 prefixEnd_6500350 370867108050416398270049 := by
  unfold tailWord_6500350
  simp only [CollatzResearch.WordTrace]
  refine ⟨29635905250043699529981313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 158058161333566397493233669 29635905250043699529981313)
  ·
    refine ⟨22226928937532774647485985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29635905250043699529981313 22226928937532774647485985)
    ·
      refine ⟨16670196703149580985614489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22226928937532774647485985 16670196703149580985614489)
      ·
        refine ⟨12502647527362185739210867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16670196703149580985614489 12502647527362185739210867)
        ·
          refine ⟨18753971291043278608816301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12502647527362185739210867 18753971291043278608816301)
          ·
            refine ⟨7032739234141229478306113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18753971291043278608816301 7032739234141229478306113)
            ·
              refine ⟨5274554425605922108729585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7032739234141229478306113 5274554425605922108729585)
              ·
                refine ⟨3955915819204441581547189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5274554425605922108729585 3955915819204441581547189)
                ·
                  refine ⟨370867108050416398270049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3955915819204441581547189 370867108050416398270049)
                  ·
                    rfl

theorem cell23_6500350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 2, 2, 5].length) (baseStart_6500350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6500350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6500350 prefixEnd_6500350 := by exact prefixLift 6500350
  have htrace : WordTrace (prefixWord ++ tailWord_6500350) baseStart_6500350 baseEnd_6500350 := by
    simpa [prefixWord, tailWord_6500350, baseEnd_6500350] using wordTrace_append hprefix tailTrace_6500350
  have hstable : (prefixWord ++ tailWord_6500350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6500350).length < 2 ^ (prefixWord ++ tailWord_6500350).sum := by decide
  have hdescent : baseEnd_6500350 < baseStart_6500350 := by decide
  rcases family_descends (prefixWord ++ tailWord_6500350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6500366 : List Nat := [4, 1, 1, 2, 2, 1, 3, 1, 2, 4, 2]
def baseStart_6500366 : Nat := 118140960795 + 6500366 * 2 ^ 59
def prefixEnd_6500366 : Nat := 4983230072969 + 3 ^ 40 * 6500366 * 2
def baseEnd_6500366 : Nat := 3337812188144219521830367

theorem tailTrace_6500366 : CollatzResearch.WordTrace tailWord_6500366 prefixEnd_6500366 3337812188144219521830367 := by
  unfold tailWord_6500366
  simp only [CollatzResearch.WordTrace]
  refine ⟨29635978196036453871554119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 158058550378861087314955301 29635978196036453871554119)
  ·
    refine ⟨44453967294054680807331179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29635978196036453871554119 44453967294054680807331179)
    ·
      refine ⟨66680950941082021210996769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44453967294054680807331179 66680950941082021210996769)
      ·
        refine ⟨50010713205811515908247577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66680950941082021210996769 50010713205811515908247577)
        ·
          refine ⟨37508034904358636931185683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50010713205811515908247577 37508034904358636931185683)
          ·
            refine ⟨56262052356537955396778525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37508034904358636931185683 56262052356537955396778525)
            ·
              refine ⟨21098269633701733273791947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56262052356537955396778525 21098269633701733273791947)
              ·
                refine ⟨31647404450552599910687921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21098269633701733273791947 31647404450552599910687921)
                ·
                  refine ⟨23735553337914449933015941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31647404450552599910687921 23735553337914449933015941)
                  ·
                    refine ⟨4450416250858959362440489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23735553337914449933015941 4450416250858959362440489)
                    ·
                      refine ⟨3337812188144219521830367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4450416250858959362440489 3337812188144219521830367)
                      ·
                        rfl

theorem cell23_6500366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 1, 2, 4, 2].length) (baseStart_6500366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6500366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6500366 prefixEnd_6500366 := by exact prefixLift 6500366
  have htrace : WordTrace (prefixWord ++ tailWord_6500366) baseStart_6500366 baseEnd_6500366 := by
    simpa [prefixWord, tailWord_6500366, baseEnd_6500366] using wordTrace_append hprefix tailTrace_6500366
  have hstable : (prefixWord ++ tailWord_6500366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6500366).length < 2 ^ (prefixWord ++ tailWord_6500366).sum := by decide
  have hdescent : baseEnd_6500366 < baseStart_6500366 := by decide
  rcases family_descends (prefixWord ++ tailWord_6500366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6500416 : List Nat := [2, 1, 1, 2, 2, 4, 1, 3, 3, 1, 3]
def baseStart_6500416 : Nat := 118140960795 + 6500416 * 2 ^ 59
def prefixEnd_6500416 : Nat := 4983230072969 + 3 ^ 40 * 6500416 * 2
def baseEnd_6500416 : Nat := 3337837862176944326205137

theorem tailTrace_6500416 : CollatzResearch.WordTrace tailWord_6500416 prefixEnd_6500416 3337837862176944326205137 := by
  unfold tailWord_6500416
  simp only [CollatzResearch.WordTrace]
  refine ⟨118544824609055244755876551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158059766145406993007835401 118544824609055244755876551)
  ·
    refine ⟨177817236913582867133814827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118544824609055244755876551 177817236913582867133814827)
    ·
      refine ⟨266725855370374300700722241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177817236913582867133814827 266725855370374300700722241)
      ·
        refine ⟨200044391527780725525541681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 266725855370374300700722241 200044391527780725525541681)
        ·
          refine ⟨150033293645835544144156261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 200044391527780725525541681 150033293645835544144156261)
          ·
            refine ⟨28131242558594164527029299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 150033293645835544144156261 28131242558594164527029299)
            ·
              refine ⟨42196863837891246790543949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28131242558594164527029299 42196863837891246790543949)
              ·
                refine ⟨15823823939209217546453981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42196863837891246790543949 15823823939209217546453981)
                ·
                  refine ⟨5933933977203456579920243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15823823939209217546453981 5933933977203456579920243)
                  ·
                    refine ⟨8900900965805184869880365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5933933977203456579920243 8900900965805184869880365)
                    ·
                      refine ⟨3337837862176944326205137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8900900965805184869880365 3337837862176944326205137)
                      ·
                        rfl

theorem cell23_6500416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 3, 3, 1, 3].length) (baseStart_6500416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6500416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6500416 prefixEnd_6500416 := by exact prefixLift 6500416
  have htrace : WordTrace (prefixWord ++ tailWord_6500416) baseStart_6500416 baseEnd_6500416 := by
    simpa [prefixWord, tailWord_6500416, baseEnd_6500416] using wordTrace_append hprefix tailTrace_6500416
  have hstable : (prefixWord ++ tailWord_6500416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6500416).length < 2 ^ (prefixWord ++ tailWord_6500416).sum := by decide
  have hdescent : baseEnd_6500416 < baseStart_6500416 := by decide
  rcases family_descends (prefixWord ++ tailWord_6500416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6500439 : List Nat := [1, 1, 3, 2, 2, 1, 2, 3, 3, 1, 4]
def baseStart_6500439 : Nat := 118140960795 + 6500439 * 2 ^ 59
def prefixEnd_6500439 : Nat := 4983230072969 + 3 ^ 40 * 6500439 * 2
def baseEnd_6500439 : Nat := 3337849672231997736217531

theorem tailTrace_6500439 : CollatzResearch.WordTrace tailWord_6500439 prefixEnd_6500439 3337849672231997736217531 := by
  unfold tailWord_6500439
  simp only [CollatzResearch.WordTrace]
  refine ⟨237090488097027164439840371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158060325398018109626560247 237090488097027164439840371)
  ·
    refine ⟨355635732145540746659760557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237090488097027164439840371 355635732145540746659760557)
    ·
      refine ⟨133363399554577779997410209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 355635732145540746659760557 133363399554577779997410209)
      ·
        refine ⟨100022549665933334998057657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133363399554577779997410209 100022549665933334998057657)
        ·
          refine ⟨75016912249450001248543243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100022549665933334998057657 75016912249450001248543243)
          ·
            refine ⟨112525368374175001872814865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75016912249450001248543243 112525368374175001872814865)
            ·
              refine ⟨84394026280631251404611149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112525368374175001872814865 84394026280631251404611149)
              ·
                refine ⟨31647759855236719276729181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84394026280631251404611149 31647759855236719276729181)
                ·
                  refine ⟨11867909945713769728773443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31647759855236719276729181 11867909945713769728773443)
                  ·
                    refine ⟨17801864918570654593160165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11867909945713769728773443 17801864918570654593160165)
                    ·
                      refine ⟨3337849672231997736217531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17801864918570654593160165 3337849672231997736217531)
                      ·
                        rfl

theorem cell23_6500439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 3, 3, 1, 4].length) (baseStart_6500439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6500439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6500439 prefixEnd_6500439 := by exact prefixLift 6500439
  have htrace : WordTrace (prefixWord ++ tailWord_6500439) baseStart_6500439 baseEnd_6500439 := by
    simpa [prefixWord, tailWord_6500439, baseEnd_6500439] using wordTrace_append hprefix tailTrace_6500439
  have hstable : (prefixWord ++ tailWord_6500439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6500439).length < 2 ^ (prefixWord ++ tailWord_6500439).sum := by decide
  have hdescent : baseEnd_6500439 < baseStart_6500439 := by decide
  rcases family_descends (prefixWord ++ tailWord_6500439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6500466 : List Nat := [3, 2, 1, 2, 2, 2, 2, 1, 4, 4]
def baseStart_6500466 : Nat := 118140960795 + 6500466 * 2 ^ 59
def prefixEnd_6500466 : Nat := 4983230072969 + 3 ^ 40 * 6500466 * 2
def baseEnd_6500466 : Nat := 1112621178736556376859969

theorem tailTrace_6500466 : CollatzResearch.WordTrace tailWord_6500466 prefixEnd_6500466 1112621178736556376859969 := by
  unfold tailWord_6500466
  simp only [CollatzResearch.WordTrace]
  refine ⟨59272868216982337012768313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158060981911952898700715501 59272868216982337012768313)
  ·
    refine ⟨44454651162736752759576235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59272868216982337012768313 44454651162736752759576235)
    ·
      refine ⟨66681976744105129139364353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44454651162736752759576235 66681976744105129139364353)
      ·
        refine ⟨50011482558078846854523265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66681976744105129139364353 50011482558078846854523265)
        ·
          refine ⟨37508611918559135140892449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50011482558078846854523265 37508611918559135140892449)
          ·
            refine ⟨28131458938919351355669337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37508611918559135140892449 28131458938919351355669337)
            ·
              refine ⟨21098594204189513516752003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28131458938919351355669337 21098594204189513516752003)
              ·
                refine ⟨31647891306284270275128005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21098594204189513516752003 31647891306284270275128005)
                ·
                  refine ⟨5933979619928300676586501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31647891306284270275128005 5933979619928300676586501)
                  ·
                    refine ⟨1112621178736556376859969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5933979619928300676586501 1112621178736556376859969)
                    ·
                      rfl

theorem cell23_6500466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 1, 4, 4].length) (baseStart_6500466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6500466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6500466 prefixEnd_6500466 := by exact prefixLift 6500466
  have htrace : WordTrace (prefixWord ++ tailWord_6500466) baseStart_6500466 baseEnd_6500466 := by
    simpa [prefixWord, tailWord_6500466, baseEnd_6500466] using wordTrace_append hprefix tailTrace_6500466
  have hstable : (prefixWord ++ tailWord_6500466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6500466).length < 2 ^ (prefixWord ++ tailWord_6500466).sum := by decide
  have hdescent : baseEnd_6500466 < baseStart_6500466 := by decide
  rcases family_descends (prefixWord ++ tailWord_6500466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6500483 : List Nat := [1, 1, 1, 3, 3, 3, 4, 1, 2, 4]
def baseStart_6500483 : Nat := 118140960795 + 6500483 * 2 ^ 59
def prefixEnd_6500483 : Nat := 4983230072969 + 3 ^ 40 * 6500483 * 2
def baseEnd_6500483 : Nat := 1112624088460265188022443

theorem tailTrace_6500483 : CollatzResearch.WordTrace tailWord_6500483 prefixEnd_6500483 1112624088460265188022443 := by
  unfold tailWord_6500483
  simp only [CollatzResearch.WordTrace]
  refine ⟨237092092908867759954442103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158061395272578506636294735 237092092908867759954442103)
  ·
    refine ⟨355638139363301639931663155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237092092908867759954442103 355638139363301639931663155)
    ·
      refine ⟨533457209044952459897494733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 355638139363301639931663155 533457209044952459897494733)
      ·
        refine ⟨200046453391857172461560525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 533457209044952459897494733 200046453391857172461560525)
        ·
          refine ⟨75017420021946439673085197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 200046453391857172461560525 75017420021946439673085197)
          ·
            refine ⟨28131532508229914877406949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75017420021946439673085197 28131532508229914877406949)
            ·
              refine ⟨5274662345293109039513803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28131532508229914877406949 5274662345293109039513803)
              ·
                refine ⟨7911993517939663559270705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5274662345293109039513803 7911993517939663559270705)
                ·
                  refine ⟨5933995138454747669453029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7911993517939663559270705 5933995138454747669453029)
                  ·
                    refine ⟨1112624088460265188022443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5933995138454747669453029 1112624088460265188022443)
                    ·
                      rfl

theorem cell23_6500483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 4, 1, 2, 4].length) (baseStart_6500483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6500483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6500483 prefixEnd_6500483 := by exact prefixLift 6500483
  have htrace : WordTrace (prefixWord ++ tailWord_6500483) baseStart_6500483 baseEnd_6500483 := by
    simpa [prefixWord, tailWord_6500483, baseEnd_6500483] using wordTrace_append hprefix tailTrace_6500483
  have hstable : (prefixWord ++ tailWord_6500483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6500483).length < 2 ^ (prefixWord ++ tailWord_6500483).sum := by decide
  have hdescent : baseEnd_6500483 < baseStart_6500483 := by decide
  rcases family_descends (prefixWord ++ tailWord_6500483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6500510 : List Nat := [4, 3, 1, 1, 3, 2, 1, 1, 1, 1, 5]
def baseStart_6500510 : Nat := 118140960795 + 6500510 * 2 ^ 59
def prefixEnd_6500510 : Nat := 4983230072969 + 3 ^ 40 * 6500510 * 2
def baseEnd_6500510 : Nat := 3337886129358466958429705

theorem tailTrace_6500510 : CollatzResearch.WordTrace tailWord_6500510 prefixEnd_6500510 3337886129358466958429705 := by
  unfold tailWord_6500510
  simp only [CollatzResearch.WordTrace]
  refine ⟨29636634709971242945709373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 158062051786513295710449989 29636634709971242945709373)
  ·
    refine ⟨11113738016239216104641015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29636634709971242945709373 11113738016239216104641015)
    ·
      refine ⟨16670607024358824156961523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11113738016239216104641015 16670607024358824156961523)
      ·
        refine ⟨25005910536538236235442285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16670607024358824156961523 25005910536538236235442285)
        ·
          refine ⟨9377216451201838588290857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25005910536538236235442285 9377216451201838588290857)
          ·
            refine ⟨7032912338401378941218143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9377216451201838588290857 7032912338401378941218143)
            ·
              refine ⟨10549368507602068411827215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7032912338401378941218143 10549368507602068411827215)
              ·
                refine ⟨15824052761403102617740823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10549368507602068411827215 15824052761403102617740823)
                ·
                  refine ⟨23736079142104653926611235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15824052761403102617740823 23736079142104653926611235)
                  ·
                    refine ⟨35604118713156980889916853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23736079142104653926611235 35604118713156980889916853)
                    ·
                      refine ⟨3337886129358466958429705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35604118713156980889916853 3337886129358466958429705)
                      ·
                        rfl

theorem cell23_6500510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 1, 1, 1, 1, 5].length) (baseStart_6500510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6500510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6500510 prefixEnd_6500510 := by exact prefixLift 6500510
  have htrace : WordTrace (prefixWord ++ tailWord_6500510) baseStart_6500510 baseEnd_6500510 := by
    simpa [prefixWord, tailWord_6500510, baseEnd_6500510] using wordTrace_append hprefix tailTrace_6500510
  have hstable : (prefixWord ++ tailWord_6500510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6500510).length < 2 ^ (prefixWord ++ tailWord_6500510).sum := by decide
  have hdescent : baseEnd_6500510 < baseStart_6500510 := by decide
  rcases family_descends (prefixWord ++ tailWord_6500510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6500539 : List Nat := [1, 1, 1, 1, 1, 2, 7, 1, 2, 6]
def baseStart_6500539 : Nat := 118140960795 + 6500539 * 2 ^ 59
def prefixEnd_6500539 : Nat := 4983230072969 + 3 ^ 40 * 6500539 * 2
def baseEnd_6500539 : Nat := 1112633673432482448322357

theorem tailTrace_6500539 : CollatzResearch.WordTrace tailWord_6500539 prefixEnd_6500539 1112633673432482448322357 := by
  unfold tailWord_6500539
  simp only [CollatzResearch.WordTrace]
  refine ⟨237094135396664881518480671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158062756931109921012320447 237094135396664881518480671)
  ·
    refine ⟨355641203094997322277721007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237094135396664881518480671 355641203094997322277721007)
    ·
      refine ⟨533461804642495983416581511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 355641203094997322277721007 533461804642495983416581511)
      ·
        refine ⟨800192706963743975124872267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 533461804642495983416581511 800192706963743975124872267)
        ·
          refine ⟨1200289060445615962687308401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 800192706963743975124872267 1200289060445615962687308401)
          ·
            refine ⟨900216795334211972015481301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1200289060445615962687308401 900216795334211972015481301)
            ·
              refine ⟨21098831140645593094112843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 900216795334211972015481301 21098831140645593094112843)
              ·
                refine ⟨31648246710968389641169265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21098831140645593094112843 31648246710968389641169265)
                ·
                  refine ⟨23736185033226292230876949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31648246710968389641169265 23736185033226292230876949)
                  ·
                    refine ⟨1112633673432482448322357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23736185033226292230876949 1112633673432482448322357)
                    ·
                      rfl

theorem cell23_6500539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 1, 2, 6].length) (baseStart_6500539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6500539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6500539 prefixEnd_6500539 := by exact prefixLift 6500539
  have htrace : WordTrace (prefixWord ++ tailWord_6500539) baseStart_6500539 baseEnd_6500539 := by
    simpa [prefixWord, tailWord_6500539, baseEnd_6500539] using wordTrace_append hprefix tailTrace_6500539
  have hstable : (prefixWord ++ tailWord_6500539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6500539).length < 2 ^ (prefixWord ++ tailWord_6500539).sum := by decide
  have hdescent : baseEnd_6500539 < baseStart_6500539 := by decide
  rcases family_descends (prefixWord ++ tailWord_6500539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6500549 : List Nat := [1, 3, 1, 1, 1, 1, 4, 1, 4, 1, 5]
def baseStart_6500549 : Nat := 118140960795 + 6500549 * 2 ^ 59
def prefixEnd_6500549 : Nat := 4983230072969 + 3 ^ 40 * 6500549 * 2
def baseEnd_6500549 : Nat := 3337906155103992305842025

theorem tailTrace_6500549 : CollatzResearch.WordTrace tailWord_6500549 prefixEnd_6500549 3337906155103992305842025 := by
  unfold tailWord_6500549
  simp only [CollatzResearch.WordTrace]
  refine ⟨237094500126628653226344701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158063000084419102150896467 237094500126628653226344701)
  ·
    refine ⟨88910437547485744959879263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 237094500126628653226344701 88910437547485744959879263)
    ·
      refine ⟨133365656321228617439818895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88910437547485744959879263 133365656321228617439818895)
      ·
        refine ⟨200048484481842926159728343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133365656321228617439818895 200048484481842926159728343)
        ·
          refine ⟨300072726722764389239592515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200048484481842926159728343 300072726722764389239592515)
          ·
            refine ⟨450109090084146583859388773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 300072726722764389239592515 450109090084146583859388773)
            ·
              refine ⟨84395454390777484473635395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 450109090084146583859388773 84395454390777484473635395)
              ·
                refine ⟨126593181586166226710453093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84395454390777484473635395 126593181586166226710453093)
                ·
                  refine ⟨23736221547406167508209955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 126593181586166226710453093 23736221547406167508209955)
                  ·
                    refine ⟨35604332321109251262314933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23736221547406167508209955 35604332321109251262314933)
                    ·
                      refine ⟨3337906155103992305842025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35604332321109251262314933 3337906155103992305842025)
                      ·
                        rfl

theorem cell23_6500549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 1, 4, 1, 5].length) (baseStart_6500549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6500549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6500549 prefixEnd_6500549 := by exact prefixLift 6500549
  have htrace : WordTrace (prefixWord ++ tailWord_6500549) baseStart_6500549 baseEnd_6500549 := by
    simpa [prefixWord, tailWord_6500549, baseEnd_6500549] using wordTrace_append hprefix tailTrace_6500549
  have hstable : (prefixWord ++ tailWord_6500549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6500549).length < 2 ^ (prefixWord ++ tailWord_6500549).sum := by decide
  have hdescent : baseEnd_6500549 < baseStart_6500549 := by decide
  rcases family_descends (prefixWord ++ tailWord_6500549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6500559 : List Nat := [1, 1, 2, 1, 1, 3, 3, 2, 1, 4, 4]
def baseStart_6500559 : Nat := 118140960795 + 6500559 * 2 ^ 59
def prefixEnd_6500559 : Nat := 4983230072969 + 3 ^ 40 * 6500559 * 2
def baseEnd_6500559 : Nat := 3337911289910537266716979

theorem tailTrace_6500559 : CollatzResearch.WordTrace tailWord_6500559 prefixEnd_6500559 3337911289910537266716979 := by
  unfold tailWord_6500559
  simp only [CollatzResearch.WordTrace]
  refine ⟨237094864856592424934208731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158063243237728283289472487 237094864856592424934208731)
  ·
    refine ⟨355642297284888637401313097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237094864856592424934208731 355642297284888637401313097)
    ·
      refine ⟨266731722963666478050984823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 355642297284888637401313097 266731722963666478050984823)
      ·
        refine ⟨400097584445499717076477235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266731722963666478050984823 400097584445499717076477235)
        ·
          refine ⟨600146376668249575614715853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 400097584445499717076477235 600146376668249575614715853)
          ·
            refine ⟨225054891250593590855518445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 600146376668249575614715853 225054891250593590855518445)
            ·
              refine ⟨84395584218972596570819417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 225054891250593590855518445 84395584218972596570819417)
              ·
                refine ⟨63296688164229447428114563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84395584218972596570819417 63296688164229447428114563)
                ·
                  refine ⟨94945032246344171142171845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63296688164229447428114563 94945032246344171142171845)
                  ·
                    refine ⟨17802193546189532089157221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 94945032246344171142171845 17802193546189532089157221)
                    ·
                      refine ⟨3337911289910537266716979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17802193546189532089157221 3337911289910537266716979)
                      ·
                        rfl

theorem cell23_6500559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 2, 1, 4, 4].length) (baseStart_6500559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6500559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6500559 prefixEnd_6500559 := by exact prefixLift 6500559
  have htrace : WordTrace (prefixWord ++ tailWord_6500559) baseStart_6500559 baseEnd_6500559 := by
    simpa [prefixWord, tailWord_6500559, baseEnd_6500559] using wordTrace_append hprefix tailTrace_6500559
  have hstable : (prefixWord ++ tailWord_6500559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6500559).length < 2 ^ (prefixWord ++ tailWord_6500559).sum := by decide
  have hdescent : baseEnd_6500559 < baseStart_6500559 := by decide
  rcases family_descends (prefixWord ++ tailWord_6500559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6500586 : List Nat := [3, 1, 3, 1, 1, 2, 4, 1, 7]
def baseStart_6500586 : Nat := 118140960795 + 6500586 * 2 ^ 59
def prefixEnd_6500586 : Nat := 4983230072969 + 3 ^ 40 * 6500586 * 2
def baseEnd_6500586 : Nat := 370880572654245406786595

theorem tailTrace_6500586 : CollatzResearch.WordTrace tailWord_6500586 prefixEnd_6500586 370880572654245406786595 := by
  unfold tailWord_6500586
  simp only [CollatzResearch.WordTrace]
  refine ⟨59273962406873652136360403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158063899751663072363627741 59273962406873652136360403)
  ·
    refine ⟨88910943610310478204540605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59273962406873652136360403 88910943610310478204540605)
    ·
      refine ⟨33341603853866429326702727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88910943610310478204540605 33341603853866429326702727)
      ·
        refine ⟨50012405780799643990054091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33341603853866429326702727 50012405780799643990054091)
        ·
          refine ⟨75018608671199465985081137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50012405780799643990054091 75018608671199465985081137)
          ·
            refine ⟨56263956503399599488810853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75018608671199465985081137 56263956503399599488810853)
            ·
              refine ⟨10549491844387424904152035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56263956503399599488810853 10549491844387424904152035)
              ·
                refine ⟨15824237766581137356228053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10549491844387424904152035 15824237766581137356228053)
                ·
                  refine ⟨370880572654245406786595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15824237766581137356228053 370880572654245406786595)
                  ·
                    rfl

theorem cell23_6500586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 4, 1, 7].length) (baseStart_6500586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6500586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6500586 prefixEnd_6500586 := by exact prefixLift 6500586
  have htrace : WordTrace (prefixWord ++ tailWord_6500586) baseStart_6500586 baseEnd_6500586 := by
    simpa [prefixWord, tailWord_6500586, baseEnd_6500586] using wordTrace_append hprefix tailTrace_6500586
  have hstable : (prefixWord ++ tailWord_6500586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6500586).length < 2 ^ (prefixWord ++ tailWord_6500586).sum := by decide
  have hdescent : baseEnd_6500586 < baseStart_6500586 := by decide
  rcases family_descends (prefixWord ++ tailWord_6500586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6500616 : List Nat := [2, 1, 3, 2, 3, 1, 2, 1, 1, 7]
def baseStart_6500616 : Nat := 118140960795 + 6500616 * 2 ^ 59
def prefixEnd_6500616 : Nat := 4983230072969 + 3 ^ 40 * 6500616 * 2
def baseEnd_6500616 : Nat := 1112646852769281181234739

theorem tailTrace_6500616 : CollatzResearch.WordTrace tailWord_6500616 prefixEnd_6500616 1112646852769281181234739 := by
  unfold tailWord_6500616
  simp only [CollatzResearch.WordTrace]
  refine ⟨118548471908692961834516851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158064629211590615779355801 118548471908692961834516851)
  ·
    refine ⟨177822707863039442751775277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118548471908692961834516851 177822707863039442751775277)
    ·
      refine ⟨66683515448639791031915729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177822707863039442751775277 66683515448639791031915729)
      ·
        refine ⟨50012636586479843273936797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66683515448639791031915729 50012636586479843273936797)
        ·
          refine ⟨18754738719929941227726299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50012636586479843273936797 18754738719929941227726299)
          ·
            refine ⟨28132108079894911841589449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18754738719929941227726299 28132108079894911841589449)
            ·
              refine ⟨21099081059921183881192087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28132108079894911841589449 21099081059921183881192087)
              ·
                refine ⟨31648621589881775821788131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21099081059921183881192087 31648621589881775821788131)
                ·
                  refine ⟨47472932384822663732682197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31648621589881775821788131 47472932384822663732682197)
                  ·
                    refine ⟨1112646852769281181234739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47472932384822663732682197 1112646852769281181234739)
                    ·
                      rfl

theorem cell23_6500616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 1, 1, 7].length) (baseStart_6500616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6500616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6500616 prefixEnd_6500616 := by exact prefixLift 6500616
  have htrace : WordTrace (prefixWord ++ tailWord_6500616) baseStart_6500616 baseEnd_6500616 := by
    simpa [prefixWord, tailWord_6500616, baseEnd_6500616] using wordTrace_append hprefix tailTrace_6500616
  have hstable : (prefixWord ++ tailWord_6500616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6500616).length < 2 ^ (prefixWord ++ tailWord_6500616).sum := by decide
  have hdescent : baseEnd_6500616 < baseStart_6500616 := by decide
  rcases family_descends (prefixWord ++ tailWord_6500616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6500637 : List Nat := [1, 4, 2, 3, 2, 1, 3, 2, 5]
def baseStart_6500637 : Nat := 118140960795 + 6500637 * 2 ^ 59
def prefixEnd_6500637 : Nat := 4983230072969 + 3 ^ 40 * 6500637 * 2
def baseEnd_6500637 : Nat := 370883482377954217949069

theorem tailTrace_6500637 : CollatzResearch.WordTrace tailWord_6500637 prefixEnd_6500637 370883482377954217949069 := by
  unfold tailWord_6500637
  simp only [CollatzResearch.WordTrace]
  refine ⟨237097709750309844255548165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158065139833539896170365443 237097709750309844255548165)
  ·
    refine ⟨44455820578183095797915281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 237097709750309844255548165 44455820578183095797915281)
    ·
      refine ⟨33341865433637321848436461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44455820578183095797915281 33341865433637321848436461)
      ·
        refine ⟨12503199537613995693163673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33341865433637321848436461 12503199537613995693163673)
        ·
          refine ⟨9377399653210496769872755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12503199537613995693163673 9377399653210496769872755)
          ·
            refine ⟨14066099479815745154809133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9377399653210496769872755 14066099479815745154809133)
            ·
              refine ⟨5274787304930904433053425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14066099479815745154809133 5274787304930904433053425)
              ·
                refine ⟨3956090478698178324790069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5274787304930904433053425 3956090478698178324790069)
                ·
                  refine ⟨370883482377954217949069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3956090478698178324790069 370883482377954217949069)
                  ·
                    rfl

theorem cell23_6500637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 3, 2, 5].length) (baseStart_6500637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6500637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6500637 prefixEnd_6500637 := by exact prefixLift 6500637
  have htrace : WordTrace (prefixWord ++ tailWord_6500637) baseStart_6500637 baseEnd_6500637 := by
    simpa [prefixWord, tailWord_6500637, baseEnd_6500637] using wordTrace_append hprefix tailTrace_6500637
  have hstable : (prefixWord ++ tailWord_6500637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6500637).length < 2 ^ (prefixWord ++ tailWord_6500637).sum := by decide
  have hdescent : baseEnd_6500637 < baseStart_6500637 := by decide
  rcases family_descends (prefixWord ++ tailWord_6500637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6500656 : List Nat := [2, 1, 1, 1, 2, 2, 2, 4, 1, 4, 3]
def baseStart_6500656 : Nat := 118140960795 + 6500656 * 2 ^ 59
def prefixEnd_6500656 : Nat := 4983230072969 + 3 ^ 40 * 6500656 * 2
def baseEnd_6500656 : Nat := 3337961097534023387204033

theorem tailTrace_6500656 : CollatzResearch.WordTrace tailWord_6500656 prefixEnd_6500656 3337961097534023387204033 := by
  unfold tailWord_6500656
  simp only [CollatzResearch.WordTrace]
  refine ⟨118549201368620505250244911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158065601824827340333659881 118549201368620505250244911)
  ·
    refine ⟨177823802052930757875367367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118549201368620505250244911 177823802052930757875367367)
    ·
      refine ⟨266735703079396136813051051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177823802052930757875367367 266735703079396136813051051)
      ·
        refine ⟨400103554619094205219576577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266735703079396136813051051 400103554619094205219576577)
        ·
          refine ⟨300077665964320653914682433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 400103554619094205219576577 300077665964320653914682433)
          ·
            refine ⟨225058249473240490436011825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 300077665964320653914682433 225058249473240490436011825)
            ·
              refine ⟨168793687104930367827008869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 225058249473240490436011825 168793687104930367827008869)
              ·
                refine ⟨31648816332174443967564163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 168793687104930367827008869 31648816332174443967564163)
                ·
                  refine ⟨47473224498261665951346245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31648816332174443967564163 47473224498261665951346245)
                  ·
                    refine ⟨8901229593424062365877421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47473224498261665951346245 8901229593424062365877421)
                    ·
                      refine ⟨3337961097534023387204033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8901229593424062365877421 3337961097534023387204033)
                      ·
                        rfl

theorem cell23_6500656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 4, 1, 4, 3].length) (baseStart_6500656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6500656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6500656 prefixEnd_6500656 := by exact prefixLift 6500656
  have htrace : WordTrace (prefixWord ++ tailWord_6500656) baseStart_6500656 baseEnd_6500656 := by
    simpa [prefixWord, tailWord_6500656, baseEnd_6500656] using wordTrace_append hprefix tailTrace_6500656
  have hstable : (prefixWord ++ tailWord_6500656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6500656).length < 2 ^ (prefixWord ++ tailWord_6500656).sum := by decide
  have hdescent : baseEnd_6500656 < baseStart_6500656 := by decide
  rcases family_descends (prefixWord ++ tailWord_6500656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6500670 : List Nat := [4, 2, 1, 2, 1, 3, 2, 1, 2, 1, 4]
def baseStart_6500670 : Nat := 118140960795 + 6500670 * 2 ^ 59
def prefixEnd_6500670 : Nat := 4983230072969 + 3 ^ 40 * 6500670 * 2
def baseEnd_6500670 : Nat := 3337968286263186332428969

theorem tailTrace_6500670 : CollatzResearch.WordTrace tailWord_6500670 prefixEnd_6500670 3337968286263186332428969 := by
  unfold tailWord_6500670
  simp only [CollatzResearch.WordTrace]
  refine ⟨29637364169898786361437433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 158065942239460193927666309 29637364169898786361437433)
  ·
    refine ⟨22228023127424089771078075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29637364169898786361437433 22228023127424089771078075)
    ·
      refine ⟨33342034691136134656617113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22228023127424089771078075 33342034691136134656617113)
      ·
        refine ⟨25006526018352100992462835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33342034691136134656617113 25006526018352100992462835)
        ·
          refine ⟨37509789027528151488694253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25006526018352100992462835 37509789027528151488694253)
          ·
            refine ⟨14066170885323056808260345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37509789027528151488694253 14066170885323056808260345)
            ·
              refine ⟨10549628163992292606195259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14066170885323056808260345 10549628163992292606195259)
              ·
                refine ⟨15824442245988438909292889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10549628163992292606195259 15824442245988438909292889)
                ·
                  refine ⟨11868331684491329181969667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15824442245988438909292889 11868331684491329181969667)
                  ·
                    refine ⟨17802497526736993772954501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11868331684491329181969667 17802497526736993772954501)
                    ·
                      refine ⟨3337968286263186332428969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17802497526736993772954501 3337968286263186332428969)
                      ·
                        rfl

theorem cell23_6500670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 2, 1, 2, 1, 4].length) (baseStart_6500670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6500670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6500670 prefixEnd_6500670 := by exact prefixLift 6500670
  have htrace : WordTrace (prefixWord ++ tailWord_6500670) baseStart_6500670 baseEnd_6500670 := by
    simpa [prefixWord, tailWord_6500670, baseEnd_6500670] using wordTrace_append hprefix tailTrace_6500670
  have hstable : (prefixWord ++ tailWord_6500670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6500670).length < 2 ^ (prefixWord ++ tailWord_6500670).sum := by decide
  have hdescent : baseEnd_6500670 < baseStart_6500670 := by decide
  rcases family_descends (prefixWord ++ tailWord_6500670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6500713 : List Nat := [1, 2, 1, 1, 1, 3, 4, 2, 1, 5, 2]
def baseStart_6500713 : Nat := 118140960795 + 6500713 * 2 ^ 59
def prefixEnd_6500713 : Nat := 4983230072969 + 3 ^ 40 * 6500713 * 2
def baseEnd_6500713 : Nat := 3337990365931329664191271

theorem tailTrace_6500713 : CollatzResearch.WordTrace tailWord_6500713 prefixEnd_6500713 3337990365931329664191271 := by
  unfold tailWord_6500713
  simp only [CollatzResearch.WordTrace]
  refine ⟨237100481698034509235314793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158066987798689672823543195 237100481698034509235314793)
  ·
    refine ⟨177825361273525881926486095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237100481698034509235314793 177825361273525881926486095)
    ·
      refine ⟨266738041910288822889729143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177825361273525881926486095 266738041910288822889729143)
      ·
        refine ⟨400107062865433234334593715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266738041910288822889729143 400107062865433234334593715)
        ·
          refine ⟨600160594298149851501890573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 400107062865433234334593715 600160594298149851501890573)
          ·
            refine ⟨225060222861806194313208965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 600160594298149851501890573 225060222861806194313208965)
            ·
              refine ⟨42198791786588661433726681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 225060222861806194313208965 42198791786588661433726681)
              ·
                refine ⟨31649093839941496075295011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42198791786588661433726681 31649093839941496075295011)
                ·
                  refine ⟨47473640759912244112942517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31649093839941496075295011 47473640759912244112942517)
                  ·
                    refine ⟨4450653821241772885588361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47473640759912244112942517 4450653821241772885588361)
                    ·
                      refine ⟨3337990365931329664191271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4450653821241772885588361 3337990365931329664191271)
                      ·
                        rfl

theorem cell23_6500713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 2, 1, 5, 2].length) (baseStart_6500713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6500713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6500713 prefixEnd_6500713 := by exact prefixLift 6500713
  have htrace : WordTrace (prefixWord ++ tailWord_6500713) baseStart_6500713 baseEnd_6500713 := by
    simpa [prefixWord, tailWord_6500713, baseEnd_6500713] using wordTrace_append hprefix tailTrace_6500713
  have hstable : (prefixWord ++ tailWord_6500713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6500713).length < 2 ^ (prefixWord ++ tailWord_6500713).sum := by decide
  have hdescent : baseEnd_6500713 < baseStart_6500713 := by decide
  rcases family_descends (prefixWord ++ tailWord_6500713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6500720 : List Nat := [2, 1, 1, 1, 4, 4, 1, 2, 3, 1, 3]
def baseStart_6500720 : Nat := 118140960795 + 6500720 * 2 ^ 59
def prefixEnd_6500720 : Nat := 4983230072969 + 3 ^ 40 * 6500720 * 2
def baseEnd_6500720 : Nat := 3337993960295911136803739

theorem tailTrace_6500720 : CollatzResearch.WordTrace tailWord_6500720 prefixEnd_6500720 3337993960295911136803739 := by
  unfold tailWord_6500720
  simp only [CollatzResearch.WordTrace]
  refine ⟨118550368504504574715409807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158067158006006099620546409 118550368504504574715409807)
  ·
    refine ⟨177825552756756862073114711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118550368504504574715409807 177825552756756862073114711)
    ·
      refine ⟨266738329135135293109672067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177825552756756862073114711 266738329135135293109672067)
      ·
        refine ⟨400107493702702939664508101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266738329135135293109672067 400107493702702939664508101)
        ·
          refine ⟨75020155069256801187095269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 400107493702702939664508101 75020155069256801187095269)
          ·
            refine ⟨14066279075485650222580363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75020155069256801187095269 14066279075485650222580363)
            ·
              refine ⟨21099418613228475333870545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14066279075485650222580363 21099418613228475333870545)
              ·
                refine ⟨15824563959921356500402909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21099418613228475333870545 15824563959921356500402909)
                ·
                  refine ⟨5934211484970508687651091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15824563959921356500402909 5934211484970508687651091)
                  ·
                    refine ⟨8901317227455763031476637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5934211484970508687651091 8901317227455763031476637)
                    ·
                      refine ⟨3337993960295911136803739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8901317227455763031476637 3337993960295911136803739)
                      ·
                        rfl

theorem cell23_6500720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 2, 3, 1, 3].length) (baseStart_6500720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6500720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6500720 prefixEnd_6500720 := by exact prefixLift 6500720
  have htrace : WordTrace (prefixWord ++ tailWord_6500720) baseStart_6500720 baseEnd_6500720 := by
    simpa [prefixWord, tailWord_6500720, baseEnd_6500720] using wordTrace_append hprefix tailTrace_6500720
  have hstable : (prefixWord ++ tailWord_6500720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6500720).length < 2 ^ (prefixWord ++ tailWord_6500720).sum := by decide
  have hdescent : baseEnd_6500720 < baseStart_6500720 := by decide
  rcases family_descends (prefixWord ++ tailWord_6500720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6500810 : List Nat := [3, 1, 2, 1, 2, 2, 1, 3, 4, 1, 3]
def baseStart_6500810 : Nat := 118140960795 + 6500810 * 2 ^ 59
def prefixEnd_6500810 : Nat := 4983230072969 + 3 ^ 40 * 6500810 * 2
def baseEnd_6500810 : Nat := 3338040173554815784678325

theorem tailTrace_6500810 : CollatzResearch.WordTrace tailWord_6500810 prefixEnd_6500810 3338040173554815784678325 := by
  unfold tailWord_6500810
  simp only [CollatzResearch.WordTrace]
  refine ⟨59276004894670773700398971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158069346385788729867730589 59276004894670773700398971)
  ·
    refine ⟨88914007342006160550598457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59276004894670773700398971 88914007342006160550598457)
    ·
      refine ⟨66685505506504620412948843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88914007342006160550598457 66685505506504620412948843)
      ·
        refine ⟨100028258259756930619423265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66685505506504620412948843 100028258259756930619423265)
        ·
          refine ⟨75021193694817697964567449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100028258259756930619423265 75021193694817697964567449)
          ·
            refine ⟨56265895271113273473425587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75021193694817697964567449 56265895271113273473425587)
            ·
              refine ⟨84398842906669910210138381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56265895271113273473425587 84398842906669910210138381)
              ·
                refine ⟨31649566090001216328801893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84398842906669910210138381 31649566090001216328801893)
                ·
                  refine ⟨5934293641875228061650355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31649566090001216328801893 5934293641875228061650355)
                  ·
                    refine ⟨8901440462812842092475533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5934293641875228061650355 8901440462812842092475533)
                    ·
                      refine ⟨3338040173554815784678325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8901440462812842092475533 3338040173554815784678325)
                      ·
                        rfl

theorem cell23_6500810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 3, 4, 1, 3].length) (baseStart_6500810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6500810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6500810 prefixEnd_6500810 := by exact prefixLift 6500810
  have htrace : WordTrace (prefixWord ++ tailWord_6500810) baseStart_6500810 baseEnd_6500810 := by
    simpa [prefixWord, tailWord_6500810, baseEnd_6500810] using wordTrace_append hprefix tailTrace_6500810
  have hstable : (prefixWord ++ tailWord_6500810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6500810).length < 2 ^ (prefixWord ++ tailWord_6500810).sum := by decide
  have hdescent : baseEnd_6500810 < baseStart_6500810 := by decide
  rcases family_descends (prefixWord ++ tailWord_6500810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6500863 : List Nat := [1, 1, 2, 2, 1, 2, 4, 2, 2, 2, 4]
def baseStart_6500863 : Nat := 118140960795 + 6500863 * 2 ^ 59
def prefixEnd_6500863 : Nat := 4983230072969 + 3 ^ 40 * 6500863 * 2
def baseEnd_6500863 : Nat := 3338067388029504077315581

theorem tailTrace_6500863 : CollatzResearch.WordTrace tailWord_6500863 prefixEnd_6500863 3338067388029504077315581 := by
  unfold tailWord_6500863
  simp only [CollatzResearch.WordTrace]
  refine ⟨237105952647491084853275243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158070635098327389902183495 237105952647491084853275243)
  ·
    refine ⟨355658928971236627279912865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237105952647491084853275243 355658928971236627279912865)
    ·
      refine ⟨266744196728427470459934649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 355658928971236627279912865 266744196728427470459934649)
      ·
        refine ⟨200058147546320602844950987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 266744196728427470459934649 200058147546320602844950987)
        ·
          refine ⟨300087221319480904267426481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200058147546320602844950987 300087221319480904267426481)
          ·
            refine ⟨225065415989610678200569861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 300087221319480904267426481 225065415989610678200569861)
            ·
              refine ⟨42199765498052002162606849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 225065415989610678200569861 42199765498052002162606849)
              ·
                refine ⟨31649824123539001621955137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42199765498052002162606849 31649824123539001621955137)
                ·
                  refine ⟨23737368092654251216466353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31649824123539001621955137 23737368092654251216466353)
                  ·
                    refine ⟨17803026069490688412349765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23737368092654251216466353 17803026069490688412349765)
                    ·
                      refine ⟨3338067388029504077315581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17803026069490688412349765 3338067388029504077315581)
                      ·
                        rfl

theorem cell23_6500863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 2, 2, 2, 4].length) (baseStart_6500863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6500863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6500863 prefixEnd_6500863 := by exact prefixLift 6500863
  have htrace : WordTrace (prefixWord ++ tailWord_6500863) baseStart_6500863 baseEnd_6500863 := by
    simpa [prefixWord, tailWord_6500863, baseEnd_6500863] using wordTrace_append hprefix tailTrace_6500863
  have hstable : (prefixWord ++ tailWord_6500863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6500863).length < 2 ^ (prefixWord ++ tailWord_6500863).sum := by decide
  have hdescent : baseEnd_6500863 < baseStart_6500863 := by decide
  rcases family_descends (prefixWord ++ tailWord_6500863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6500877 : List Nat := [1, 7, 1, 1, 1, 1, 1, 1, 1, 8]
def baseStart_6500877 : Nat := 118140960795 + 6500877 * 2 ^ 59
def prefixEnd_6500877 : Nat := 4983230072969 + 3 ^ 40 * 6500877 * 2
def baseEnd_6500877 : Nat := 1112691525586222340846839

theorem tailTrace_6500877 : CollatzResearch.WordTrace tailWord_6500877 prefixEnd_6500877 1112691525586222340846839 := by
  unfold tailWord_6500877
  simp only [CollatzResearch.WordTrace]
  refine ⟨237106463269440365244284885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158070975512960243496189923 237106463269440365244284885)
  ·
    refine ⟨5557182732877508560412927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 237106463269440365244284885 5557182732877508560412927)
    ·
      refine ⟨8335774099316262840619391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5557182732877508560412927 8335774099316262840619391)
      ·
        refine ⟨12503661148974394260929087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8335774099316262840619391 12503661148974394260929087)
        ·
          refine ⟨18755491723461591391393631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12503661148974394260929087 18755491723461591391393631)
          ·
            refine ⟨28133237585192387087090447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18755491723461591391393631 28133237585192387087090447)
            ·
              refine ⟨42199856377788580630635671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28133237585192387087090447 42199856377788580630635671)
              ·
                refine ⟨63299784566682870945953507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42199856377788580630635671 63299784566682870945953507)
                ·
                  refine ⟨94949676850024306418930261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63299784566682870945953507 94949676850024306418930261)
                  ·
                    refine ⟨1112691525586222340846839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 94949676850024306418930261 1112691525586222340846839)
                    ·
                      rfl

theorem cell23_6500877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_6500877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6500877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6500877 prefixEnd_6500877 := by exact prefixLift 6500877
  have htrace : WordTrace (prefixWord ++ tailWord_6500877) baseStart_6500877 baseEnd_6500877 := by
    simpa [prefixWord, tailWord_6500877, baseEnd_6500877] using wordTrace_append hprefix tailTrace_6500877
  have hstable : (prefixWord ++ tailWord_6500877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6500877).length < 2 ^ (prefixWord ++ tailWord_6500877).sum := by decide
  have hdescent : baseEnd_6500877 < baseStart_6500877 := by decide
  rcases family_descends (prefixWord ++ tailWord_6500877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6500884 : List Nat := [2, 4, 3, 1, 1, 1, 1, 3, 1, 4, 2]
def baseStart_6500884 : Nat := 118140960795 + 6500884 * 2 ^ 59
def prefixEnd_6500884 : Nat := 4983230072969 + 3 ^ 40 * 6500884 * 2
def baseEnd_6500884 : Nat := 3338078171123248495152985

theorem tailTrace_6500884 : CollatzResearch.WordTrace tailWord_6500884 prefixEnd_6500884 3338078171123248495152985 := by
  unfold tailWord_6500884
  simp only [CollatzResearch.WordTrace]
  refine ⟨118553359290207502719894853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158071145720276670293193137 118553359290207502719894853)
  ·
    refine ⟨22228754866913906759980285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 118553359290207502719894853 22228754866913906759980285)
    ·
      refine ⟨8335783075092715034992607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22228754866913906759980285 8335783075092715034992607)
      ·
        refine ⟨12503674612639072552488911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8335783075092715034992607 12503674612639072552488911)
        ·
          refine ⟨18755511918958608828733367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12503674612639072552488911 18755511918958608828733367)
          ·
            refine ⟨28133267878437913243100051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18755511918958608828733367 28133267878437913243100051)
            ·
              refine ⟨42199901817656869864650077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28133267878437913243100051 42199901817656869864650077)
              ·
                refine ⟨15824963181621326199243779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42199901817656869864650077 15824963181621326199243779)
                ·
                  refine ⟨23737444772431989298865669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15824963181621326199243779 23737444772431989298865669)
                  ·
                    refine ⟨4450770894830997993537313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23737444772431989298865669 4450770894830997993537313)
                    ·
                      refine ⟨3338078171123248495152985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4450770894830997993537313 3338078171123248495152985)
                      ·
                        rfl

theorem cell23_6500884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 3, 1, 4, 2].length) (baseStart_6500884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6500884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6500884 prefixEnd_6500884 := by exact prefixLift 6500884
  have htrace : WordTrace (prefixWord ++ tailWord_6500884) baseStart_6500884 baseEnd_6500884 := by
    simpa [prefixWord, tailWord_6500884, baseEnd_6500884] using wordTrace_append hprefix tailTrace_6500884
  have hstable : (prefixWord ++ tailWord_6500884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6500884).length < 2 ^ (prefixWord ++ tailWord_6500884).sum := by decide
  have hdescent : baseEnd_6500884 < baseStart_6500884 := by decide
  rcases family_descends (prefixWord ++ tailWord_6500884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6500913 : List Nat := [1, 2, 2, 3, 1, 1, 2, 1, 3, 2, 5]
def baseStart_6500913 : Nat := 118140960795 + 6500913 * 2 ^ 59
def prefixEnd_6500913 : Nat := 4983230072969 + 3 ^ 40 * 6500913 * 2
def baseEnd_6500913 : Nat := 3338093062062228881690351

theorem tailTrace_6500913 : CollatzResearch.WordTrace tailWord_6500913 prefixEnd_6500913 3338093062062228881690351 := by
  unfold tailWord_6500913
  simp only [CollatzResearch.WordTrace]
  refine ⟨237107776297309943392595393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158071850864873295595063595 237107776297309943392595393)
  ·
    refine ⟨177830832222982457544446545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237107776297309943392595393 177830832222982457544446545)
    ·
      refine ⟨133373124167236843158334909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177830832222982457544446545 133373124167236843158334909)
      ·
        refine ⟨50014921562713816184375591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133373124167236843158334909 50014921562713816184375591)
        ·
          refine ⟨75022382344070724276563387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50014921562713816184375591 75022382344070724276563387)
          ·
            refine ⟨112533573516106086414845081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75022382344070724276563387 112533573516106086414845081)
            ·
              refine ⟨84400180137079564811133811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112533573516106086414845081 84400180137079564811133811)
              ·
                refine ⟨126600270205619347216700717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84400180137079564811133811 126600270205619347216700717)
                ·
                  refine ⟨47475101327107255206262769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 126600270205619347216700717 47475101327107255206262769)
                  ·
                    refine ⟨35606325995330441404697077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47475101327107255206262769 35606325995330441404697077)
                    ·
                      refine ⟨3338093062062228881690351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35606325995330441404697077 3338093062062228881690351)
                      ·
                        rfl

theorem cell23_6500913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 1, 3, 2, 5].length) (baseStart_6500913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6500913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6500913 prefixEnd_6500913 := by exact prefixLift 6500913
  have htrace : WordTrace (prefixWord ++ tailWord_6500913) baseStart_6500913 baseEnd_6500913 := by
    simpa [prefixWord, tailWord_6500913, baseEnd_6500913] using wordTrace_append hprefix tailTrace_6500913
  have hstable : (prefixWord ++ tailWord_6500913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6500913).length < 2 ^ (prefixWord ++ tailWord_6500913).sum := by decide
  have hdescent : baseEnd_6500913 < baseStart_6500913 := by decide
  rcases family_descends (prefixWord ++ tailWord_6500913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6500918 : List Nat := [5, 1, 2, 1, 2, 3, 1, 2, 2, 2, 2]
def baseStart_6500918 : Nat := 118140960795 + 6500918 * 2 ^ 59
def prefixEnd_6500918 : Nat := 4983230072969 + 3 ^ 40 * 6500918 * 2
def baseEnd_6500918 : Nat := 3338095629465501362127829

theorem tailTrace_6500918 : CollatzResearch.WordTrace tailWord_6500918 prefixEnd_6500918 3338095629465501362127829 := by
  unfold tailWord_6500918
  simp only [CollatzResearch.WordTrace]
  refine ⟨14819247416393239327907963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 158071972441527886164351605 14819247416393239327907963)
  ·
    refine ⟨22228871124589858991861945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14819247416393239327907963 22228871124589858991861945)
    ·
      refine ⟨16671653343442394243896459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22228871124589858991861945 16671653343442394243896459)
      ·
        refine ⟨25007480015163591365844689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16671653343442394243896459 25007480015163591365844689)
        ·
          refine ⟨18755610011372693524383517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25007480015163591365844689 18755610011372693524383517)
          ·
            refine ⟨7033353754264760071643819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18755610011372693524383517 7033353754264760071643819)
            ·
              refine ⟨10550030631397140107465729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7033353754264760071643819 10550030631397140107465729)
              ·
                refine ⟨7912522973547855080599297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10550030631397140107465729 7912522973547855080599297)
                ·
                  refine ⟨5934392230160891310449473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7912522973547855080599297 5934392230160891310449473)
                  ·
                    refine ⟨4450794172620668482837105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5934392230160891310449473 4450794172620668482837105)
                    ·
                      refine ⟨3338095629465501362127829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4450794172620668482837105 3338095629465501362127829)
                      ·
                        rfl

theorem cell23_6500918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 1, 2, 2, 2, 2].length) (baseStart_6500918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6500918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6500918 prefixEnd_6500918 := by exact prefixLift 6500918
  have htrace : WordTrace (prefixWord ++ tailWord_6500918) baseStart_6500918 baseEnd_6500918 := by
    simpa [prefixWord, tailWord_6500918, baseEnd_6500918] using wordTrace_append hprefix tailTrace_6500918
  have hstable : (prefixWord ++ tailWord_6500918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6500918).length < 2 ^ (prefixWord ++ tailWord_6500918).sum := by decide
  have hdescent : baseEnd_6500918 < baseStart_6500918 := by decide
  rcases family_descends (prefixWord ++ tailWord_6500918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6500934 : List Nat := [6, 1, 1, 1, 2, 1, 2, 1, 2, 3, 3]
def baseStart_6500934 : Nat := 118140960795 + 6500934 * 2 ^ 59
def prefixEnd_6500934 : Nat := 4983230072969 + 3 ^ 40 * 6500934 * 2
def baseEnd_6500934 : Nat := 3338103845155973299527755

theorem tailTrace_6500934 : CollatzResearch.WordTrace tailWord_6500934 prefixEnd_6500934 3338103845155973299527755 := by
  unfold tailWord_6500934
  simp only [CollatzResearch.WordTrace]
  refine ⟨7409641944694808249347183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 158072361486822575986073237 7409641944694808249347183)
  ·
    refine ⟨11114462917042212374020775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7409641944694808249347183 11114462917042212374020775)
    ·
      refine ⟨16671694375563318561031163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11114462917042212374020775 16671694375563318561031163)
      ·
        refine ⟨25007541563344977841546745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16671694375563318561031163 25007541563344977841546745)
        ·
          refine ⟨18755656172508733381160059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25007541563344977841546745 18755656172508733381160059)
          ·
            refine ⟨28133484258763100071740089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18755656172508733381160059 28133484258763100071740089)
            ·
              refine ⟨21100113194072325053805067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28133484258763100071740089 21100113194072325053805067)
              ·
                refine ⟨31650169791108487580707601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21100113194072325053805067 31650169791108487580707601)
                ·
                  refine ⟨23737627343331365685530701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31650169791108487580707601 23737627343331365685530701)
                  ·
                    refine ⟨8901610253749262132074013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23737627343331365685530701 8901610253749262132074013)
                    ·
                      refine ⟨3338103845155973299527755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8901610253749262132074013 3338103845155973299527755)
                      ·
                        rfl

theorem cell23_6500934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 1, 2, 3, 3].length) (baseStart_6500934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6500934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6500934 prefixEnd_6500934 := by exact prefixLift 6500934
  have htrace : WordTrace (prefixWord ++ tailWord_6500934) baseStart_6500934 baseEnd_6500934 := by
    simpa [prefixWord, tailWord_6500934, baseEnd_6500934] using wordTrace_append hprefix tailTrace_6500934
  have hstable : (prefixWord ++ tailWord_6500934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6500934).length < 2 ^ (prefixWord ++ tailWord_6500934).sum := by decide
  have hdescent : baseEnd_6500934 < baseStart_6500934 := by decide
  rcases family_descends (prefixWord ++ tailWord_6500934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6500960 : List Nat := [2, 1, 1, 3, 2, 1, 4, 1, 1, 4, 3]
def baseStart_6500960 : Nat := 118140960795 + 6500960 * 2 ^ 59
def prefixEnd_6500960 : Nat := 4983230072969 + 3 ^ 40 * 6500960 * 2
def baseEnd_6500960 : Nat := 3338117195652990197802635

theorem tailTrace_6500960 : CollatzResearch.WordTrace tailWord_6500960 prefixEnd_6500960 3338117195652990197802635 := by
  unfold tailWord_6500960
  simp only [CollatzResearch.WordTrace]
  refine ⟨118554745264069835209778167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158072993685426446946370889 118554745264069835209778167)
  ·
    refine ⟨177832117896104752814667251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118554745264069835209778167 177832117896104752814667251)
    ·
      refine ⟨266748176844157129222000877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177832117896104752814667251 266748176844157129222000877)
      ·
        refine ⟨100030566316558923458250329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 266748176844157129222000877 100030566316558923458250329)
        ·
          refine ⟨75022924737419192593687747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100030566316558923458250329 75022924737419192593687747)
          ·
            refine ⟨112534387106128788890531621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75022924737419192593687747 112534387106128788890531621)
            ·
              refine ⟨21100197582399147916974679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 112534387106128788890531621 21100197582399147916974679)
              ·
                refine ⟨31650296373598721875462019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21100197582399147916974679 31650296373598721875462019)
                ·
                  refine ⟨47475444560398082813193029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31650296373598721875462019 47475444560398082813193029)
                  ·
                    refine ⟨8901645855074640527473693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47475444560398082813193029 8901645855074640527473693)
                    ·
                      refine ⟨3338117195652990197802635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8901645855074640527473693 3338117195652990197802635)
                      ·
                        rfl

theorem cell23_6500960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 1, 1, 4, 3].length) (baseStart_6500960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6500960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6500960 prefixEnd_6500960 := by exact prefixLift 6500960
  have htrace : WordTrace (prefixWord ++ tailWord_6500960) baseStart_6500960 baseEnd_6500960 := by
    simpa [prefixWord, tailWord_6500960, baseEnd_6500960] using wordTrace_append hprefix tailTrace_6500960
  have hstable : (prefixWord ++ tailWord_6500960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6500960).length < 2 ^ (prefixWord ++ tailWord_6500960).sum := by decide
  have hdescent : baseEnd_6500960 < baseStart_6500960 := by decide
  rcases family_descends (prefixWord ++ tailWord_6500960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6500963 : List Nat := [1, 1, 1, 5, 1, 2, 1, 1, 10]
def baseStart_6500963 : Nat := 118140960795 + 6500963 * 2 ^ 59
def prefixEnd_6500963 : Nat := 4983230072969 + 3 ^ 40 * 6500963 * 2
def baseEnd_6500963 : Nat := 370902081788328187340569

theorem tailTrace_6500963 : CollatzResearch.WordTrace tailWord_6500963 prefixEnd_6500963 370902081788328187340569 := by
  unfold tailWord_6500963
  simp only [CollatzResearch.WordTrace]
  refine ⟨237109599947128801931915543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158073066631419201287943695 237109599947128801931915543)
  ·
    refine ⟨355664399920693202897873315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237109599947128801931915543 355664399920693202897873315)
    ·
      refine ⟨533496599881039804346809973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 355664399920693202897873315 533496599881039804346809973)
      ·
        refine ⟨50015306238847481657513435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 533496599881039804346809973 50015306238847481657513435)
        ·
          refine ⟨75022959358271222486270153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50015306238847481657513435 75022959358271222486270153)
          ·
            refine ⟨56267219518703416864702615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75022959358271222486270153 56267219518703416864702615)
            ·
              refine ⟨84400829278055125297053923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56267219518703416864702615 84400829278055125297053923)
              ·
                refine ⟨126601243917082687945580885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84400829278055125297053923 126601243917082687945580885)
                ·
                  refine ⟨370902081788328187340569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 126601243917082687945580885 370902081788328187340569)
                  ·
                    rfl

theorem cell23_6500963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 1, 10].length) (baseStart_6500963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6500963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6500963 prefixEnd_6500963 := by exact prefixLift 6500963
  have htrace : WordTrace (prefixWord ++ tailWord_6500963) baseStart_6500963 baseEnd_6500963 := by
    simpa [prefixWord, tailWord_6500963, baseEnd_6500963] using wordTrace_append hprefix tailTrace_6500963
  have hstable : (prefixWord ++ tailWord_6500963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6500963).length < 2 ^ (prefixWord ++ tailWord_6500963).sum := by decide
  have hdescent : baseEnd_6500963 < baseStart_6500963 := by decide
  rcases family_descends (prefixWord ++ tailWord_6500963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6500983 : List Nat := [1, 1, 3, 1, 1, 3, 2, 1, 1, 1, 8]
def baseStart_6500983 : Nat := 118140960795 + 6500983 * 2 ^ 59
def prefixEnd_6500983 : Nat := 4983230072969 + 3 ^ 40 * 6500983 * 2
def baseEnd_6500983 : Nat := 3338129005708043607815029

theorem tailTrace_6500983 : CollatzResearch.WordTrace tailWord_6500983 prefixEnd_6500983 3338129005708043607815029 := by
  unfold tailWord_6500983
  simp only [CollatzResearch.WordTrace]
  refine ⟨237110329407056345347643603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158073552938037563565095735 237110329407056345347643603)
  ·
    refine ⟨355665494110584518021465405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237110329407056345347643603 355665494110584518021465405)
    ·
      refine ⟨133374560291469194258049527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 355665494110584518021465405 133374560291469194258049527)
      ·
        refine ⟨200061840437203791387074291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133374560291469194258049527 200061840437203791387074291)
        ·
          refine ⟨300092760655805687080611437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200061840437203791387074291 300092760655805687080611437)
          ·
            refine ⟨112534785245927132655229289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 300092760655805687080611437 112534785245927132655229289)
            ·
              refine ⟨84401088934445349491421967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112534785245927132655229289 84401088934445349491421967)
              ·
                refine ⟨126601633401668024237132951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84401088934445349491421967 126601633401668024237132951)
                ·
                  refine ⟨189902450102502036355699427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 126601633401668024237132951 189902450102502036355699427)
                  ·
                    refine ⟨284853675153753054533549141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 189902450102502036355699427 284853675153753054533549141)
                    ·
                      refine ⟨3338129005708043607815029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 284853675153753054533549141 3338129005708043607815029)
                      ·
                        rfl

theorem cell23_6500983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 1, 1, 1, 8].length) (baseStart_6500983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6500983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6500983 prefixEnd_6500983 := by exact prefixLift 6500983
  have htrace : WordTrace (prefixWord ++ tailWord_6500983) baseStart_6500983 baseEnd_6500983 := by
    simpa [prefixWord, tailWord_6500983, baseEnd_6500983] using wordTrace_append hprefix tailTrace_6500983
  have hstable : (prefixWord ++ tailWord_6500983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6500983).length < 2 ^ (prefixWord ++ tailWord_6500983).sum := by decide
  have hdescent : baseEnd_6500983 < baseStart_6500983 := by decide
  rcases family_descends (prefixWord ++ tailWord_6500983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6500997 : List Nat := [1, 3, 1, 1, 4, 2, 4, 1, 6]
def baseStart_6500997 : Nat := 118140960795 + 6500997 * 2 ^ 59
def prefixEnd_6500997 : Nat := 4983230072969 + 3 ^ 40 * 6500997 * 2
def baseEnd_6500997 : Nat := 370904021604134061448885

theorem tailTrace_6500997 : CollatzResearch.WordTrace tailWord_6500997 prefixEnd_6500997 370904021604134061448885 := by
  unfold tailWord_6500997
  simp only [CollatzResearch.WordTrace]
  refine ⟨237110840029005625738653245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158073893352670417159102163 237110840029005625738653245)
  ·
    refine ⟨88916565010877109651994967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 237110840029005625738653245 88916565010877109651994967)
    ·
      refine ⟨133374847516315664477992451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88916565010877109651994967 133374847516315664477992451)
      ·
        refine ⟨200062271274473496716988677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133374847516315664477992451 200062271274473496716988677)
        ·
          refine ⟨37511675863963780634435377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 200062271274473496716988677 37511675863963780634435377)
          ·
            refine ⟨28133756897972835475826533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37511675863963780634435377 28133756897972835475826533)
            ·
              refine ⟨5275079418369906651717475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28133756897972835475826533 5275079418369906651717475)
              ·
                refine ⟨7912619127554859977576213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5275079418369906651717475 7912619127554859977576213)
                ·
                  refine ⟨370904021604134061448885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7912619127554859977576213 370904021604134061448885)
                  ·
                    rfl

theorem cell23_6500997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 4, 1, 6].length) (baseStart_6500997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6500997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6500997 prefixEnd_6500997 := by exact prefixLift 6500997
  have htrace : WordTrace (prefixWord ++ tailWord_6500997) baseStart_6500997 baseEnd_6500997 := by
    simpa [prefixWord, tailWord_6500997, baseEnd_6500997] using wordTrace_append hprefix tailTrace_6500997
  have hstable : (prefixWord ++ tailWord_6500997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6500997).length < 2 ^ (prefixWord ++ tailWord_6500997).sum := by decide
  have hdescent : baseEnd_6500997 < baseStart_6500997 := by decide
  rcases family_descends (prefixWord ++ tailWord_6500997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6501003 : List Nat := [1, 1, 1, 1, 4, 1, 2, 1, 1, 3, 7]
def baseStart_6501003 : Nat := 118140960795 + 6501003 * 2 ^ 59
def prefixEnd_6501003 : Nat := 4983230072969 + 3 ^ 40 * 6501003 * 2
def baseEnd_6501003 : Nat := 3338139275321133529564937

theorem tailTrace_6501003 : CollatzResearch.WordTrace tailWord_6501003 prefixEnd_6501003 3338139275321133529564937 := by
  unfold tailWord_6501003
  simp only [CollatzResearch.WordTrace]
  refine ⟨237111058866983888763371663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158074039244655925842247775 237111058866983888763371663)
  ·
    refine ⟨355666588300475833145057495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237111058866983888763371663 355666588300475833145057495)
    ·
      refine ⟨533499882450713749717586243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 355666588300475833145057495 533499882450713749717586243)
      ·
        refine ⟨800249823676070624576379365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 533499882450713749717586243 800249823676070624576379365)
        ·
          refine ⟨150046841939263242108071131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 800249823676070624576379365 150046841939263242108071131)
          ·
            refine ⟨225070262908894863162106697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150046841939263242108071131 225070262908894863162106697)
            ·
              refine ⟨168802697181671147371580023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 225070262908894863162106697 168802697181671147371580023)
              ·
                refine ⟨253204045772506721057370035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 168802697181671147371580023 253204045772506721057370035)
                ·
                  refine ⟨379806068658760081586055053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 253204045772506721057370035 379806068658760081586055053)
                  ·
                    refine ⟨142427275747035030594770645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 379806068658760081586055053 142427275747035030594770645)
                    ·
                      refine ⟨3338139275321133529564937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 142427275747035030594770645 3338139275321133529564937)
                      ·
                        rfl

theorem cell23_6501003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 3, 7].length) (baseStart_6501003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6501003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6501003 prefixEnd_6501003 := by exact prefixLift 6501003
  have htrace : WordTrace (prefixWord ++ tailWord_6501003) baseStart_6501003 baseEnd_6501003 := by
    simpa [prefixWord, tailWord_6501003, baseEnd_6501003] using wordTrace_append hprefix tailTrace_6501003
  have hstable : (prefixWord ++ tailWord_6501003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6501003).length < 2 ^ (prefixWord ++ tailWord_6501003).sum := by decide
  have hdescent : baseEnd_6501003 < baseStart_6501003 := by decide
  rcases family_descends (prefixWord ++ tailWord_6501003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6501050 : List Nat := [3, 1, 1, 1, 2, 3, 2, 1, 3, 1, 5]
def baseStart_6501050 : Nat := 118140960795 + 6501050 * 2 ^ 59
def prefixEnd_6501050 : Nat := 4983230072969 + 3 ^ 40 * 6501050 * 2
def baseEnd_6501050 : Nat := 3338163408911894845677221

theorem tailTrace_6501050 : CollatzResearch.WordTrace tailWord_6501050 prefixEnd_6501050 3338163408911894845677221 := by
  unfold tailWord_6501050
  simp only [CollatzResearch.WordTrace]
  refine ⟨59278193274453403947583151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158075182065209077193555069 59278193274453403947583151)
  ·
    refine ⟨88917289911680105921374727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59278193274453403947583151 88917289911680105921374727)
    ·
      refine ⟨133375934867520158882062091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88917289911680105921374727 133375934867520158882062091)
      ·
        refine ⟨200063902301280238323093137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133375934867520158882062091 200063902301280238323093137)
        ·
          refine ⟨150047926725960178742319853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 200063902301280238323093137 150047926725960178742319853)
          ·
            refine ⟨56267972522235067028369945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 150047926725960178742319853 56267972522235067028369945)
            ·
              refine ⟨42200979391676300271277459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56267972522235067028369945 42200979391676300271277459)
              ·
                refine ⟨63301469087514450406916189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42200979391676300271277459 63301469087514450406916189)
                ·
                  refine ⟨23738050907817918902593571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63301469087514450406916189 23738050907817918902593571)
                  ·
                    refine ⟨35607076361726878353890357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23738050907817918902593571 35607076361726878353890357)
                    ·
                      refine ⟨3338163408911894845677221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35607076361726878353890357 3338163408911894845677221)
                      ·
                        rfl

theorem cell23_6501050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 1, 3, 1, 5].length) (baseStart_6501050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6501050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6501050 prefixEnd_6501050 := by exact prefixLift 6501050
  have htrace : WordTrace (prefixWord ++ tailWord_6501050) baseStart_6501050 baseEnd_6501050 := by
    simpa [prefixWord, tailWord_6501050, baseEnd_6501050] using wordTrace_append hprefix tailTrace_6501050
  have hstable : (prefixWord ++ tailWord_6501050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6501050).length < 2 ^ (prefixWord ++ tailWord_6501050).sum := by decide
  have hdescent : baseEnd_6501050 < baseStart_6501050 := by decide
  rcases family_descends (prefixWord ++ tailWord_6501050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6501064 : List Nat := [2, 1, 3, 1, 2, 3, 1, 1, 5, 2, 2]
def baseStart_6501064 : Nat := 118140960795 + 6501064 * 2 ^ 59
def prefixEnd_6501064 : Nat := 4983230072969 + 3 ^ 40 * 6501064 * 2
def baseEnd_6501064 : Nat := 3338170597641057790902157

theorem tailTrace_6501064 : CollatzResearch.WordTrace tailWord_6501064 prefixEnd_6501064 3338170597641057790902157 := by
  unfold tailWord_6501064
  simp only [CollatzResearch.WordTrace]
  refine ⟨118556641859881448090671123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158075522479841930787561497 118556641859881448090671123)
  ·
    refine ⟨177834962789822172136006685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118556641859881448090671123 177834962789822172136006685)
    ·
      refine ⟨66688111046183314551002507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177834962789822172136006685 66688111046183314551002507)
      ·
        refine ⟨100032166569274971826503761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66688111046183314551002507 100032166569274971826503761)
        ·
          refine ⟨75024124926956228869877821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100032166569274971826503761 75024124926956228869877821)
          ·
            refine ⟨28134046847608585826204183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75024124926956228869877821 28134046847608585826204183)
            ·
              refine ⟨42201070271412878739306275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28134046847608585826204183 42201070271412878739306275)
              ·
                refine ⟨63301605407119318108959413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42201070271412878739306275 63301605407119318108959413)
                ·
                  refine ⟨5934525506917436072714945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 63301605407119318108959413 5934525506917436072714945)
                  ·
                    refine ⟨4450894130188077054536209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5934525506917436072714945 4450894130188077054536209)
                    ·
                      refine ⟨3338170597641057790902157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4450894130188077054536209 3338170597641057790902157)
                      ·
                        rfl

theorem cell23_6501064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 1, 5, 2, 2].length) (baseStart_6501064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6501064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6501064 prefixEnd_6501064 := by exact prefixLift 6501064
  have htrace : WordTrace (prefixWord ++ tailWord_6501064) baseStart_6501064 baseEnd_6501064 := by
    simpa [prefixWord, tailWord_6501064, baseEnd_6501064] using wordTrace_append hprefix tailTrace_6501064
  have hstable : (prefixWord ++ tailWord_6501064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6501064).length < 2 ^ (prefixWord ++ tailWord_6501064).sum := by decide
  have hdescent : baseEnd_6501064 < baseStart_6501064 := by decide
  rcases family_descends (prefixWord ++ tailWord_6501064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6501091 : List Nat := [1, 1, 1, 7, 1, 3, 1, 2, 2, 4]
def baseStart_6501091 : Nat := 118140960795 + 6501091 * 2 ^ 59
def prefixEnd_6501091 : Nat := 4983230072969 + 3 ^ 40 * 6501091 * 2
def baseEnd_6501091 : Nat := 1112728153872909728421511

theorem tailTrace_6501091 : CollatzResearch.WordTrace tailWord_6501091 prefixEnd_6501091 1112728153872909728421511 := by
  unfold tailWord_6501091
  simp only [CollatzResearch.WordTrace]
  refine ⟨237114268490665079792575127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158076178993776719861716751 237114268490665079792575127)
  ·
    refine ⟨355671402735997619688862691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237114268490665079792575127 355671402735997619688862691)
    ·
      refine ⟨533507104103996429533294037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 355671402735997619688862691 533507104103996429533294037)
      ·
        refine ⟨12504072752437416317186579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 533507104103996429533294037 12504072752437416317186579)
        ·
          refine ⟨18756109128656124475779869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12504072752437416317186579 18756109128656124475779869)
          ·
            refine ⟨7033540923246046678417451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18756109128656124475779869 7033540923246046678417451)
            ·
              refine ⟨10550311384869070017626177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7033540923246046678417451 10550311384869070017626177)
              ·
                refine ⟨7912733538651802513219633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10550311384869070017626177 7912733538651802513219633)
                ·
                  refine ⟨5934550153988851884914725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7912733538651802513219633 5934550153988851884914725)
                  ·
                    refine ⟨1112728153872909728421511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5934550153988851884914725 1112728153872909728421511)
                    ·
                      rfl

theorem cell23_6501091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 1, 2, 2, 4].length) (baseStart_6501091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6501091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6501091 prefixEnd_6501091 := by exact prefixLift 6501091
  have htrace : WordTrace (prefixWord ++ tailWord_6501091) baseStart_6501091 baseEnd_6501091 := by
    simpa [prefixWord, tailWord_6501091, baseEnd_6501091] using wordTrace_append hprefix tailTrace_6501091
  have hstable : (prefixWord ++ tailWord_6501091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6501091).length < 2 ^ (prefixWord ++ tailWord_6501091).sum := by decide
  have hdescent : baseEnd_6501091 < baseStart_6501091 := by decide
  rcases family_descends (prefixWord ++ tailWord_6501091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6501108 : List Nat := [2, 6, 1, 1, 2, 2, 1, 1, 1, 6]
def baseStart_6501108 : Nat := 118140960795 + 6501108 * 2 ^ 59
def prefixEnd_6501108 : Nat := 4983230072969 + 3 ^ 40 * 6501108 * 2
def baseEnd_6501108 : Nat := 1112731063596618539583985

theorem tailTrace_6501108 : CollatzResearch.WordTrace tailWord_6501108 prefixEnd_6501108 1112731063596618539583985 := by
  unfold tailWord_6501108
  simp only [CollatzResearch.WordTrace]
  refine ⟨118557444265801745847971989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158076592354402327797295985 118557444265801745847971989)
  ·
    refine ⟨5557380199959456836623687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 118557444265801745847971989 5557380199959456836623687)
    ·
      refine ⟨8336070299939185254935531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5557380199959456836623687 8336070299939185254935531)
      ·
        refine ⟨12504105449908777882403297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8336070299939185254935531 12504105449908777882403297)
        ·
          refine ⟨9378079087431583411802473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12504105449908777882403297 9378079087431583411802473)
          ·
            refine ⟨7033559315573687558851855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9378079087431583411802473 7033559315573687558851855)
            ·
              refine ⟨10550338973360531338277783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7033559315573687558851855 10550338973360531338277783)
              ·
                refine ⟨15825508460040797007416675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10550338973360531338277783 15825508460040797007416675)
                ·
                  refine ⟨23738262690061195511125013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15825508460040797007416675 23738262690061195511125013)
                  ·
                    refine ⟨1112731063596618539583985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23738262690061195511125013 1112731063596618539583985)
                    ·
                      rfl

theorem cell23_6501108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_6501108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6501108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6501108 prefixEnd_6501108 := by exact prefixLift 6501108
  have htrace : WordTrace (prefixWord ++ tailWord_6501108) baseStart_6501108 baseEnd_6501108 := by
    simpa [prefixWord, tailWord_6501108, baseEnd_6501108] using wordTrace_append hprefix tailTrace_6501108
  have hstable : (prefixWord ++ tailWord_6501108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6501108).length < 2 ^ (prefixWord ++ tailWord_6501108).sum := by decide
  have hdescent : baseEnd_6501108 < baseStart_6501108 := by decide
  rcases family_descends (prefixWord ++ tailWord_6501108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6501114 : List Nat := [3, 1, 1, 1, 1, 3, 2, 5, 2, 1, 3]
def baseStart_6501114 : Nat := 118140960795 + 6501114 * 2 ^ 59
def prefixEnd_6501114 : Nat := 4983230072969 + 3 ^ 40 * 6501114 * 2
def baseEnd_6501114 : Nat := 3338196271673782595276927

theorem tailTrace_6501114 : CollatzResearch.WordTrace tailWord_6501114 prefixEnd_6501114 3338196271673782595276927 := by
  unfold tailWord_6501114
  simp only [CollatzResearch.WordTrace]
  refine ⟨59278776842395438680165599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158076738246387836480441597 59278776842395438680165599)
  ·
    refine ⟨88918165263593158020248399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59278776842395438680165599 88918165263593158020248399)
    ·
      refine ⟨133377247895389737030372599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88918165263593158020248399 133377247895389737030372599)
      ·
        refine ⟨200065871843084605545558899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133377247895389737030372599 200065871843084605545558899)
        ·
          refine ⟨300098807764626908318338349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200065871843084605545558899 300098807764626908318338349)
          ·
            refine ⟨112537052911735090619376881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 300098807764626908318338349 112537052911735090619376881)
            ·
              refine ⟨84402789683801317964532661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112537052911735090619376881 84402789683801317964532661)
              ·
                refine ⟨7912761532856373559174937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 84402789683801317964532661 7912761532856373559174937)
                ·
                  refine ⟨5934571149642280169381203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7912761532856373559174937 5934571149642280169381203)
                  ·
                    refine ⟨8901856724463420254071805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5934571149642280169381203 8901856724463420254071805)
                    ·
                      refine ⟨3338196271673782595276927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8901856724463420254071805 3338196271673782595276927)
                      ·
                        rfl

theorem cell23_6501114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 5, 2, 1, 3].length) (baseStart_6501114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6501114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6501114 prefixEnd_6501114 := by exact prefixLift 6501114
  have htrace : WordTrace (prefixWord ++ tailWord_6501114) baseStart_6501114 baseEnd_6501114 := by
    simpa [prefixWord, tailWord_6501114, baseEnd_6501114] using wordTrace_append hprefix tailTrace_6501114
  have hstable : (prefixWord ++ tailWord_6501114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6501114).length < 2 ^ (prefixWord ++ tailWord_6501114).sum := by decide
  have hdescent : baseEnd_6501114 < baseStart_6501114 := by decide
  rcases family_descends (prefixWord ++ tailWord_6501114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6501127 : List Nat := [1, 1, 4, 4, 1, 1, 1, 1, 2, 2, 5]
def baseStart_6501127 : Nat := 118140960795 + 6501127 * 2 ^ 59
def prefixEnd_6501127 : Nat := 4983230072969 + 3 ^ 40 * 6501127 * 2
def baseEnd_6501127 : Nat := 3338202946922291044414367

theorem tailTrace_6501127 : CollatzResearch.WordTrace tailWord_6501127 prefixEnd_6501127 3338202946922291044414367 := by
  unfold tailWord_6501127
  simp only [CollatzResearch.WordTrace]
  refine ⟨237115581518534657940885635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158077054345689771960590423 237115581518534657940885635)
  ·
    refine ⟨355673372277801986911328453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237115581518534657940885635 355673372277801986911328453)
    ·
      refine ⟨66688757302087872545874085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 355673372277801986911328453 66688757302087872545874085)
      ·
        refine ⟨12504141994141476102351391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66688757302087872545874085 12504141994141476102351391)
        ·
          refine ⟨18756212991212214153527087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12504141994141476102351391 18756212991212214153527087)
          ·
            refine ⟨28134319486818321230290631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18756212991212214153527087 28134319486818321230290631)
            ·
              refine ⟨42201479230227481845435947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28134319486818321230290631 42201479230227481845435947)
              ·
                refine ⟨63302218845341222768153921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42201479230227481845435947 63302218845341222768153921)
                ·
                  refine ⟨47476664134005917076115441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63302218845341222768153921 47476664134005917076115441)
                  ·
                    refine ⟨35607498100504437807086581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47476664134005917076115441 35607498100504437807086581)
                    ·
                      refine ⟨3338202946922291044414367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35607498100504437807086581 3338202946922291044414367)
                      ·
                        rfl

theorem cell23_6501127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_6501127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6501127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6501127 prefixEnd_6501127 := by exact prefixLift 6501127
  have htrace : WordTrace (prefixWord ++ tailWord_6501127) baseStart_6501127 baseEnd_6501127 := by
    simpa [prefixWord, tailWord_6501127, baseEnd_6501127] using wordTrace_append hprefix tailTrace_6501127
  have hstable : (prefixWord ++ tailWord_6501127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6501127).length < 2 ^ (prefixWord ++ tailWord_6501127).sum := by decide
  have hdescent : baseEnd_6501127 < baseStart_6501127 := by decide
  rcases family_descends (prefixWord ++ tailWord_6501127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6501157 : List Nat := [1, 3, 1, 2, 3, 1, 2, 1, 2, 4, 3]
def baseStart_6501157 : Nat := 118140960795 + 6501157 * 2 ^ 59
def prefixEnd_6501157 : Nat := 4983230072969 + 3 ^ 40 * 6501157 * 2
def baseEnd_6501157 : Nat := 3338218351341925927039229

theorem tailTrace_6501157 : CollatzResearch.WordTrace tailWord_6501157 prefixEnd_6501157 3338218351341925927039229 := by
  unfold tailWord_6501157
  simp only [CollatzResearch.WordTrace]
  refine ⟨237116675708425973064477725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158077783805617315376318483 237116675708425973064477725)
  ·
    refine ⟨88918753390659739899179147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 237116675708425973064477725 88918753390659739899179147)
    ·
      refine ⟨133378130085989609848768721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88918753390659739899179147 133378130085989609848768721)
      ·
        refine ⟨100033597564492207386576541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133378130085989609848768721 100033597564492207386576541)
        ·
          refine ⟨37512599086684577769966203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100033597564492207386576541 37512599086684577769966203)
          ·
            refine ⟨56268898630026866654949305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37512599086684577769966203 56268898630026866654949305)
            ·
              refine ⟨42201673972520149991211979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56268898630026866654949305 42201673972520149991211979)
              ·
                refine ⟨63302510958780224986817969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42201673972520149991211979 63302510958780224986817969)
                ·
                  refine ⟨47476883219085168740113477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63302510958780224986817969 47476883219085168740113477)
                  ·
                    refine ⟨8901915603578469138771277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47476883219085168740113477 8901915603578469138771277)
                    ·
                      refine ⟨3338218351341925927039229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8901915603578469138771277 3338218351341925927039229)
                      ·
                        rfl

theorem cell23_6501157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 1, 2, 4, 3].length) (baseStart_6501157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6501157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6501157 prefixEnd_6501157 := by exact prefixLift 6501157
  have htrace : WordTrace (prefixWord ++ tailWord_6501157) baseStart_6501157 baseEnd_6501157 := by
    simpa [prefixWord, tailWord_6501157, baseEnd_6501157] using wordTrace_append hprefix tailTrace_6501157
  have hstable : (prefixWord ++ tailWord_6501157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6501157).length < 2 ^ (prefixWord ++ tailWord_6501157).sum := by decide
  have hdescent : baseEnd_6501157 < baseStart_6501157 := by decide
  rcases family_descends (prefixWord ++ tailWord_6501157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6501165 : List Nat := [1, 5, 3, 2, 1, 1, 1, 3, 2, 1, 3]
def baseStart_6501165 : Nat := 118140960795 + 6501165 * 2 ^ 59
def prefixEnd_6501165 : Nat := 4983230072969 + 3 ^ 40 * 6501165 * 2
def baseEnd_6501165 : Nat := 3338222459187161895739193

theorem tailTrace_6501165 : CollatzResearch.WordTrace tailWord_6501165 prefixEnd_6501165 3338222459187161895739193 := by
  unfold tailWord_6501165
  simp only [CollatzResearch.WordTrace]
  refine ⟨237116967492396990430768949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158077978328264660287179299 237116967492396990430768949)
  ·
    refine ⟨22229715702412217852884589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 237116967492396990430768949 22229715702412217852884589)
    ·
      refine ⟨8336143388404581694831721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22229715702412217852884589 8336143388404581694831721)
      ·
        refine ⟨6252107541303436271123791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8336143388404581694831721 6252107541303436271123791)
        ·
          refine ⟨9378161311955154406685687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6252107541303436271123791 9378161311955154406685687)
          ·
            refine ⟨14067241967932731610028531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9378161311955154406685687 14067241967932731610028531)
            ·
              refine ⟨21100862951899097415042797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14067241967932731610028531 21100862951899097415042797)
              ·
                refine ⟨7912823606962161530641049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21100862951899097415042797 7912823606962161530641049)
                ·
                  refine ⟨5934617705221621147980787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7912823606962161530641049 5934617705221621147980787)
                  ·
                    refine ⟨8901926557832431721971181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5934617705221621147980787 8901926557832431721971181)
                    ·
                      refine ⟨3338222459187161895739193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8901926557832431721971181 3338222459187161895739193)
                      ·
                        rfl

theorem cell23_6501165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_6501165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6501165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6501165 prefixEnd_6501165 := by exact prefixLift 6501165
  have htrace : WordTrace (prefixWord ++ tailWord_6501165) baseStart_6501165 baseEnd_6501165 := by
    simpa [prefixWord, tailWord_6501165, baseEnd_6501165] using wordTrace_append hprefix tailTrace_6501165
  have hstable : (prefixWord ++ tailWord_6501165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6501165).length < 2 ^ (prefixWord ++ tailWord_6501165).sum := by decide
  have hdescent : baseEnd_6501165 < baseStart_6501165 := by decide
  rcases family_descends (prefixWord ++ tailWord_6501165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6501227 : List Nat := [1, 1, 1, 1, 2, 2, 4, 2, 4, 1, 4]
def baseStart_6501227 : Nat := 118140960795 + 6501227 * 2 ^ 59
def prefixEnd_6501227 : Nat := 4983230072969 + 3 ^ 40 * 6501227 * 2
def baseEnd_6501227 : Nat := 3338254294987740653163907

theorem tailTrace_6501227 : CollatzResearch.WordTrace tailWord_6501227 prefixEnd_6501227 3338254294987740653163907 := by
  unfold tailWord_6501227
  simp only [CollatzResearch.WordTrace]
  refine ⟨237119228818172375019525935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158079485878781583346350623 237119228818172375019525935)
  ·
    refine ⟨355678843227258562529288903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237119228818172375019525935 355678843227258562529288903)
    ·
      refine ⟨533518264840887843793933355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 355678843227258562529288903 533518264840887843793933355)
      ·
        refine ⟨800277397261331765690900033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 533518264840887843793933355 800277397261331765690900033)
        ·
          refine ⟨600208047945998824268175025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 800277397261331765690900033 600208047945998824268175025)
          ·
            refine ⟨450156035959499118201131269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 600208047945998824268175025 450156035959499118201131269)
            ·
              refine ⟨84404256742406084662712113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 450156035959499118201131269 84404256742406084662712113)
              ·
                refine ⟨63303192556804563497034085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84404256742406084662712113 63303192556804563497034085)
                ·
                  refine ⟨11869348604400855655693891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63303192556804563497034085 11869348604400855655693891)
                  ·
                    refine ⟨17804022906601283483540837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11869348604400855655693891 17804022906601283483540837)
                    ·
                      refine ⟨3338254294987740653163907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17804022906601283483540837 3338254294987740653163907)
                      ·
                        rfl

theorem cell23_6501227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 2, 4, 1, 4].length) (baseStart_6501227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6501227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6501227 prefixEnd_6501227 := by exact prefixLift 6501227
  have htrace : WordTrace (prefixWord ++ tailWord_6501227) baseStart_6501227 baseEnd_6501227 := by
    simpa [prefixWord, tailWord_6501227, baseEnd_6501227] using wordTrace_append hprefix tailTrace_6501227
  have hstable : (prefixWord ++ tailWord_6501227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6501227).length < 2 ^ (prefixWord ++ tailWord_6501227).sum := by decide
  have hdescent : baseEnd_6501227 < baseStart_6501227 := by decide
  rcases family_descends (prefixWord ++ tailWord_6501227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
