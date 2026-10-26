import V185TrunkScan20Chunk113

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_693192 : List Nat := [2, 1, 3, 1, 6, 1, 2, 1, 3]
def baseStart_693192 : Nat := 118140960795 + 693192 * 2 ^ 59
def prefixEnd_693192 : Nat := 4983230072969 + 3 ^ 40 * 693192 * 2
def baseEnd_693192 : Nat := 316391717201384103832955

theorem tailTrace_693192 : CollatzResearch.WordTrace tailWord_693192 prefixEnd_693192 316391717201384103832955 := by
  unfold tailWord_693192
  simp only [CollatzResearch.WordTrace]
  refine ⟨12641394652345623306688915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16855192869794164408918553 12641394652345623306688915)
  ·
    refine ⟨18962091978518434960033373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12641394652345623306688915 18962091978518434960033373)
    ·
      refine ⟨7110784491944413110012515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18962091978518434960033373 7110784491944413110012515)
      ·
        refine ⟨10666176737916619665018773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7110784491944413110012515 10666176737916619665018773)
        ·
          refine ⟨499977034589841546797755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 10666176737916619665018773 499977034589841546797755)
          ·
            refine ⟨749965551884762320196633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 499977034589841546797755 749965551884762320196633)
            ·
              refine ⟨562474163913571740147475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 749965551884762320196633 562474163913571740147475)
              ·
                refine ⟨843711245870357610221213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 562474163913571740147475 843711245870357610221213)
                ·
                  refine ⟨316391717201384103832955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 843711245870357610221213 316391717201384103832955)
                  ·
                    rfl

theorem cell20_693192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 2, 1, 3].length) (baseStart_693192 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_693192 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_693192 prefixEnd_693192 := by exact prefixLift 693192
  have htrace : WordTrace (prefixWord ++ tailWord_693192) baseStart_693192 baseEnd_693192 := by
    simpa [prefixWord, tailWord_693192, baseEnd_693192] using wordTrace_append hprefix tailTrace_693192
  have hstable : (prefixWord ++ tailWord_693192).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693192).length < 2 ^ (prefixWord ++ tailWord_693192).sum := by decide
  have hdescent : baseEnd_693192 < baseStart_693192 := by decide
  rcases family_descends (prefixWord ++ tailWord_693192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693241 : List Nat := [1, 2, 1, 3, 1, 3, 3, 4, 2]
def baseStart_693241 : Nat := 118140960795 + 693241 * 2 ^ 59
def prefixEnd_693241 : Nat := 4983230072969 + 3 ^ 40 * 693241 * 2
def baseEnd_693241 : Nat := 316414082136557711199421

theorem tailTrace_693241 : CollatzResearch.WordTrace tailWord_693241 prefixEnd_693241 316414082136557711199421 := by
  unfold tailWord_693241
  simp only [CollatzResearch.WordTrace]
  refine ⟨25284576481513727981911577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16856384321009151987941051 25284576481513727981911577)
  ·
    refine ⟨18963432361135295986433683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25284576481513727981911577 18963432361135295986433683)
    ·
      refine ⟨28445148541702943979650525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18963432361135295986433683 28445148541702943979650525)
      ·
        refine ⟨10666930703138603992368947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28445148541702943979650525 10666930703138603992368947)
        ·
          refine ⟨16000396054707905988553421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10666930703138603992368947 16000396054707905988553421)
          ·
            refine ⟨6000148520515464745707533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16000396054707905988553421 6000148520515464745707533)
            ·
              refine ⟨2250055695193299279640325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6000148520515464745707533 2250055695193299279640325)
              ·
                refine ⟨421885442848743614932561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2250055695193299279640325 421885442848743614932561)
                ·
                  refine ⟨316414082136557711199421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 421885442848743614932561 316414082136557711199421)
                  ·
                    rfl

theorem cell20_693241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 4, 2].length) (baseStart_693241 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_693241 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_693241 prefixEnd_693241 := by exact prefixLift 693241
  have htrace : WordTrace (prefixWord ++ tailWord_693241) baseStart_693241 baseEnd_693241 := by
    simpa [prefixWord, tailWord_693241, baseEnd_693241] using wordTrace_append hprefix tailTrace_693241
  have hstable : (prefixWord ++ tailWord_693241).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693241).length < 2 ^ (prefixWord ++ tailWord_693241).sum := by decide
  have hdescent : baseEnd_693241 < baseStart_693241 := by decide
  rcases family_descends (prefixWord ++ tailWord_693241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693255 : List Nat := [1, 1, 4, 3, 1, 1, 1, 5, 3]
def baseStart_693255 : Nat := 118140960795 + 693255 * 2 ^ 59
def prefixEnd_693255 : Nat := 4983230072969 + 3 ^ 40 * 693255 * 2
def baseEnd_693255 : Nat := 316420472118035884732697

theorem tailTrace_693255 : CollatzResearch.WordTrace tailWord_693255 prefixEnd_693255 316420472118035884732697 := by
  unfold tailWord_693255
  simp only [CollatzResearch.WordTrace]
  refine ⟨25285087103463008372921219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16856724735642005581947479 25285087103463008372921219)
  ·
    refine ⟨37927630655194512559381829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25285087103463008372921219 37927630655194512559381829)
    ·
      refine ⟨7111430747848971104884093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37927630655194512559381829 7111430747848971104884093)
      ·
        refine ⟨2666786530443364164331535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7111430747848971104884093 2666786530443364164331535)
        ·
          refine ⟨4000179795665046246497303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2666786530443364164331535 4000179795665046246497303)
          ·
            refine ⟨6000269693497569369745955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4000179795665046246497303 6000269693497569369745955)
            ·
              refine ⟨9000404540246354054618933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6000269693497569369745955 9000404540246354054618933)
              ·
                refine ⟨843787925648095692620525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9000404540246354054618933 843787925648095692620525)
                ·
                  refine ⟨316420472118035884732697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 843787925648095692620525 316420472118035884732697)
                  ·
                    rfl

theorem cell20_693255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 5, 3].length) (baseStart_693255 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_693255 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_693255 prefixEnd_693255 := by exact prefixLift 693255
  have htrace : WordTrace (prefixWord ++ tailWord_693255) baseStart_693255 baseEnd_693255 := by
    simpa [prefixWord, tailWord_693255, baseEnd_693255] using wordTrace_append hprefix tailTrace_693255
  have hstable : (prefixWord ++ tailWord_693255).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693255).length < 2 ^ (prefixWord ++ tailWord_693255).sum := by decide
  have hdescent : baseEnd_693255 < baseStart_693255 := by decide
  rcases family_descends (prefixWord ++ tailWord_693255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693262 : List Nat := [4, 1, 1, 2, 2, 2, 1, 1, 6]
def baseStart_693262 : Nat := 118140960795 + 693262 * 2 ^ 59
def prefixEnd_693262 : Nat := 4983230072969 + 3 ^ 40 * 693262 * 2
def baseEnd_693262 : Nat := 316423667108774971499335

theorem tailTrace_693262 : CollatzResearch.WordTrace tailWord_693262 prefixEnd_693262 316423667108774971499335 := by
  unfold tailWord_693262
  simp only [CollatzResearch.WordTrace]
  refine ⟨3160667801804706071053255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16856894942958432378950693 3160667801804706071053255)
  ·
    refine ⟨4741001702707059106579883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3160667801804706071053255 4741001702707059106579883)
    ·
      refine ⟨7111502554060588659869825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4741001702707059106579883 7111502554060588659869825)
      ·
        refine ⟨5333626915545441494902369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7111502554060588659869825 5333626915545441494902369)
        ·
          refine ⟨4000220186659081121176777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5333626915545441494902369 4000220186659081121176777)
          ·
            refine ⟨3000165139994310840882583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4000220186659081121176777 3000165139994310840882583)
            ·
              refine ⟨4500247709991466261323875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3000165139994310840882583 4500247709991466261323875)
              ·
                refine ⟨6750371564987199391985813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4500247709991466261323875 6750371564987199391985813)
                ·
                  refine ⟨316423667108774971499335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6750371564987199391985813 316423667108774971499335)
                  ·
                    rfl

theorem cell20_693262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 1, 6].length) (baseStart_693262 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_693262 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_693262 prefixEnd_693262 := by exact prefixLift 693262
  have htrace : WordTrace (prefixWord ++ tailWord_693262) baseStart_693262 baseEnd_693262 := by
    simpa [prefixWord, tailWord_693262, baseEnd_693262] using wordTrace_append hprefix tailTrace_693262
  have hstable : (prefixWord ++ tailWord_693262).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693262).length < 2 ^ (prefixWord ++ tailWord_693262).sum := by decide
  have hdescent : baseEnd_693262 < baseStart_693262 := by decide
  rcases family_descends (prefixWord ++ tailWord_693262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693279 : List Nat := [1, 1, 2, 4, 1, 3, 1, 5, 2]
def baseStart_693279 : Nat := 118140960795 + 693279 * 2 ^ 59
def prefixEnd_693279 : Nat := 4983230072969 + 3 ^ 40 * 693279 * 2
def baseEnd_693279 : Nat := 316431426371998467932599

theorem tailTrace_693279 : CollatzResearch.WordTrace tailWord_693279 prefixEnd_693279 316431426371998467932599 := by
  unfold tailWord_693279
  simp only [CollatzResearch.WordTrace]
  refine ⟨25285962455376060471794891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16857308303584040314529927 25285962455376060471794891)
  ·
    refine ⟨37928943683064090707692337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25285962455376060471794891 37928943683064090707692337)
    ·
      refine ⟨28446707762298068030769253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37928943683064090707692337 28446707762298068030769253)
      ·
        refine ⟨5333757705430887755769235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28446707762298068030769253 5333757705430887755769235)
        ·
          refine ⟨8000636558146331633653853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5333757705430887755769235 8000636558146331633653853)
          ·
            refine ⟨3000238709304874362620195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8000636558146331633653853 3000238709304874362620195)
            ·
              refine ⟨4500358063957311543930293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3000238709304874362620195 4500358063957311543930293)
              ·
                refine ⟨421908568495997957243465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4500358063957311543930293 421908568495997957243465)
                ·
                  refine ⟨316431426371998467932599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 421908568495997957243465 316431426371998467932599)
                  ·
                    rfl

theorem cell20_693279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 5, 2].length) (baseStart_693279 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_693279 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_693279 prefixEnd_693279 := by exact prefixLift 693279
  have htrace : WordTrace (prefixWord ++ tailWord_693279) baseStart_693279 baseEnd_693279 := by
    simpa [prefixWord, tailWord_693279, baseEnd_693279] using wordTrace_append hprefix tailTrace_693279
  have hstable : (prefixWord ++ tailWord_693279).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693279).length < 2 ^ (prefixWord ++ tailWord_693279).sum := by decide
  have hdescent : baseEnd_693279 < baseStart_693279 := by decide
  rcases family_descends (prefixWord ++ tailWord_693279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693321 : List Nat := [1, 2, 1, 1, 2, 2, 2, 3, 6]
def baseStart_693321 : Nat := 118140960795 + 693321 * 2 ^ 59
def prefixEnd_693321 : Nat := 4983230072969 + 3 ^ 40 * 693321 * 2
def baseEnd_693321 : Nat := 316450596316432988532427

theorem tailTrace_693321 : CollatzResearch.WordTrace tailWord_693321 prefixEnd_693321 316450596316432988532427 := by
  unfold tailWord_693321
  simp only [CollatzResearch.WordTrace]
  refine ⟨25287494321223901644823817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16858329547482601096549211 25287494321223901644823817)
  ·
    refine ⟨18965620740917926233617863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25287494321223901644823817 18965620740917926233617863)
    ·
      refine ⟨28448431111376889350426795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18965620740917926233617863 28448431111376889350426795)
      ·
        refine ⟨42672646667065334025640193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28448431111376889350426795 42672646667065334025640193)
        ·
          refine ⟨32004485000299000519230145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42672646667065334025640193 32004485000299000519230145)
          ·
            refine ⟨24003363750224250389422609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32004485000299000519230145 24003363750224250389422609)
            ·
              refine ⟨18002522812668187792066957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24003363750224250389422609 18002522812668187792066957)
              ·
                refine ⟨6750946054750570422025109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18002522812668187792066957 6750946054750570422025109)
                ·
                  refine ⟨316450596316432988532427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6750946054750570422025109 316450596316432988532427)
                  ·
                    rfl

theorem cell20_693321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 3, 6].length) (baseStart_693321 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_693321 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_693321 prefixEnd_693321 := by exact prefixLift 693321
  have htrace : WordTrace (prefixWord ++ tailWord_693321) baseStart_693321 baseEnd_693321 := by
    simpa [prefixWord, tailWord_693321, baseEnd_693321] using wordTrace_append hprefix tailTrace_693321
  have hstable : (prefixWord ++ tailWord_693321).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693321).length < 2 ^ (prefixWord ++ tailWord_693321).sum := by decide
  have hdescent : baseEnd_693321 < baseStart_693321 := by decide
  rcases family_descends (prefixWord ++ tailWord_693321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693341 : List Nat := [1, 4, 4, 1, 2, 2, 6]
def baseStart_693341 : Nat := 118140960795 + 693341 * 2 ^ 59
def prefixEnd_693341 : Nat := 4983230072969 + 3 ^ 40 * 693341 * 2
def baseEnd_693341 : Nat := 35162191651266867540631

theorem tailTrace_693341 : CollatzResearch.WordTrace tailWord_693341 prefixEnd_693341 35162191651266867540631 := by
  unfold tailWord_693341
  simp only [CollatzResearch.WordTrace]
  refine ⟨25288223781151445060551877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16858815854100963373701251 25288223781151445060551877)
  ·
    refine ⟨4741541958965895948853477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25288223781151445060551877 4741541958965895948853477)
    ·
      refine ⟨889039117306105490410027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4741541958965895948853477 889039117306105490410027)
      ·
        refine ⟨1333558675959158235615041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 889039117306105490410027 1333558675959158235615041)
        ·
          refine ⟨1000169006969368676711281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1333558675959158235615041 1000169006969368676711281)
          ·
            refine ⟨750126755227026507533461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1000169006969368676711281 750126755227026507533461)
            ·
              refine ⟨35162191651266867540631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 750126755227026507533461 35162191651266867540631)
              ·
                rfl

theorem cell20_693341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 6].length) (baseStart_693341 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_693341 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_693341 prefixEnd_693341 := by exact prefixLift 693341
  have htrace : WordTrace (prefixWord ++ tailWord_693341) baseStart_693341 baseEnd_693341 := by
    simpa [prefixWord, tailWord_693341, baseEnd_693341] using wordTrace_append hprefix tailTrace_693341
  have hstable : (prefixWord ++ tailWord_693341).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693341).length < 2 ^ (prefixWord ++ tailWord_693341).sum := by decide
  have hdescent : baseEnd_693341 < baseStart_693341 := by decide
  rcases family_descends (prefixWord ++ tailWord_693341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693365 : List Nat := [1, 3, 4, 3, 1, 1, 1, 3, 3]
def baseStart_693365 : Nat := 118140960795 + 693365 * 2 ^ 59
def prefixEnd_693365 : Nat := 4983230072969 + 3 ^ 40 * 693365 * 2
def baseEnd_693365 : Nat := 316470679115364391065581

theorem tailTrace_693365 : CollatzResearch.WordTrace tailWord_693365 prefixEnd_693365 316470679115364391065581 := by
  unfold tailWord_693365
  simp only [CollatzResearch.WordTrace]
  refine ⟨25289099133064497159425549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16859399422042998106283699 25289099133064497159425549)
  ·
    refine ⟨9483412174899186434784581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25289099133064497159425549 9483412174899186434784581)
    ·
      refine ⟨1778139782793597456522109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9483412174899186434784581 1778139782793597456522109)
      ·
        refine ⟨666802418547599046195791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1778139782793597456522109 666802418547599046195791)
        ·
          refine ⟨1000203627821398569293687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 666802418547599046195791 1000203627821398569293687)
          ·
            refine ⟨1500305441732097853940531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1000203627821398569293687 1500305441732097853940531)
            ·
              refine ⟨2250458162598146780910797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1500305441732097853940531 2250458162598146780910797)
              ·
                refine ⟨843921810974305042841549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2250458162598146780910797 843921810974305042841549)
                ·
                  refine ⟨316470679115364391065581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 843921810974305042841549 316470679115364391065581)
                  ·
                    rfl

theorem cell20_693365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 3, 3].length) (baseStart_693365 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_693365 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_693365 prefixEnd_693365 := by exact prefixLift 693365
  have htrace : WordTrace (prefixWord ++ tailWord_693365) baseStart_693365 baseEnd_693365 := by
    simpa [prefixWord, tailWord_693365, baseEnd_693365] using wordTrace_append hprefix tailTrace_693365
  have hstable : (prefixWord ++ tailWord_693365).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693365).length < 2 ^ (prefixWord ++ tailWord_693365).sum := by decide
  have hdescent : baseEnd_693365 < baseStart_693365 := by decide
  rcases family_descends (prefixWord ++ tailWord_693365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693397 : List Nat := [1, 3, 2, 1, 1, 1, 2, 1, 8]
def baseStart_693397 : Nat := 118140960795 + 693397 * 2 ^ 59
def prefixEnd_693397 : Nat := 4983230072969 + 3 ^ 40 * 693397 * 2
def baseEnd_693397 : Nat := 316485284787314501998783

theorem tailTrace_693397 : CollatzResearch.WordTrace tailWord_693397 prefixEnd_693397 316485284787314501998783 := by
  unfold tailWord_693397
  simp only [CollatzResearch.WordTrace]
  refine ⟨25290266268948566624590445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16860177512632377749726963 25290266268948566624590445)
  ·
    refine ⟨9483849850855712484221417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25290266268948566624590445 9483849850855712484221417)
    ·
      refine ⟨7112887388141784363166063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9483849850855712484221417 7112887388141784363166063)
      ·
        refine ⟨10669331082212676544749095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7112887388141784363166063 10669331082212676544749095)
        ·
          refine ⟨16003996623319014817123643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10669331082212676544749095 16003996623319014817123643)
          ·
            refine ⟨24005994934978522225685465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16003996623319014817123643 24005994934978522225685465)
            ·
              refine ⟨18004496201233891669264099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24005994934978522225685465 18004496201233891669264099)
              ·
                refine ⟨27006744301850837503896149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18004496201233891669264099 27006744301850837503896149)
                ·
                  refine ⟨316485284787314501998783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27006744301850837503896149 316485284787314501998783)
                  ·
                    rfl

theorem cell20_693397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 8].length) (baseStart_693397 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_693397 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_693397 prefixEnd_693397 := by exact prefixLift 693397
  have htrace : WordTrace (prefixWord ++ tailWord_693397) baseStart_693397 baseEnd_693397 := by
    simpa [prefixWord, tailWord_693397, baseEnd_693397] using wordTrace_append hprefix tailTrace_693397
  have hstable : (prefixWord ++ tailWord_693397).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693397).length < 2 ^ (prefixWord ++ tailWord_693397).sum := by decide
  have hdescent : baseEnd_693397 < baseStart_693397 := by decide
  rcases family_descends (prefixWord ++ tailWord_693397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693406 : List Nat := [4, 3, 1, 1, 2, 3, 2, 2, 2]
def baseStart_693406 : Nat := 118140960795 + 693406 * 2 ^ 59
def prefixEnd_693406 : Nat := 4983230072969 + 3 ^ 40 * 693406 * 2
def baseEnd_693406 : Nat := 316489392632550470698747

theorem tailTrace_693406 : CollatzResearch.WordTrace tailWord_693406 prefixEnd_693406 316489392632550470698747 := by
  unfold tailWord_693406
  simp only [CollatzResearch.WordTrace]
  refine ⟨3161324315739495145208509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16860396350610640774445381 3161324315739495145208509)
  ·
    refine ⟨1185496618402310679453191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3161324315739495145208509 1185496618402310679453191)
    ·
      refine ⟨1778244927603466019179787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1185496618402310679453191 1778244927603466019179787)
      ·
        refine ⟨2667367391405199028769681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1778244927603466019179787 2667367391405199028769681)
        ·
          refine ⟨2000525543553899271577261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2667367391405199028769681 2000525543553899271577261)
          ·
            refine ⟨750197078832712226841473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2000525543553899271577261 750197078832712226841473)
            ·
              refine ⟨562647809124534170131105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 750197078832712226841473 562647809124534170131105)
              ·
                refine ⟨421985856843400627598329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 562647809124534170131105 421985856843400627598329)
                ·
                  refine ⟨316489392632550470698747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 421985856843400627598329 316489392632550470698747)
                  ·
                    rfl

theorem cell20_693406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 2, 2, 2].length) (baseStart_693406 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_693406 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_693406 prefixEnd_693406 := by exact prefixLift 693406
  have htrace : WordTrace (prefixWord ++ tailWord_693406) baseStart_693406 baseEnd_693406 := by
    simpa [prefixWord, tailWord_693406, baseEnd_693406] using wordTrace_append hprefix tailTrace_693406
  have hstable : (prefixWord ++ tailWord_693406).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693406).length < 2 ^ (prefixWord ++ tailWord_693406).sum := by decide
  have hdescent : baseEnd_693406 < baseStart_693406 := by decide
  rcases family_descends (prefixWord ++ tailWord_693406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693479 : List Nat := [1, 1, 5, 3, 2, 1, 3, 1, 3]
def baseStart_693479 : Nat := 118140960795 + 693479 * 2 ^ 59
def prefixEnd_693479 : Nat := 4983230072969 + 3 ^ 40 * 693479 * 2
def baseEnd_693479 : Nat := 316522711821686661265115

theorem tailTrace_693479 : CollatzResearch.WordTrace tailWord_693479 prefixEnd_693479 316522711821686661265115 := by
  unfold tailWord_693479
  simp only [CollatzResearch.WordTrace]
  refine ⟨25293257054651494629075491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16862171369767663086050327 25293257054651494629075491)
  ·
    refine ⟨37939885581977241943613237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25293257054651494629075491 37939885581977241943613237)
    ·
      refine ⟨3556864273310366432213741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37939885581977241943613237 3556864273310366432213741)
      ·
        refine ⟨1333824102491387412080153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3556864273310366432213741 1333824102491387412080153)
        ·
          refine ⟨1000368076868540559060115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1333824102491387412080153 1000368076868540559060115)
          ·
            refine ⟨1500552115302810838590173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1000368076868540559060115 1500552115302810838590173)
            ·
              refine ⟨562707043238554064471315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1500552115302810838590173 562707043238554064471315)
              ·
                refine ⟨844060564857831096706973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 562707043238554064471315 844060564857831096706973)
                ·
                  refine ⟨316522711821686661265115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 844060564857831096706973 316522711821686661265115)
                  ·
                    rfl

theorem cell20_693479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 3, 1, 3].length) (baseStart_693479 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_693479 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_693479 prefixEnd_693479 := by exact prefixLift 693479
  have htrace : WordTrace (prefixWord ++ tailWord_693479) baseStart_693479 baseEnd_693479 := by
    simpa [prefixWord, tailWord_693479, baseEnd_693479] using wordTrace_append hprefix tailTrace_693479
  have hstable : (prefixWord ++ tailWord_693479).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693479).length < 2 ^ (prefixWord ++ tailWord_693479).sum := by decide
  have hdescent : baseEnd_693479 < baseStart_693479 := by decide
  rcases family_descends (prefixWord ++ tailWord_693479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693507 : List Nat := [1, 1, 1, 3, 2, 4, 3, 3, 2]
def baseStart_693507 : Nat := 118140960795 + 693507 * 2 ^ 59
def prefixEnd_693507 : Nat := 4983230072969 + 3 ^ 40 * 693507 * 2
def baseEnd_693507 : Nat := 316535491784643008331667

theorem tailTrace_693507 : CollatzResearch.WordTrace tailWord_693507 prefixEnd_693507 316535491784643008331667 := by
  unfold tailWord_693507
  simp only [CollatzResearch.WordTrace]
  refine ⟨25294278298550055411094775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16862852199033370274063183 25294278298550055411094775)
  ·
    refine ⟨37941417447825083116642163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25294278298550055411094775 37941417447825083116642163)
    ·
      refine ⟨56912126171737624674963245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37941417447825083116642163 56912126171737624674963245)
      ·
        refine ⟨21342047314401609253111217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56912126171737624674963245 21342047314401609253111217)
        ·
          refine ⟨16006535485801206939833413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21342047314401609253111217 16006535485801206939833413)
          ·
            refine ⟨3001225403587726301218765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16006535485801206939833413 3001225403587726301218765)
            ·
              refine ⟨1125459526345397362957037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3001225403587726301218765 1125459526345397362957037)
              ·
                refine ⟨422047322379524011108889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1125459526345397362957037 422047322379524011108889)
                ·
                  refine ⟨316535491784643008331667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 422047322379524011108889 316535491784643008331667)
                  ·
                    rfl

theorem cell20_693507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 3, 3, 2].length) (baseStart_693507 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_693507 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_693507 prefixEnd_693507 := by exact prefixLift 693507
  have htrace : WordTrace (prefixWord ++ tailWord_693507) baseStart_693507 baseEnd_693507 := by
    simpa [prefixWord, tailWord_693507, baseEnd_693507] using wordTrace_append hprefix tailTrace_693507
  have hstable : (prefixWord ++ tailWord_693507).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693507).length < 2 ^ (prefixWord ++ tailWord_693507).sum := by decide
  have hdescent : baseEnd_693507 < baseStart_693507 := by decide
  rcases family_descends (prefixWord ++ tailWord_693507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693528 : List Nat := [2, 1, 2, 3, 1, 3, 3, 1, 4]
def baseStart_693528 : Nat := 118140960795 + 693528 * 2 ^ 59
def prefixEnd_693528 : Nat := 4983230072969 + 3 ^ 40 * 693528 * 2
def baseEnd_693528 : Nat := 316545076756860268631581

theorem tailTrace_693528 : CollatzResearch.WordTrace tailWord_693528 prefixEnd_693528 316545076756860268631581 := by
  unfold tailWord_693528
  simp only [CollatzResearch.WordTrace]
  refine ⟨12647522115736987998804619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16863362820982650665072825 12647522115736987998804619)
  ·
    refine ⟨18971283173605481998206929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12647522115736987998804619 18971283173605481998206929)
    ·
      refine ⟨14228462380204111498655197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18971283173605481998206929 14228462380204111498655197)
      ·
        refine ⟨5335673392576541811995699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14228462380204111498655197 5335673392576541811995699)
        ·
          refine ⟨8003510088864812717993549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5335673392576541811995699 8003510088864812717993549)
          ·
            refine ⟨3001316283324304769247581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8003510088864812717993549 3001316283324304769247581)
            ·
              refine ⟨1125493606246614288467843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3001316283324304769247581 1125493606246614288467843)
              ·
                refine ⟨1688240409369921432701765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1125493606246614288467843 1688240409369921432701765)
                ·
                  refine ⟨316545076756860268631581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1688240409369921432701765 316545076756860268631581)
                  ·
                    rfl

theorem cell20_693528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 3, 1, 4].length) (baseStart_693528 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_693528 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_693528 prefixEnd_693528 := by exact prefixLift 693528
  have htrace : WordTrace (prefixWord ++ tailWord_693528) baseStart_693528 baseEnd_693528 := by
    simpa [prefixWord, tailWord_693528, baseEnd_693528] using wordTrace_append hprefix tailTrace_693528
  have hstable : (prefixWord ++ tailWord_693528).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693528).length < 2 ^ (prefixWord ++ tailWord_693528).sum := by decide
  have hdescent : baseEnd_693528 < baseStart_693528 := by decide
  rcases family_descends (prefixWord ++ tailWord_693528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693538 : List Nat := [3, 3, 1, 1, 4, 1, 1, 3, 3]
def baseStart_693538 : Nat := 118140960795 + 693538 * 2 ^ 59
def prefixEnd_693538 : Nat := 4983230072969 + 3 ^ 40 * 693538 * 2
def baseEnd_693538 : Nat := 316549641029344678298207

theorem tailTrace_693538 : CollatzResearch.WordTrace tailWord_693538 prefixEnd_693538 316549641029344678298207 := by
  unfold tailWord_693538
  simp only [CollatzResearch.WordTrace]
  refine ⟨6323852240359436926368317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16863605974291831803648845 6323852240359436926368317)
  ·
    refine ⟨2371444590134788847388119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6323852240359436926368317 2371444590134788847388119)
    ·
      refine ⟨3557166885202183271082179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2371444590134788847388119 3557166885202183271082179)
      ·
        refine ⟨5335750327803274906623269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3557166885202183271082179 5335750327803274906623269)
        ·
          refine ⟨1000453186463114044991863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5335750327803274906623269 1000453186463114044991863)
          ·
            refine ⟨1500679779694671067487795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1000453186463114044991863 1500679779694671067487795)
            ·
              refine ⟨2251019669542006601231693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1500679779694671067487795 2251019669542006601231693)
              ·
                refine ⟨844132376078252475461885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2251019669542006601231693 844132376078252475461885)
                ·
                  refine ⟨316549641029344678298207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 844132376078252475461885 316549641029344678298207)
                  ·
                    rfl

theorem cell20_693538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 3, 3].length) (baseStart_693538 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_693538 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_693538 prefixEnd_693538 := by exact prefixLift 693538
  have htrace : WordTrace (prefixWord ++ tailWord_693538) baseStart_693538 baseEnd_693538 := by
    simpa [prefixWord, tailWord_693538, baseEnd_693538] using wordTrace_append hprefix tailTrace_693538
  have hstable : (prefixWord ++ tailWord_693538).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693538).length < 2 ^ (prefixWord ++ tailWord_693538).sum := by decide
  have hdescent : baseEnd_693538 < baseStart_693538 := by decide
  rcases family_descends (prefixWord ++ tailWord_693538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693587 : List Nat := [1, 1, 1, 2, 1, 1, 6, 3, 4]
def baseStart_693587 : Nat := 118140960795 + 693587 * 2 ^ 59
def prefixEnd_693587 : Nat := 4983230072969 + 3 ^ 40 * 693587 * 2
def baseEnd_693587 : Nat := 316572005964518285664673

theorem tailTrace_693587 : CollatzResearch.WordTrace tailWord_693587 prefixEnd_693587 316572005964518285664673 := by
  unfold tailWord_693587
  simp only [CollatzResearch.WordTrace]
  refine ⟨25297196138260229074007015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16864797425506819382671343 25297196138260229074007015)
  ·
    refine ⟨37945794207390343611010523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25297196138260229074007015 37945794207390343611010523)
    ·
      refine ⟨56918691311085515416515785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37945794207390343611010523 56918691311085515416515785)
      ·
        refine ⟨42689018483314136562386839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56918691311085515416515785 42689018483314136562386839)
        ·
          refine ⟨64033527724971204843580259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42689018483314136562386839 64033527724971204843580259)
          ·
            refine ⟨96050291587456807265370389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64033527724971204843580259 96050291587456807265370389)
            ·
              refine ⟨4502357418162037840564237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 96050291587456807265370389 4502357418162037840564237)
              ·
                refine ⟨1688384031810764190211589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4502357418162037840564237 1688384031810764190211589)
                ·
                  refine ⟨316572005964518285664673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1688384031810764190211589 316572005964518285664673)
                  ·
                    rfl

theorem cell20_693587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 3, 4].length) (baseStart_693587 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_693587 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_693587 prefixEnd_693587 := by exact prefixLift 693587
  have htrace : WordTrace (prefixWord ++ tailWord_693587) baseStart_693587 baseEnd_693587 := by
    simpa [prefixWord, tailWord_693587, baseEnd_693587] using wordTrace_append hprefix tailTrace_693587
  have hstable : (prefixWord ++ tailWord_693587).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693587).length < 2 ^ (prefixWord ++ tailWord_693587).sum := by decide
  have hdescent : baseEnd_693587 < baseStart_693587 := by decide
  rcases family_descends (prefixWord ++ tailWord_693587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693604 : List Nat := [2, 3, 1, 1, 3, 3, 1, 2, 4]
def baseStart_693604 : Nat := 118140960795 + 693604 * 2 ^ 59
def prefixEnd_693604 : Nat := 4983230072969 + 3 ^ 40 * 693604 * 2
def baseEnd_693604 : Nat := 316579765227741782097937

theorem tailTrace_693604 : CollatzResearch.WordTrace tailWord_693604 prefixEnd_693604 316579765227741782097937 := by
  unfold tailWord_693604
  simp only [CollatzResearch.WordTrace]
  refine ⟨12648908089599320488687933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16865210786132427318250577 12648908089599320488687933)
  ·
    refine ⟨4743340533599745183257975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12648908089599320488687933 4743340533599745183257975)
    ·
      refine ⟨7115010800399617774886963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4743340533599745183257975 7115010800399617774886963)
      ·
        refine ⟨10672516200599426662330445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7115010800399617774886963 10672516200599426662330445)
        ·
          refine ⟨4002193575224784998373917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10672516200599426662330445 4002193575224784998373917)
          ·
            refine ⟨1500822590709294374390219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4002193575224784998373917 1500822590709294374390219)
            ·
              refine ⟨2251233886063941561585329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1500822590709294374390219 2251233886063941561585329)
              ·
                refine ⟨1688425414547956171188997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2251233886063941561585329 1688425414547956171188997)
                ·
                  refine ⟨316579765227741782097937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1688425414547956171188997 316579765227741782097937)
                  ·
                    rfl

theorem cell20_693604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 2, 4].length) (baseStart_693604 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_693604 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_693604 prefixEnd_693604 := by exact prefixLift 693604
  have htrace : WordTrace (prefixWord ++ tailWord_693604) baseStart_693604 baseEnd_693604 := by
    simpa [prefixWord, tailWord_693604, baseEnd_693604] using wordTrace_append hprefix tailTrace_693604
  have hstable : (prefixWord ++ tailWord_693604).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693604).length < 2 ^ (prefixWord ++ tailWord_693604).sum := by decide
  have hdescent : baseEnd_693604 < baseStart_693604 := by decide
  rcases family_descends (prefixWord ++ tailWord_693604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693618 : List Nat := [3, 2, 1, 2, 1, 2, 2, 2, 5]
def baseStart_693618 : Nat := 118140960795 + 693618 * 2 ^ 59
def prefixEnd_693618 : Nat := 4983230072969 + 3 ^ 40 * 693618 * 2
def baseEnd_693618 : Nat := 316586155209219955631213

theorem tailTrace_693618 : CollatzResearch.WordTrace tailWord_693618 prefixEnd_693618 316586155209219955631213 := by
  unfold tailWord_693618
  simp only [CollatzResearch.WordTrace]
  refine ⟨6324581700286980342096377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16865551200765280912257005 6324581700286980342096377)
  ·
    refine ⟨4743436275215235256572283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6324581700286980342096377 4743436275215235256572283)
    ·
      refine ⟨7115154412822852884858425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4743436275215235256572283 7115154412822852884858425)
      ·
        refine ⟨5336365809617139663643819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7115154412822852884858425 5336365809617139663643819)
        ·
          refine ⟨8004548714425709495465729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5336365809617139663643819 8004548714425709495465729)
          ·
            refine ⟨6003411535819282121599297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8004548714425709495465729 6003411535819282121599297)
            ·
              refine ⟨4502558651864461591199473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6003411535819282121599297 4502558651864461591199473)
              ·
                refine ⟨3376918988898346193399605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4502558651864461591199473 3376918988898346193399605)
                ·
                  refine ⟨316586155209219955631213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3376918988898346193399605 316586155209219955631213)
                  ·
                    rfl

theorem cell20_693618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 2, 5].length) (baseStart_693618 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_693618 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_693618 prefixEnd_693618 := by exact prefixLift 693618
  have htrace : WordTrace (prefixWord ++ tailWord_693618) baseStart_693618 baseEnd_693618 := by
    simpa [prefixWord, tailWord_693618, baseEnd_693618] using wordTrace_append hprefix tailTrace_693618
  have hstable : (prefixWord ++ tailWord_693618).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693618).length < 2 ^ (prefixWord ++ tailWord_693618).sum := by decide
  have hdescent : baseEnd_693618 < baseStart_693618 := by decide
  rcases family_descends (prefixWord ++ tailWord_693618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693635 : List Nat := [1, 1, 1, 3, 5, 1, 3, 2, 3]
def baseStart_693635 : Nat := 118140960795 + 693635 * 2 ^ 59
def prefixEnd_693635 : Nat := 4983230072969 + 3 ^ 40 * 693635 * 2
def baseEnd_693635 : Nat := 316593914472443452064477

theorem tailTrace_693635 : CollatzResearch.WordTrace tailWord_693635 prefixEnd_693635 316593914472443452064477 := by
  unfold tailWord_693635
  simp only [CollatzResearch.WordTrace]
  refine ⟨25298946842086333271754359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16865964561390888847836239 25298946842086333271754359)
  ·
    refine ⟨37948420263129499907631539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25298946842086333271754359 37948420263129499907631539)
    ·
      refine ⟨56922630394694249861447309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37948420263129499907631539 56922630394694249861447309)
      ·
        refine ⟨21345986398010343698042741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56922630394694249861447309 21345986398010343698042741)
        ·
          refine ⟨2001186224813469721691507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21345986398010343698042741 2001186224813469721691507)
          ·
            refine ⟨3001779337220204582537261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2001186224813469721691507 3001779337220204582537261)
            ·
              refine ⟨1125667251457576718451473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3001779337220204582537261 1125667251457576718451473)
              ·
                refine ⟨844250438593182538838605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1125667251457576718451473 844250438593182538838605)
                ·
                  refine ⟨316593914472443452064477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 844250438593182538838605 316593914472443452064477)
                  ·
                    rfl

theorem cell20_693635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 3, 2, 3].length) (baseStart_693635 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_693635 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_693635 prefixEnd_693635 := by exact prefixLift 693635
  have htrace : WordTrace (prefixWord ++ tailWord_693635) baseStart_693635 baseEnd_693635 := by
    simpa [prefixWord, tailWord_693635, baseEnd_693635] using wordTrace_append hprefix tailTrace_693635
  have hstable : (prefixWord ++ tailWord_693635).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693635).length < 2 ^ (prefixWord ++ tailWord_693635).sum := by decide
  have hdescent : baseEnd_693635 < baseStart_693635 := by decide
  rcases family_descends (prefixWord ++ tailWord_693635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693662 : List Nat := [4, 3, 1, 2, 2, 2, 2, 4]
def baseStart_693662 : Nat := 118140960795 + 693662 * 2 ^ 59
def prefixEnd_693662 : Nat := 4983230072969 + 3 ^ 40 * 693662 * 2
def baseEnd_693662 : Nat := 105535412669383786054789

theorem tailTrace_693662 : CollatzResearch.WordTrace tailWord_693662 prefixEnd_693662 105535412669383786054789 := by
  unfold tailWord_693662
  simp only [CollatzResearch.WordTrace]
  refine ⟨3162491451623564610373405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16866621075325677921991493 3162491451623564610373405)
  ·
    refine ⟨1185934294358836728890027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3162491451623564610373405 1185934294358836728890027)
    ·
      refine ⟨1778901441538255093335041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1185934294358836728890027 1778901441538255093335041)
      ·
        refine ⟨1334176081153691320001281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1778901441538255093335041 1334176081153691320001281)
        ·
          refine ⟨1000632060865268490000961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1334176081153691320001281 1000632060865268490000961)
          ·
            refine ⟨750474045648951367500721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1000632060865268490000961 750474045648951367500721)
            ·
              refine ⟨562855534236713525625541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 750474045648951367500721 562855534236713525625541)
              ·
                refine ⟨105535412669383786054789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 562855534236713525625541 105535412669383786054789)
                ·
                  rfl

theorem cell20_693662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 2, 4].length) (baseStart_693662 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_693662 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_693662 prefixEnd_693662 := by exact prefixLift 693662
  have htrace : WordTrace (prefixWord ++ tailWord_693662) baseStart_693662 baseEnd_693662 := by
    simpa [prefixWord, tailWord_693662, baseEnd_693662] using wordTrace_append hprefix tailTrace_693662
  have hstable : (prefixWord ++ tailWord_693662).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693662).length < 2 ^ (prefixWord ++ tailWord_693662).sum := by decide
  have hdescent : baseEnd_693662 < baseStart_693662 := by decide
  rcases family_descends (prefixWord ++ tailWord_693662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693666 : List Nat := [3, 3, 1, 2, 1, 2, 4, 4]
def baseStart_693666 : Nat := 118140960795 + 693666 * 2 ^ 59
def prefixEnd_693666 : Nat := 4983230072969 + 3 ^ 40 * 693666 * 2
def baseEnd_693666 : Nat := 105536021239048374010339

theorem tailTrace_693666 : CollatzResearch.WordTrace tailWord_693666 prefixEnd_693666 105536021239048374010339 := by
  unfold tailWord_693666
  simp only [CollatzResearch.WordTrace]
  refine ⟨6325019376243506391533213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16866718336649350377421901 6325019376243506391533213)
  ·
    refine ⟨2371882266091314896824955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6325019376243506391533213 2371882266091314896824955)
    ·
      refine ⟨3557823399136972345237433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2371882266091314896824955 3557823399136972345237433)
      ·
        refine ⟨2668367549352729258928075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3557823399136972345237433 2668367549352729258928075)
        ·
          refine ⟨4002551324029093888392113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2668367549352729258928075 4002551324029093888392113)
          ·
            refine ⟨3001913493021820416294085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4002551324029093888392113 3001913493021820416294085)
            ·
              refine ⟨562858779941591328055141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3001913493021820416294085 562858779941591328055141)
              ·
                refine ⟨105536021239048374010339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 562858779941591328055141 105536021239048374010339)
                ·
                  rfl

theorem cell20_693666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 4, 4].length) (baseStart_693666 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_693666 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_693666 prefixEnd_693666 := by exact prefixLift 693666
  have htrace : WordTrace (prefixWord ++ tailWord_693666) baseStart_693666 baseEnd_693666 := by
    simpa [prefixWord, tailWord_693666, baseEnd_693666] using wordTrace_append hprefix tailTrace_693666
  have hstable : (prefixWord ++ tailWord_693666).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693666).length < 2 ^ (prefixWord ++ tailWord_693666).sum := by decide
  have hdescent : baseEnd_693666 < baseStart_693666 := by decide
  rcases family_descends (prefixWord ++ tailWord_693666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693672 : List Nat := [2, 1, 6, 1, 3, 1, 1, 3, 2]
def baseStart_693672 : Nat := 118140960795 + 693672 * 2 ^ 59
def prefixEnd_693672 : Nat := 4983230072969 + 3 ^ 40 * 693672 * 2
def baseEnd_693672 : Nat := 316610802280635767830993

theorem tailTrace_693672 : CollatzResearch.WordTrace tailWord_693672 prefixEnd_693672 316610802280635767830993 := by
  unfold tailWord_693672
  simp only [CollatzResearch.WordTrace]
  refine ⟨12650148171476144295425635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16866864228634859060567513 12650148171476144295425635)
  ·
    refine ⟨18975222257214216443138453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12650148171476144295425635 18975222257214216443138453)
    ·
      refine ⟨889463543306916395772115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 18975222257214216443138453 889463543306916395772115)
      ·
        refine ⟨1334195314960374593658173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 889463543306916395772115 1334195314960374593658173)
        ·
          refine ⟨500323243110140472621815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1334195314960374593658173 500323243110140472621815)
          ·
            refine ⟨750484864665210708932723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 500323243110140472621815 750484864665210708932723)
            ·
              refine ⟨1125727296997816063399085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 750484864665210708932723 1125727296997816063399085)
              ·
                refine ⟨422147736374181023774657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1125727296997816063399085 422147736374181023774657)
                ·
                  refine ⟨316610802280635767830993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 422147736374181023774657 316610802280635767830993)
                  ·
                    rfl

theorem cell20_693672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 1, 3, 2].length) (baseStart_693672 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_693672 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_693672 prefixEnd_693672 := by exact prefixLift 693672
  have htrace : WordTrace (prefixWord ++ tailWord_693672) baseStart_693672 baseEnd_693672 := by
    simpa [prefixWord, tailWord_693672, baseEnd_693672] using wordTrace_append hprefix tailTrace_693672
  have hstable : (prefixWord ++ tailWord_693672).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693672).length < 2 ^ (prefixWord ++ tailWord_693672).sum := by decide
  have hdescent : baseEnd_693672 < baseStart_693672 := by decide
  rcases family_descends (prefixWord ++ tailWord_693672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693680 : List Nat := [2, 1, 1, 1, 2, 1, 1, 9, 2]
def baseStart_693680 : Nat := 118140960795 + 693680 * 2 ^ 59
def prefixEnd_693680 : Nat := 4983230072969 + 3 ^ 40 * 693680 * 2
def baseEnd_693680 : Nat := 316614453698623295564293

theorem tailTrace_693680 : CollatzResearch.WordTrace tailWord_693680 prefixEnd_693680 316614453698623295564293 := by
  unfold tailWord_693680
  simp only [CollatzResearch.WordTrace]
  refine ⟨12650294063461652978571247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16867058751282203971428329 12650294063461652978571247)
  ·
    refine ⟨18975441095192479467856871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12650294063461652978571247 18975441095192479467856871)
    ·
      refine ⟨28463161642788719201785307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18975441095192479467856871 28463161642788719201785307)
      ·
        refine ⟨42694742464183078802677961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28463161642788719201785307 42694742464183078802677961)
        ·
          refine ⟨32021056848137309102008471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42694742464183078802677961 32021056848137309102008471)
          ·
            refine ⟨48031585272205963653012707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32021056848137309102008471 48031585272205963653012707)
            ·
              refine ⟨72047377908308945479519061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48031585272205963653012707 72047377908308945479519061)
              ·
                refine ⟨422152604931497727419057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 72047377908308945479519061 422152604931497727419057)
                ·
                  refine ⟨316614453698623295564293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 422152604931497727419057 316614453698623295564293)
                  ·
                    rfl

theorem cell20_693680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 9, 2].length) (baseStart_693680 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_693680 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_693680 prefixEnd_693680 := by exact prefixLift 693680
  have htrace : WordTrace (prefixWord ++ tailWord_693680) baseStart_693680 baseEnd_693680 := by
    simpa [prefixWord, tailWord_693680, baseEnd_693680] using wordTrace_append hprefix tailTrace_693680
  have hstable : (prefixWord ++ tailWord_693680).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693680).length < 2 ^ (prefixWord ++ tailWord_693680).sum := by decide
  have hdescent : baseEnd_693680 < baseStart_693680 := by decide
  rcases family_descends (prefixWord ++ tailWord_693680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693711 : List Nat := [1, 1, 2, 1, 1, 4, 6, 1, 3]
def baseStart_693711 : Nat := 118140960795 + 693711 * 2 ^ 59
def prefixEnd_693711 : Nat := 4983230072969 + 3 ^ 40 * 693711 * 2
def baseEnd_693711 : Nat := 316628602943324965530833

theorem tailTrace_693711 : CollatzResearch.WordTrace tailWord_693711 prefixEnd_693711 316628602943324965530833 := by
  unfold tailWord_693711
  simp only [CollatzResearch.WordTrace]
  refine ⟨25301718789810998251520987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16867812526540665501013991 25301718789810998251520987)
  ·
    refine ⟨37952578184716497377281481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25301718789810998251520987 37952578184716497377281481)
    ·
      refine ⟨28464433638537373032961111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37952578184716497377281481 28464433638537373032961111)
      ·
        refine ⟨42696650457806059549441667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28464433638537373032961111 42696650457806059549441667)
        ·
          refine ⟨64044975686709089324162501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42696650457806059549441667 64044975686709089324162501)
          ·
            refine ⟨12008432941257954248280469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64044975686709089324162501 12008432941257954248280469)
            ·
              refine ⟨562895294121466605388147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 12008432941257954248280469 562895294121466605388147)
              ·
                refine ⟨844342941182199908082221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 562895294121466605388147 844342941182199908082221)
                ·
                  refine ⟨316628602943324965530833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 844342941182199908082221 316628602943324965530833)
                  ·
                    rfl

theorem cell20_693711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 6, 1, 3].length) (baseStart_693711 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_693711 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_693711 prefixEnd_693711 := by exact prefixLift 693711
  have htrace : WordTrace (prefixWord ++ tailWord_693711) baseStart_693711 baseEnd_693711 := by
    simpa [prefixWord, tailWord_693711, baseEnd_693711] using wordTrace_append hprefix tailTrace_693711
  have hstable : (prefixWord ++ tailWord_693711).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693711).length < 2 ^ (prefixWord ++ tailWord_693711).sum := by decide
  have hdescent : baseEnd_693711 < baseStart_693711 := by decide
  rcases family_descends (prefixWord ++ tailWord_693711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693725 : List Nat := [1, 4, 3, 1, 1, 2, 2, 6]
def baseStart_693725 : Nat := 118140960795 + 693725 * 2 ^ 59
def prefixEnd_693725 : Nat := 4983230072969 + 3 ^ 40 * 693725 * 2
def baseEnd_693725 : Nat := 105544997641601046354703

theorem tailTrace_693725 : CollatzResearch.WordTrace tailWord_693725 prefixEnd_693725 105544997641601046354703 := by
  unfold tailWord_693725
  simp only [CollatzResearch.WordTrace]
  refine ⟨25302229411760278642530629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16868152941173519095020419 25302229411760278642530629)
  ·
    refine ⟨4744168014705052245474493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25302229411760278642530629 4744168014705052245474493)
    ·
      refine ⟨1779063005514394592052935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4744168014705052245474493 1779063005514394592052935)
      ·
        refine ⟨2668594508271591888079403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1779063005514394592052935 2668594508271591888079403)
        ·
          refine ⟨4002891762407387832119105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2668594508271591888079403 4002891762407387832119105)
          ·
            refine ⟨3002168821805540874089329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4002891762407387832119105 3002168821805540874089329)
            ·
              refine ⟨2251626616354155655566997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3002168821805540874089329 2251626616354155655566997)
              ·
                refine ⟨105544997641601046354703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2251626616354155655566997 105544997641601046354703)
                ·
                  rfl

theorem cell20_693725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 6].length) (baseStart_693725 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_693725 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_693725 prefixEnd_693725 := by exact prefixLift 693725
  have htrace : WordTrace (prefixWord ++ tailWord_693725) baseStart_693725 baseEnd_693725 := by
    simpa [prefixWord, tailWord_693725, baseEnd_693725] using wordTrace_append hprefix tailTrace_693725
  have hstable : (prefixWord ++ tailWord_693725).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693725).length < 2 ^ (prefixWord ++ tailWord_693725).sum := by decide
  have hdescent : baseEnd_693725 < baseStart_693725 := by decide
  rcases family_descends (prefixWord ++ tailWord_693725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693752 : List Nat := [2, 1, 2, 1, 1, 7, 2, 2, 2]
def baseStart_693752 : Nat := 118140960795 + 693752 * 2 ^ 59
def prefixEnd_693752 : Nat := 4983230072969 + 3 ^ 40 * 693752 * 2
def baseEnd_693752 : Nat := 316647316460511045163999

theorem tailTrace_693752 : CollatzResearch.WordTrace tailWord_693752 prefixEnd_693752 316647316460511045163999 := by
  unfold tailWord_693752
  simp only [CollatzResearch.WordTrace]
  refine ⟨12651607091331231126881755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16868809455108308169175673 12651607091331231126881755)
  ·
    refine ⟨18977410636996846690322633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12651607091331231126881755 18977410636996846690322633)
    ·
      refine ⟨14233057977747635017741975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18977410636996846690322633 14233057977747635017741975)
      ·
        refine ⟨21349586966621452526612963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14233057977747635017741975 21349586966621452526612963)
        ·
          refine ⟨32024380449932178789919445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21349586966621452526612963 32024380449932178789919445)
          ·
            refine ⟨750571416795285440388737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 32024380449932178789919445 750571416795285440388737)
            ·
              refine ⟨562928562596464080291553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 750571416795285440388737 562928562596464080291553)
              ·
                refine ⟨422196421947348060218665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 562928562596464080291553 422196421947348060218665)
                ·
                  refine ⟨316647316460511045163999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 422196421947348060218665 316647316460511045163999)
                  ·
                    rfl

theorem cell20_693752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 2, 2, 2].length) (baseStart_693752 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_693752 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_693752 prefixEnd_693752 := by exact prefixLift 693752
  have htrace : WordTrace (prefixWord ++ tailWord_693752) baseStart_693752 baseEnd_693752 := by
    simpa [prefixWord, tailWord_693752, baseEnd_693752] using wordTrace_append hprefix tailTrace_693752
  have hstable : (prefixWord ++ tailWord_693752).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693752).length < 2 ^ (prefixWord ++ tailWord_693752).sum := by decide
  have hdescent : baseEnd_693752 < baseStart_693752 := by decide
  rcases family_descends (prefixWord ++ tailWord_693752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693777 : List Nat := [1, 2, 2, 1, 1, 2, 5, 2, 4]
def baseStart_693777 : Nat := 118140960795 + 693777 * 2 ^ 59
def prefixEnd_693777 : Nat := 4983230072969 + 3 ^ 40 * 693777 * 2
def baseEnd_693777 : Nat := 316658727141722069330563

theorem tailTrace_693777 : CollatzResearch.WordTrace tailWord_693777 prefixEnd_693777 316658727141722069330563 := by
  unfold tailWord_693777
  simp only [CollatzResearch.WordTrace]
  refine ⟨25304126007571891523423585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16869417338381261015615723 25304126007571891523423585)
  ·
    refine ⟨18978094505678918642567689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25304126007571891523423585 18978094505678918642567689)
    ·
      refine ⟨14233570879259188981925767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18978094505678918642567689 14233570879259188981925767)
      ·
        refine ⟨21350356318888783472888651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14233570879259188981925767 21350356318888783472888651)
        ·
          refine ⟨32025534478333175209332977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21350356318888783472888651 32025534478333175209332977)
          ·
            refine ⟨24019150858749881406999733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32025534478333175209332977 24019150858749881406999733)
            ·
              refine ⟨2251795393007801381906225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24019150858749881406999733 2251795393007801381906225)
              ·
                refine ⟨1688846544755851036429669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2251795393007801381906225 1688846544755851036429669)
                ·
                  refine ⟨316658727141722069330563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1688846544755851036429669 316658727141722069330563)
                  ·
                    rfl

theorem cell20_693777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 2, 4].length) (baseStart_693777 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_693777 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_693777 prefixEnd_693777 := by exact prefixLift 693777
  have htrace : WordTrace (prefixWord ++ tailWord_693777) baseStart_693777 baseEnd_693777 := by
    simpa [prefixWord, tailWord_693777, baseEnd_693777] using wordTrace_append hprefix tailTrace_693777
  have hstable : (prefixWord ++ tailWord_693777).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693777).length < 2 ^ (prefixWord ++ tailWord_693777).sum := by decide
  have hdescent : baseEnd_693777 < baseStart_693777 := by decide
  rcases family_descends (prefixWord ++ tailWord_693777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693815 : List Nat := [1, 1, 3, 1, 2, 4, 1, 3, 4]
def baseStart_693815 : Nat := 118140960795 + 693815 * 2 ^ 59
def prefixEnd_693815 : Nat := 4983230072969 + 3 ^ 40 * 693815 * 2
def baseEnd_693815 : Nat := 316676071377162826063741

theorem tailTrace_693815 : CollatzResearch.WordTrace tailWord_693815 prefixEnd_693815 316676071377162826063741 := by
  unfold tailWord_693815
  simp only [CollatzResearch.WordTrace]
  refine ⟨25305511981434224013306899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16870341320956149342204599 25305511981434224013306899)
  ·
    refine ⟨37958267972151336019960349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25305511981434224013306899 37958267972151336019960349)
    ·
      refine ⟨14234350489556751007485131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37958267972151336019960349 14234350489556751007485131)
      ·
        refine ⟨21351525734335126511227697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14234350489556751007485131 21351525734335126511227697)
        ·
          refine ⟨16013644300751344883420773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21351525734335126511227697 16013644300751344883420773)
          ·
            refine ⟨3002558306390877165641395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16013644300751344883420773 3002558306390877165641395)
            ·
              refine ⟨4503837459586315748462093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3002558306390877165641395 4503837459586315748462093)
              ·
                refine ⟨1688939047344868405673285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4503837459586315748462093 1688939047344868405673285)
                ·
                  refine ⟨316676071377162826063741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1688939047344868405673285 316676071377162826063741)
                  ·
                    rfl

theorem cell20_693815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 3, 4].length) (baseStart_693815 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_693815 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_693815 prefixEnd_693815 := by exact prefixLift 693815
  have htrace : WordTrace (prefixWord ++ tailWord_693815) baseStart_693815 baseEnd_693815 := by
    simpa [prefixWord, tailWord_693815, baseEnd_693815] using wordTrace_append hprefix tailTrace_693815
  have hstable : (prefixWord ++ tailWord_693815).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693815).length < 2 ^ (prefixWord ++ tailWord_693815).sum := by decide
  have hdescent : baseEnd_693815 < baseStart_693815 := by decide
  rcases family_descends (prefixWord ++ tailWord_693815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693860 : List Nat := [2, 3, 1, 1, 2, 3, 8]
def baseStart_693860 : Nat := 118140960795 + 693860 * 2 ^ 59
def prefixEnd_693860 : Nat := 4983230072969 + 3 ^ 40 * 693860 * 2
def baseEnd_693860 : Nat := 35188512289260296618173

theorem tailTrace_693860 : CollatzResearch.WordTrace tailWord_693860 prefixEnd_693860 35188512289260296618173 := by
  unfold tailWord_693860
  simp only [CollatzResearch.WordTrace]
  refine ⟨12653576633135598349347517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16871435510847464465796689 12653576633135598349347517)
  ·
    refine ⟨4745091237425849381005319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12653576633135598349347517 4745091237425849381005319)
    ·
      refine ⟨7117636856138774071507979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4745091237425849381005319 7117636856138774071507979)
      ·
        refine ⟨10676455284208161107261969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7117636856138774071507979 10676455284208161107261969)
        ·
          refine ⟨8007341463156120830446477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10676455284208161107261969 8007341463156120830446477)
          ·
            refine ⟨3002753048683545311417429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8007341463156120830446477 3002753048683545311417429)
            ·
              refine ⟨35188512289260296618173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3002753048683545311417429 35188512289260296618173)
              ·
                rfl

theorem cell20_693860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 8].length) (baseStart_693860 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_693860 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_693860 prefixEnd_693860 := by exact prefixLift 693860
  have htrace : WordTrace (prefixWord ++ tailWord_693860) baseStart_693860 baseEnd_693860 := by
    simpa [prefixWord, tailWord_693860, baseEnd_693860] using wordTrace_append hprefix tailTrace_693860
  have hstable : (prefixWord ++ tailWord_693860).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693860).length < 2 ^ (prefixWord ++ tailWord_693860).sum := by decide
  have hdescent : baseEnd_693860 < baseStart_693860 := by decide
  rcases family_descends (prefixWord ++ tailWord_693860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693866 : List Nat := [3, 1, 3, 2, 1, 3, 3, 2, 2]
def baseStart_693866 : Nat := 118140960795 + 693866 * 2 ^ 59
def prefixEnd_693866 : Nat := 4983230072969 + 3 ^ 40 * 693866 * 2
def baseEnd_693866 : Nat := 316699349166833315363533

theorem tailTrace_693866 : CollatzResearch.WordTrace tailWord_693866 prefixEnd_693866 316699349166833315363533 := by
  unfold tailWord_693866
  simp only [CollatzResearch.WordTrace]
  refine ⟨6326843026062364930853363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16871581402832973148942301 6326843026062364930853363)
  ·
    refine ⟨9490264539093547396280045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6326843026062364930853363 9490264539093547396280045)
    ·
      refine ⟨3558849202160080273605017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9490264539093547396280045 3558849202160080273605017)
      ·
        refine ⟨2669136901620060205203763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3558849202160080273605017 2669136901620060205203763)
        ·
          refine ⟨4003705352430090307805645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2669136901620060205203763 4003705352430090307805645)
          ·
            refine ⟨1501389507161283865427117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4003705352430090307805645 1501389507161283865427117)
            ·
              refine ⟨563021065185481449535169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1501389507161283865427117 563021065185481449535169)
              ·
                refine ⟨422265798889111087151377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 563021065185481449535169 422265798889111087151377)
                ·
                  refine ⟨316699349166833315363533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 422265798889111087151377 316699349166833315363533)
                  ·
                    rfl

theorem cell20_693866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 3, 2, 2].length) (baseStart_693866 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_693866 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_693866 prefixEnd_693866 := by exact prefixLift 693866
  have htrace : WordTrace (prefixWord ++ tailWord_693866) baseStart_693866 baseEnd_693866 := by
    simpa [prefixWord, tailWord_693866, baseEnd_693866] using wordTrace_append hprefix tailTrace_693866
  have hstable : (prefixWord ++ tailWord_693866).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693866).length < 2 ^ (prefixWord ++ tailWord_693866).sum := by decide
  have hdescent : baseEnd_693866 < baseStart_693866 := by decide
  rcases family_descends (prefixWord ++ tailWord_693866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693877 : List Nat := [1, 3, 4, 2, 1, 1, 1, 7]
def baseStart_693877 : Nat := 118140960795 + 693877 * 2 ^ 59
def prefixEnd_693877 : Nat := 4983230072969 + 3 ^ 40 * 693877 * 2
def baseEnd_693877 : Nat := 105568123288855388665607

theorem tailTrace_693877 : CollatzResearch.WordTrace tailWord_693877 prefixEnd_693877 105568123288855388665607 := by
  unfold tailWord_693877
  simp only [CollatzResearch.WordTrace]
  refine ⟨25307773307209608602063885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16871848871473072401375923 25307773307209608602063885)
  ·
    refine ⟨9490414990203603225773957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25307773307209608602063885 9490414990203603225773957)
    ·
      refine ⟨1779452810663175604832617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9490414990203603225773957 1779452810663175604832617)
      ·
        refine ⟨1334589607997381703624463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1779452810663175604832617 1334589607997381703624463)
        ·
          refine ⟨2001884411996072555436695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1334589607997381703624463 2001884411996072555436695)
          ·
            refine ⟨3002826617994108833155043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2001884411996072555436695 3002826617994108833155043)
            ·
              refine ⟨4504239926991163249732565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3002826617994108833155043 4504239926991163249732565)
              ·
                refine ⟨105568123288855388665607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4504239926991163249732565 105568123288855388665607)
                ·
                  rfl

theorem cell20_693877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 7].length) (baseStart_693877 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_693877 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_693877 prefixEnd_693877 := by exact prefixLift 693877
  have htrace : WordTrace (prefixWord ++ tailWord_693877) baseStart_693877 baseEnd_693877 := by
    simpa [prefixWord, tailWord_693877, baseEnd_693877] using wordTrace_append hprefix tailTrace_693877
  have hstable : (prefixWord ++ tailWord_693877).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693877).length < 2 ^ (prefixWord ++ tailWord_693877).sum := by decide
  have hdescent : baseEnd_693877 < baseStart_693877 := by decide
  rcases family_descends (prefixWord ++ tailWord_693877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693905 : List Nat := [1, 2, 2, 1, 1, 1, 1, 6, 5]
def baseStart_693905 : Nat := 118140960795 + 693905 * 2 ^ 59
def prefixEnd_693905 : Nat := 4983230072969 + 3 ^ 40 * 693905 * 2
def baseEnd_693905 : Nat := 316717149829522513063373

theorem tailTrace_693905 : CollatzResearch.WordTrace tailWord_693905 prefixEnd_693905 316717149829522513063373 := by
  unfold tailWord_693905
  simp only [CollatzResearch.WordTrace]
  refine ⟨25308794551108169384083169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16872529700738779589388779 25308794551108169384083169)
  ·
    refine ⟨18981595913331127038062377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25308794551108169384083169 18981595913331127038062377)
    ·
      refine ⟨14236196934998345278546783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18981595913331127038062377 14236196934998345278546783)
      ·
        refine ⟨21354295402497517917820175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14236196934998345278546783 21354295402497517917820175)
        ·
          refine ⟨32031443103746276876730263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21354295402497517917820175 32031443103746276876730263)
          ·
            refine ⟨48047164655619415315095395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32031443103746276876730263 48047164655619415315095395)
            ·
              refine ⟨72070746983429122972643093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48047164655619415315095395 72070746983429122972643093)
              ·
                refine ⟨3378316264848240139342645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 72070746983429122972643093 3378316264848240139342645)
                ·
                  refine ⟨316717149829522513063373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3378316264848240139342645 316717149829522513063373)
                  ·
                    rfl

theorem cell20_693905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 6, 5].length) (baseStart_693905 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_693905 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_693905 prefixEnd_693905 := by exact prefixLift 693905
  have htrace : WordTrace (prefixWord ++ tailWord_693905) baseStart_693905 baseEnd_693905 := by
    simpa [prefixWord, tailWord_693905, baseEnd_693905] using wordTrace_append hprefix tailTrace_693905
  have hstable : (prefixWord ++ tailWord_693905).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693905).length < 2 ^ (prefixWord ++ tailWord_693905).sum := by decide
  have hdescent : baseEnd_693905 < baseStart_693905 := by decide
  rcases family_descends (prefixWord ++ tailWord_693905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693918 : List Nat := [4, 3, 1, 1, 1, 3, 2, 2, 3]
def baseStart_693918 : Nat := 118140960795 + 693918 * 2 ^ 59
def prefixEnd_693918 : Nat := 4983230072969 + 3 ^ 40 * 693918 * 2
def baseEnd_693918 : Nat := 316723083383752245629987

theorem tailTrace_693918 : CollatzResearch.WordTrace tailWord_693918 prefixEnd_693918 316723083383752245629987 := by
  unfold tailWord_693918
  simp only [CollatzResearch.WordTrace]
  refine ⟨3163658587507634075538301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16872845800040715069537605 3163658587507634075538301)
  ·
    refine ⟨1186371970315362778326863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3163658587507634075538301 1186371970315362778326863)
    ·
      refine ⟨1779557955473044167490295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1186371970315362778326863 1779557955473044167490295)
      ·
        refine ⟨2669336933209566251235443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1779557955473044167490295 2669336933209566251235443)
        ·
          refine ⟨4004005399814349376853165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2669336933209566251235443 4004005399814349376853165)
          ·
            refine ⟨1501502024930381016319937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4004005399814349376853165 1501502024930381016319937)
            ·
              refine ⟨1126126518697785762239953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1501502024930381016319937 1126126518697785762239953)
              ·
                refine ⟨844594889023339321679965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1126126518697785762239953 844594889023339321679965)
                ·
                  refine ⟨316723083383752245629987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 844594889023339321679965 316723083383752245629987)
                  ·
                    rfl

theorem cell20_693918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_693918 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_693918 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_693918 prefixEnd_693918 := by exact prefixLift 693918
  have htrace : WordTrace (prefixWord ++ tailWord_693918) baseStart_693918 baseEnd_693918 := by
    simpa [prefixWord, tailWord_693918, baseEnd_693918] using wordTrace_append hprefix tailTrace_693918
  have hstable : (prefixWord ++ tailWord_693918).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693918).length < 2 ^ (prefixWord ++ tailWord_693918).sum := by decide
  have hdescent : baseEnd_693918 < baseStart_693918 := by decide
  rcases family_descends (prefixWord ++ tailWord_693918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693925 : List Nat := [1, 3, 1, 2, 1, 2, 6, 2, 2]
def baseStart_693925 : Nat := 118140960795 + 693925 * 2 ^ 59
def prefixEnd_693925 : Nat := 4983230072969 + 3 ^ 40 * 693925 * 2
def baseEnd_693925 : Nat := 316726278374491332396625

theorem tailTrace_693925 : CollatzResearch.WordTrace tailWord_693925 prefixEnd_693925 316726278374491332396625 := by
  unfold tailWord_693925
  simp only [CollatzResearch.WordTrace]
  refine ⟨25309524011035712799811229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16873016007357141866540819 25309524011035712799811229)
  ·
    refine ⟨9491071504138392299929211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25309524011035712799811229 9491071504138392299929211)
    ·
      refine ⟨14236607256207588449893817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9491071504138392299929211 14236607256207588449893817)
      ·
        refine ⟨10677455442155691337420363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14236607256207588449893817 10677455442155691337420363)
        ·
          refine ⟨16016183163233537006130545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10677455442155691337420363 16016183163233537006130545)
          ·
            refine ⟨12012137372425152754597909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16016183163233537006130545 12012137372425152754597909)
            ·
              refine ⟨563068939332429035371777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 12012137372425152754597909 563068939332429035371777)
              ·
                refine ⟨422301704499321776528833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 563068939332429035371777 422301704499321776528833)
                ·
                  refine ⟨316726278374491332396625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 422301704499321776528833 316726278374491332396625)
                  ·
                    rfl

theorem cell20_693925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 6, 2, 2].length) (baseStart_693925 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_693925 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_693925 prefixEnd_693925 := by exact prefixLift 693925
  have htrace : WordTrace (prefixWord ++ tailWord_693925) baseStart_693925 baseEnd_693925 := by
    simpa [prefixWord, tailWord_693925, baseEnd_693925] using wordTrace_append hprefix tailTrace_693925
  have hstable : (prefixWord ++ tailWord_693925).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693925).length < 2 ^ (prefixWord ++ tailWord_693925).sum := by decide
  have hdescent : baseEnd_693925 < baseStart_693925 := by decide
  rcases family_descends (prefixWord ++ tailWord_693925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693928 : List Nat := [2, 1, 7, 1, 1, 2, 1, 5]
def baseStart_693928 : Nat := 118140960795 + 693928 * 2 ^ 59
def prefixEnd_693928 : Nat := 4983230072969 + 3 ^ 40 * 693928 * 2
def baseEnd_693928 : Nat := 105575882552078885098871

theorem tailTrace_693928 : CollatzResearch.WordTrace tailWord_693928 prefixEnd_693928 105575882552078885098871 := by
  unfold tailWord_693928
  simp only [CollatzResearch.WordTrace]
  refine ⟨12654816715012422156085219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16873088953349896208113625 12654816715012422156085219)
  ·
    refine ⟨18982225072518633234127829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12654816715012422156085219 18982225072518633234127829)
    ·
      refine ⟨444895900137155466424871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 18982225072518633234127829 444895900137155466424871)
      ·
        refine ⟨667343850205733199637307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 444895900137155466424871 667343850205733199637307)
        ·
          refine ⟨1001015775308599799455961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 667343850205733199637307 1001015775308599799455961)
          ·
            refine ⟨750761831481449849591971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1001015775308599799455961 750761831481449849591971)
            ·
              refine ⟨1126142747222174774387957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 750761831481449849591971 1126142747222174774387957)
              ·
                refine ⟨105575882552078885098871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1126142747222174774387957 105575882552078885098871)
                ·
                  rfl

theorem cell20_693928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 1, 5].length) (baseStart_693928 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_693928 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_693928 prefixEnd_693928 := by exact prefixLift 693928
  have htrace : WordTrace (prefixWord ++ tailWord_693928) baseStart_693928 baseEnd_693928 := by
    simpa [prefixWord, tailWord_693928, baseEnd_693928] using wordTrace_append hprefix tailTrace_693928
  have hstable : (prefixWord ++ tailWord_693928).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693928).length < 2 ^ (prefixWord ++ tailWord_693928).sum := by decide
  have hdescent : baseEnd_693928 < baseStart_693928 := by decide
  rcases family_descends (prefixWord ++ tailWord_693928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693936 : List Nat := [2, 1, 1, 1, 2, 1, 7, 5]
def baseStart_693936 : Nat := 118140960795 + 693936 * 2 ^ 59
def prefixEnd_693936 : Nat := 4983230072969 + 3 ^ 40 * 693936 * 2
def baseEnd_693936 : Nat := 105577099691408061009971

theorem tailTrace_693936 : CollatzResearch.WordTrace tailWord_693936 prefixEnd_693936 105577099691408061009971 := by
  unfold tailWord_693936
  simp only [CollatzResearch.WordTrace]
  refine ⟨12654962606997930839230831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16873283475997241118974441 12654962606997930839230831)
  ·
    refine ⟨18982443910496896258846247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12654962606997930839230831 18982443910496896258846247)
    ·
      refine ⟨28473665865745344388269371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18982443910496896258846247 28473665865745344388269371)
      ·
        refine ⟨42710498798618016582404057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28473665865745344388269371 42710498798618016582404057)
        ·
          refine ⟨32032874098963512436803043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42710498798618016582404057 32032874098963512436803043)
          ·
            refine ⟨48049311148445268655204565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32032874098963512436803043 48049311148445268655204565)
            ·
              refine ⟨1126155730041685984106357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 48049311148445268655204565 1126155730041685984106357)
              ·
                refine ⟨105577099691408061009971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1126155730041685984106357 105577099691408061009971)
                ·
                  rfl

theorem cell20_693936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 7, 5].length) (baseStart_693936 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_693936 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_693936 prefixEnd_693936 := by exact prefixLift 693936
  have htrace : WordTrace (prefixWord ++ tailWord_693936) baseStart_693936 baseEnd_693936 := by
    simpa [prefixWord, tailWord_693936, baseEnd_693936] using wordTrace_append hprefix tailTrace_693936
  have hstable : (prefixWord ++ tailWord_693936).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693936).length < 2 ^ (prefixWord ++ tailWord_693936).sum := by decide
  have hdescent : baseEnd_693936 < baseStart_693936 := by decide
  rcases family_descends (prefixWord ++ tailWord_693936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693977 : List Nat := [1, 2, 1, 2, 3, 5, 1, 2, 3]
def baseStart_693977 : Nat := 118140960795 + 693977 * 2 ^ 59
def prefixEnd_693977 : Nat := 4983230072969 + 3 ^ 40 * 693977 * 2
def baseEnd_693977 : Nat := 316750012591410262663079

theorem tailTrace_693977 : CollatzResearch.WordTrace tailWord_693977 prefixEnd_693977 316750012591410262663079 := by
  unfold tailWord_693977
  simp only [CollatzResearch.WordTrace]
  refine ⟨25311420606847325680704185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16874280404564883787136123 25311420606847325680704185)
  ·
    refine ⟨18983565455135494260528139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25311420606847325680704185 18983565455135494260528139)
    ·
      refine ⟨28475348182703241390792209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18983565455135494260528139 28475348182703241390792209)
      ·
        refine ⟨21356511137027431043094157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28475348182703241390792209 21356511137027431043094157)
        ·
          refine ⟨8008691676385286641160309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21356511137027431043094157 8008691676385286641160309)
          ·
            refine ⟨750814844661120622608779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8008691676385286641160309 750814844661120622608779)
            ·
              refine ⟨1126222266991680933913169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 750814844661120622608779 1126222266991680933913169)
              ·
                refine ⟨844666700243760700434877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1126222266991680933913169 844666700243760700434877)
                ·
                  refine ⟨316750012591410262663079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 844666700243760700434877 316750012591410262663079)
                  ·
                    rfl

theorem cell20_693977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 1, 2, 3].length) (baseStart_693977 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_693977 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_693977 prefixEnd_693977 := by exact prefixLift 693977
  have htrace : WordTrace (prefixWord ++ tailWord_693977) baseStart_693977 baseEnd_693977 := by
    simpa [prefixWord, tailWord_693977, baseEnd_693977] using wordTrace_append hprefix tailTrace_693977
  have hstable : (prefixWord ++ tailWord_693977).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693977).length < 2 ^ (prefixWord ++ tailWord_693977).sum := by decide
  have hdescent : baseEnd_693977 < baseStart_693977 := by decide
  rcases family_descends (prefixWord ++ tailWord_693977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_693984 : List Nat := [2, 1, 1, 3, 1, 2, 4, 4, 2]
def baseStart_693984 : Nat := 118140960795 + 693984 * 2 ^ 59
def prefixEnd_693984 : Nat := 4983230072969 + 3 ^ 40 * 693984 * 2
def baseEnd_693984 : Nat := 316753207582149349429717

theorem tailTrace_693984 : CollatzResearch.WordTrace tailWord_693984 prefixEnd_693984 316753207582149349429717 := by
  unfold tailWord_693984
  simp only [CollatzResearch.WordTrace]
  refine ⟨12655837958910982938104503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16874450611881310584139337 12655837958910982938104503)
  ·
    refine ⟨18983756938366474407156755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12655837958910982938104503 18983756938366474407156755)
    ·
      refine ⟨28475635407549711610735133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18983756938366474407156755 28475635407549711610735133)
      ·
        refine ⟨10678363277831141854025675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28475635407549711610735133 10678363277831141854025675)
        ·
          refine ⟨16017544916746712781038513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10678363277831141854025675 16017544916746712781038513)
          ·
            refine ⟨12013158687560034585778885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16017544916746712781038513 12013158687560034585778885)
            ·
              refine ⟨2252467253917506484833541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12013158687560034585778885 2252467253917506484833541)
              ·
                refine ⟨422337610109532465906289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2252467253917506484833541 422337610109532465906289)
                ·
                  refine ⟨316753207582149349429717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 422337610109532465906289 316753207582149349429717)
                  ·
                    rfl

theorem cell20_693984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 4, 2].length) (baseStart_693984 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_693984 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_693984 prefixEnd_693984 := by exact prefixLift 693984
  have htrace : WordTrace (prefixWord ++ tailWord_693984) baseStart_693984 baseEnd_693984 := by
    simpa [prefixWord, tailWord_693984, baseEnd_693984] using wordTrace_append hprefix tailTrace_693984
  have hstable : (prefixWord ++ tailWord_693984).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_693984).length < 2 ^ (prefixWord ++ tailWord_693984).sum := by decide
  have hdescent : baseEnd_693984 < baseStart_693984 := by decide
  rcases family_descends (prefixWord ++ tailWord_693984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694004 : List Nat := [2, 6, 1, 1, 1, 3, 2, 4]
def baseStart_694004 : Nat := 118140960795 + 694004 * 2 ^ 59
def prefixEnd_694004 : Nat := 4983230072969 + 3 ^ 40 * 694004 * 2
def baseEnd_694004 : Nat := 105587445375706056254323

theorem tailTrace_694004 : CollatzResearch.WordTrace tailWord_694004 prefixEnd_694004 105587445375706056254323 := by
  unfold tailWord_694004
  simp only [CollatzResearch.WordTrace]
  refine ⟨12656202688874754645968533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16874936918499672861291377 12656202688874754645968533)
  ·
    refine ⟨593259501041004124029775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 12656202688874754645968533 593259501041004124029775)
    ·
      refine ⟨889889251561506186044663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 593259501041004124029775 889889251561506186044663)
      ·
        refine ⟨1334833877342259279066995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 889889251561506186044663 1334833877342259279066995)
        ·
          refine ⟨2002250816013388918600493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1334833877342259279066995 2002250816013388918600493)
          ·
            refine ⟨750844056005020844475185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2002250816013388918600493 750844056005020844475185)
            ·
              refine ⟨563133042003765633356389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 750844056005020844475185 563133042003765633356389)
              ·
                refine ⟨105587445375706056254323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 563133042003765633356389 105587445375706056254323)
                ·
                  rfl

theorem cell20_694004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 2, 4].length) (baseStart_694004 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_694004 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_694004 prefixEnd_694004 := by exact prefixLift 694004
  have htrace : WordTrace (prefixWord ++ tailWord_694004) baseStart_694004 baseEnd_694004 := by
    simpa [prefixWord, tailWord_694004, baseEnd_694004] using wordTrace_append hprefix tailTrace_694004
  have hstable : (prefixWord ++ tailWord_694004).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694004).length < 2 ^ (prefixWord ++ tailWord_694004).sum := by decide
  have hdescent : baseEnd_694004 < baseStart_694004 := by decide
  rcases family_descends (prefixWord ++ tailWord_694004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694012 : List Nat := [2, 2, 2, 1, 3, 1, 3, 6]
def baseStart_694012 : Nat := 118140960795 + 694012 * 2 ^ 59
def prefixEnd_694012 : Nat := 4983230072969 + 3 ^ 40 * 694012 * 2
def baseEnd_694012 : Nat := 105588662515035232165423

theorem tailTrace_694012 : CollatzResearch.WordTrace tailWord_694012 prefixEnd_694012 105588662515035232165423 := by
  unfold tailWord_694012
  simp only [CollatzResearch.WordTrace]
  refine ⟨12656348580860263329114145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16875131441147017772152193 12656348580860263329114145)
  ·
    refine ⟨9492261435645197496835609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12656348580860263329114145 9492261435645197496835609)
    ·
      refine ⟨7119196076733898122626707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9492261435645197496835609 7119196076733898122626707)
      ·
        refine ⟨10678794115100847183940061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7119196076733898122626707 10678794115100847183940061)
        ·
          refine ⟨4004547793162817693977523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10678794115100847183940061 4004547793162817693977523)
          ·
            refine ⟨6006821689744226540966285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4004547793162817693977523 6006821689744226540966285)
            ·
              refine ⟨2252558133654084952862357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6006821689744226540966285 2252558133654084952862357)
              ·
                refine ⟨105588662515035232165423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2252558133654084952862357 105588662515035232165423)
                ·
                  rfl

theorem cell20_694012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 6].length) (baseStart_694012 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_694012 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_694012 prefixEnd_694012 := by exact prefixLift 694012
  have htrace : WordTrace (prefixWord ++ tailWord_694012) baseStart_694012 baseEnd_694012 := by
    simpa [prefixWord, tailWord_694012, baseEnd_694012] using wordTrace_append hprefix tailTrace_694012
  have hstable : (prefixWord ++ tailWord_694012).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694012).length < 2 ^ (prefixWord ++ tailWord_694012).sum := by decide
  have hdescent : baseEnd_694012 < baseStart_694012 := by decide
  rcases family_descends (prefixWord ++ tailWord_694012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694019 : List Nat := [1, 1, 1, 3, 2, 2, 3, 2, 5]
def baseStart_694019 : Nat := 118140960795 + 694019 * 2 ^ 59
def prefixEnd_694019 : Nat := 4983230072969 + 3 ^ 40 * 694019 * 2
def baseEnd_694019 : Nat := 316769182535844783262907

theorem tailTrace_694019 : CollatzResearch.WordTrace tailWord_694019 prefixEnd_694019 316769182535844783262907 := by
  unfold tailWord_694019
  simp only [CollatzResearch.WordTrace]
  refine ⟨25312952472695166853733111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16875301648463444569155407 25312952472695166853733111)
  ·
    refine ⟨37969428709042750280599667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25312952472695166853733111 37969428709042750280599667)
    ·
      refine ⟨56954143063564125420899501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37969428709042750280599667 56954143063564125420899501)
      ·
        refine ⟨21357803648836547032837313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56954143063564125420899501 21357803648836547032837313)
        ·
          refine ⟨16018352736627410274627985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21357803648836547032837313 16018352736627410274627985)
          ·
            refine ⟨12013764552470557705970989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16018352736627410274627985 12013764552470557705970989)
            ·
              refine ⟨4505161707176459139739121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12013764552470557705970989 4505161707176459139739121)
              ·
                refine ⟨3378871280382344354804341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4505161707176459139739121 3378871280382344354804341)
                ·
                  refine ⟨316769182535844783262907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3378871280382344354804341 316769182535844783262907)
                  ·
                    rfl

theorem cell20_694019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 2, 5].length) (baseStart_694019 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_694019 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_694019 prefixEnd_694019 := by exact prefixLift 694019
  have htrace : WordTrace (prefixWord ++ tailWord_694019) baseStart_694019 baseEnd_694019 := by
    simpa [prefixWord, tailWord_694019, baseEnd_694019] using wordTrace_append hprefix tailTrace_694019
  have hstable : (prefixWord ++ tailWord_694019).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694019).length < 2 ^ (prefixWord ++ tailWord_694019).sum := by decide
  have hdescent : baseEnd_694019 < baseStart_694019 := by decide
  rcases family_descends (prefixWord ++ tailWord_694019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694053 : List Nat := [1, 3, 1, 2, 3, 2, 4, 1, 3]
def baseStart_694053 : Nat := 118140960795 + 694053 * 2 ^ 59
def prefixEnd_694053 : Nat := 4983230072969 + 3 ^ 40 * 694053 * 2
def baseEnd_694053 : Nat := 316784701062291776129435

theorem tailTrace_694053 : CollatzResearch.WordTrace tailWord_694053 prefixEnd_694053 316784701062291776129435 := by
  unfold tailWord_694053
  simp only [CollatzResearch.WordTrace]
  refine ⟨25314192554571990660470813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16876128369714660440313875 25314192554571990660470813)
  ·
    refine ⟨9492822207964496497676555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25314192554571990660470813 9492822207964496497676555)
    ·
      refine ⟨14239233311946744746514833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9492822207964496497676555 14239233311946744746514833)
      ·
        refine ⟨10679424983960058559886125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14239233311946744746514833 10679424983960058559886125)
        ·
          refine ⟨4004784368985021959957297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10679424983960058559886125 4004784368985021959957297)
          ·
            refine ⟨3003588276738766469967973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4004784368985021959957297 3003588276738766469967973)
            ·
              refine ⟨563172801888518713118995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3003588276738766469967973 563172801888518713118995)
              ·
                refine ⟨844759202832778069678493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 563172801888518713118995 844759202832778069678493)
                ·
                  refine ⟨316784701062291776129435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 844759202832778069678493 316784701062291776129435)
                  ·
                    rfl

theorem cell20_694053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 4, 1, 3].length) (baseStart_694053 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_694053 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_694053 prefixEnd_694053 := by exact prefixLift 694053
  have htrace : WordTrace (prefixWord ++ tailWord_694053) baseStart_694053 baseEnd_694053 := by
    simpa [prefixWord, tailWord_694053, baseEnd_694053] using wordTrace_append hprefix tailTrace_694053
  have hstable : (prefixWord ++ tailWord_694053).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694053).length < 2 ^ (prefixWord ++ tailWord_694053).sum := by decide
  have hdescent : baseEnd_694053 < baseStart_694053 := by decide
  rcases family_descends (prefixWord ++ tailWord_694053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694112 : List Nat := [2, 1, 1, 3, 3, 2, 2, 3, 3]
def baseStart_694112 : Nat := 118140960795 + 694112 * 2 ^ 59
def prefixEnd_694112 : Nat := 4983230072969 + 3 ^ 40 * 694112 * 2
def baseEnd_694112 : Nat := 316811630269949793162527

theorem tailTrace_694112 : CollatzResearch.WordTrace tailWord_694112 prefixEnd_694112 316811630269949793162527 := by
  unfold tailWord_694112
  simp only [CollatzResearch.WordTrace]
  refine ⟨12658172230679121868434295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16877562974238829157912393 12658172230679121868434295)
  ·
    refine ⟨18987258346018682802651443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12658172230679121868434295 18987258346018682802651443)
    ·
      refine ⟨28480887519028024203977165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18987258346018682802651443 28480887519028024203977165)
      ·
        refine ⟨10680332819635509076491437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28480887519028024203977165 10680332819635509076491437)
        ·
          refine ⟨4005124807363315903684289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10680332819635509076491437 4005124807363315903684289)
          ·
            refine ⟨3003843605522486927763217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4005124807363315903684289 3003843605522486927763217)
            ·
              refine ⟨2252882704141865195822413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3003843605522486927763217 2252882704141865195822413)
              ·
                refine ⟨844831014053199448433405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2252882704141865195822413 844831014053199448433405)
                ·
                  refine ⟨316811630269949793162527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 844831014053199448433405 316811630269949793162527)
                  ·
                    rfl

theorem cell20_694112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 3, 3].length) (baseStart_694112 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_694112 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_694112 prefixEnd_694112 := by exact prefixLift 694112
  have htrace : WordTrace (prefixWord ++ tailWord_694112) baseStart_694112 baseEnd_694112 := by
    simpa [prefixWord, tailWord_694112, baseEnd_694112] using wordTrace_append hprefix tailTrace_694112
  have hstable : (prefixWord ++ tailWord_694112).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694112).length < 2 ^ (prefixWord ++ tailWord_694112).sum := by decide
  have hdescent : baseEnd_694112 < baseStart_694112 := by decide
  rcases family_descends (prefixWord ++ tailWord_694112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694119 : List Nat := [1, 1, 5, 1, 2, 1, 3, 2, 4]
def baseStart_694119 : Nat := 118140960795 + 694119 * 2 ^ 59
def prefixEnd_694119 : Nat := 4983230072969 + 3 ^ 40 * 694119 * 2
def baseEnd_694119 : Nat := 316814825260688879929165

theorem tailTrace_694119 : CollatzResearch.WordTrace tailWord_694119 prefixEnd_694119 316814825260688879929165 := by
  unfold tailWord_694119
  simp only [CollatzResearch.WordTrace]
  refine ⟨25316599772332883932373411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16877733181555255954915607 25316599772332883932373411)
  ·
    refine ⟨37974899658499325898560117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25316599772332883932373411 37974899658499325898560117)
    ·
      refine ⟨3560146842984311802990011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37974899658499325898560117 3560146842984311802990011)
      ·
        refine ⟨5340220264476467704485017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3560146842984311802990011 5340220264476467704485017)
        ·
          refine ⟨4005165198357350778363763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5340220264476467704485017 4005165198357350778363763)
          ·
            refine ⟨6007747797536026167545645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4005165198357350778363763 6007747797536026167545645)
            ·
              refine ⟨2252905424076009812829617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6007747797536026167545645 2252905424076009812829617)
              ·
                refine ⟨1689679068057007359622213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2252905424076009812829617 1689679068057007359622213)
                ·
                  refine ⟨316814825260688879929165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1689679068057007359622213 316814825260688879929165)
                  ·
                    rfl

theorem cell20_694119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 2, 4].length) (baseStart_694119 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_694119 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_694119 prefixEnd_694119 := by exact prefixLift 694119
  have htrace : WordTrace (prefixWord ++ tailWord_694119) baseStart_694119 baseEnd_694119 := by
    simpa [prefixWord, tailWord_694119, baseEnd_694119] using wordTrace_append hprefix tailTrace_694119
  have hstable : (prefixWord ++ tailWord_694119).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694119).length < 2 ^ (prefixWord ++ tailWord_694119).sum := by decide
  have hdescent : baseEnd_694119 < baseStart_694119 := by decide
  rcases family_descends (prefixWord ++ tailWord_694119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694167 : List Nat := [1, 1, 3, 3, 1, 4, 3, 1, 3]
def baseStart_694167 : Nat := 118140960795 + 694167 * 2 ^ 59
def prefixEnd_694167 : Nat := 4983230072969 + 3 ^ 40 * 694167 * 2
def baseEnd_694167 : Nat := 316836733768614046328969

theorem tailTrace_694167 : CollatzResearch.WordTrace tailWord_694167 prefixEnd_694167 316836733768614046328969 := by
  unfold tailWord_694167
  simp only [CollatzResearch.WordTrace]
  refine ⟨25318350476158988130120755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16878900317439325420080503 25318350476158988130120755)
  ·
    refine ⟨37977525714238482195181133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25318350476158988130120755 37977525714238482195181133)
    ·
      refine ⟨14241572142839430823192925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37977525714238482195181133 14241572142839430823192925)
      ·
        refine ⟨5340589553564786558697347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14241572142839430823192925 5340589553564786558697347)
        ·
          refine ⟨8010884330347179838046021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5340589553564786558697347 8010884330347179838046021)
          ·
            refine ⟨1502040811940096219633629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8010884330347179838046021 1502040811940096219633629)
            ·
              refine ⟨563265304477536082362611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1502040811940096219633629 563265304477536082362611)
              ·
                refine ⟨844897956716304123543917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 563265304477536082362611 844897956716304123543917)
                ·
                  refine ⟨316836733768614046328969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 844897956716304123543917 316836733768614046328969)
                  ·
                    rfl

theorem cell20_694167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 3, 1, 3].length) (baseStart_694167 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_694167 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_694167 prefixEnd_694167 := by exact prefixLift 694167
  have htrace : WordTrace (prefixWord ++ tailWord_694167) baseStart_694167 baseEnd_694167 := by
    simpa [prefixWord, tailWord_694167, baseEnd_694167] using wordTrace_append hprefix tailTrace_694167
  have hstable : (prefixWord ++ tailWord_694167).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694167).length < 2 ^ (prefixWord ++ tailWord_694167).sum := by decide
  have hdescent : baseEnd_694167 < baseStart_694167 := by decide
  rcases family_descends (prefixWord ++ tailWord_694167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694177 : List Nat := [1, 2, 3, 4, 3, 1, 2, 4]
def baseStart_694177 : Nat := 118140960795 + 694177 * 2 ^ 59
def prefixEnd_694177 : Nat := 4983230072969 + 3 ^ 40 * 694177 * 2
def baseEnd_694177 : Nat := 105613766013699485331865

theorem tailTrace_694177 : CollatzResearch.WordTrace tailWord_694177 prefixEnd_694177 105613766013699485331865 := by
  unfold tailWord_694177
  simp only [CollatzResearch.WordTrace]
  refine ⟨25318715206122759837984785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16879143470748506558656523 25318715206122759837984785)
  ·
    refine ⟨18989036404592069878488589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25318715206122759837984785 18989036404592069878488589)
    ·
      refine ⟨7120888651722026204433221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18989036404592069878488589 7120888651722026204433221)
      ·
        refine ⟨1335166622197879913331229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7120888651722026204433221 1335166622197879913331229)
        ·
          refine ⟨500687483324204967499211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1335166622197879913331229 500687483324204967499211)
          ·
            refine ⟨751031224986307451248817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 500687483324204967499211 751031224986307451248817)
            ·
              refine ⟨563273418739730588436613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 751031224986307451248817 563273418739730588436613)
              ·
                refine ⟨105613766013699485331865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 563273418739730588436613 105613766013699485331865)
                ·
                  rfl

theorem cell20_694177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 2, 4].length) (baseStart_694177 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_694177 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_694177 prefixEnd_694177 := by exact prefixLift 694177
  have htrace : WordTrace (prefixWord ++ tailWord_694177) baseStart_694177 baseEnd_694177 := by
    simpa [prefixWord, tailWord_694177, baseEnd_694177] using wordTrace_append hprefix tailTrace_694177
  have hstable : (prefixWord ++ tailWord_694177).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694177).length < 2 ^ (prefixWord ++ tailWord_694177).sum := by decide
  have hdescent : baseEnd_694177 < baseStart_694177 := by decide
  rcases family_descends (prefixWord ++ tailWord_694177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694250 : List Nat := [3, 1, 3, 1, 2, 1, 2, 5, 2]
def baseStart_694250 : Nat := 118140960795 + 694250 * 2 ^ 59
def prefixEnd_694250 : Nat := 4983230072969 + 3 ^ 40 * 694250 * 2
def baseEnd_694250 : Nat := 316874617230234646561963

theorem tailTrace_694250 : CollatzResearch.WordTrace tailWord_694250 prefixEnd_694250 316874617230234646561963 := by
  unfold tailWord_694250
  simp only [CollatzResearch.WordTrace]
  refine ⟨6330344433714573326348051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16880918489905528870261469 6330344433714573326348051)
  ·
    refine ⟨9495516650571859989522077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6330344433714573326348051 9495516650571859989522077)
    ·
      refine ⟨3560818743964447496070779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9495516650571859989522077 3560818743964447496070779)
      ·
        refine ⟨5341228115946671244106169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3560818743964447496070779 5341228115946671244106169)
        ·
          refine ⟨4005921086960003433079627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5341228115946671244106169 4005921086960003433079627)
          ·
            refine ⟨6008881630440005149619441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4005921086960003433079627 6008881630440005149619441)
            ·
              refine ⟨4506661222830003862214581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6008881630440005149619441 4506661222830003862214581)
              ·
                refine ⟨422499489640312862082617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4506661222830003862214581 422499489640312862082617)
                ·
                  refine ⟨316874617230234646561963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 422499489640312862082617 316874617230234646561963)
                  ·
                    rfl

theorem cell20_694250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 5, 2].length) (baseStart_694250 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_694250 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_694250 prefixEnd_694250 := by exact prefixLift 694250
  have htrace : WordTrace (prefixWord ++ tailWord_694250) baseStart_694250 baseEnd_694250 := by
    simpa [prefixWord, tailWord_694250, baseEnd_694250] using wordTrace_append hprefix tailTrace_694250
  have hstable : (prefixWord ++ tailWord_694250).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694250).length < 2 ^ (prefixWord ++ tailWord_694250).sum := by decide
  have hdescent : baseEnd_694250 < baseStart_694250 := by decide
  rcases family_descends (prefixWord ++ tailWord_694250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694305 : List Nat := [1, 2, 3, 2, 4, 1, 2, 3, 2]
def baseStart_694305 : Nat := 118140960795 + 694305 * 2 ^ 59
def prefixEnd_694305 : Nat := 4983230072969 + 3 ^ 40 * 694305 * 2
def baseEnd_694305 : Nat := 316899720728898899728405

theorem tailTrace_694305 : CollatzResearch.WordTrace tailWord_694305 prefixEnd_694305 316899720728898899728405 := by
  unfold tailWord_694305
  simp only [CollatzResearch.WordTrace]
  refine ⟨25323383749659037698644369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16882255833106025132429579 25323383749659037698644369)
  ·
    refine ⟨18992537812244278273983277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25323383749659037698644369 18992537812244278273983277)
    ·
      refine ⟨7122201679591604352743729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18992537812244278273983277 7122201679591604352743729)
      ·
        refine ⟨5341651259693703264557797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7122201679591604352743729 5341651259693703264557797)
        ·
          refine ⟨1001559611192569362104587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5341651259693703264557797 1001559611192569362104587)
          ·
            refine ⟨1502339416788854043156881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1001559611192569362104587 1502339416788854043156881)
            ·
              refine ⟨1126754562591640532367661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1502339416788854043156881 1126754562591640532367661)
              ·
                refine ⟨422532960971865199637873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1126754562591640532367661 422532960971865199637873)
                ·
                  refine ⟨316899720728898899728405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 422532960971865199637873 316899720728898899728405)
                  ·
                    rfl

theorem cell20_694305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 2, 3, 2].length) (baseStart_694305 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_694305 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_694305 prefixEnd_694305 := by exact prefixLift 694305
  have htrace : WordTrace (prefixWord ++ tailWord_694305) baseStart_694305 baseEnd_694305 := by
    simpa [prefixWord, tailWord_694305, baseEnd_694305] using wordTrace_append hprefix tailTrace_694305
  have hstable : (prefixWord ++ tailWord_694305).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694305).length < 2 ^ (prefixWord ++ tailWord_694305).sum := by decide
  have hdescent : baseEnd_694305 < baseStart_694305 := by decide
  rcases family_descends (prefixWord ++ tailWord_694305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694326 : List Nat := [5, 1, 2, 1, 1, 1, 4, 1, 4]
def baseStart_694326 : Nat := 118140960795 + 694326 * 2 ^ 59
def prefixEnd_694326 : Nat := 4983230072969 + 3 ^ 40 * 694326 * 2
def baseEnd_694326 : Nat := 316909305701116160028319

theorem tailTrace_694326 : CollatzResearch.WordTrace tailWord_694326 prefixEnd_694326 316909305701116160028319 := by
  unfold tailWord_694326
  simp only [CollatzResearch.WordTrace]
  refine ⟨1582759355161434892822427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16882766455055305523439221 1582759355161434892822427)
  ·
    refine ⟨2374139032742152339233641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1582759355161434892822427 2374139032742152339233641)
    ·
      refine ⟨1780604274556614254425231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2374139032742152339233641 1780604274556614254425231)
      ·
        refine ⟨2670906411834921381637847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1780604274556614254425231 2670906411834921381637847)
        ·
          refine ⟨4006359617752382072456771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2670906411834921381637847 4006359617752382072456771)
          ·
            refine ⟨6009539426628573108685157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4006359617752382072456771 6009539426628573108685157)
            ·
              refine ⟨1126788642492857457878467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6009539426628573108685157 1126788642492857457878467)
              ·
                refine ⟨1690182963739286186817701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1126788642492857457878467 1690182963739286186817701)
                ·
                  refine ⟨316909305701116160028319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1690182963739286186817701 316909305701116160028319)
                  ·
                    rfl

theorem cell20_694326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_694326 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_694326 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_694326 prefixEnd_694326 := by exact prefixLift 694326
  have htrace : WordTrace (prefixWord ++ tailWord_694326) baseStart_694326 baseEnd_694326 := by
    simpa [prefixWord, tailWord_694326, baseEnd_694326] using wordTrace_append hprefix tailTrace_694326
  have hstable : (prefixWord ++ tailWord_694326).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694326).length < 2 ^ (prefixWord ++ tailWord_694326).sum := by decide
  have hdescent : baseEnd_694326 < baseStart_694326 := by decide
  rcases family_descends (prefixWord ++ tailWord_694326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694381 : List Nat := [1, 5, 1, 1, 2, 1, 5, 2, 2]
def baseStart_694381 : Nat := 118140960795 + 694381 * 2 ^ 59
def prefixEnd_694381 : Nat := 4983230072969 + 3 ^ 40 * 694381 * 2
def baseEnd_694381 : Nat := 316934409199780413194761

theorem tailTrace_694381 : CollatzResearch.WordTrace tailWord_694381 prefixEnd_694381 316934409199780413194761 := by
  unfold tailWord_694381
  simp only [CollatzResearch.WordTrace]
  refine ⟨25326155697383702678410997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16884103798255801785607331 25326155697383702678410997)
  ·
    refine ⟨2374327096629722126101031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25326155697383702678410997 2374327096629722126101031)
    ·
      refine ⟨3561490644944583189151547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2374327096629722126101031 3561490644944583189151547)
      ·
        refine ⟨5342235967416874783727321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3561490644944583189151547 5342235967416874783727321)
        ·
          refine ⟨4006676975562656087795491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5342235967416874783727321 4006676975562656087795491)
          ·
            refine ⟨6010015463343984131693237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4006676975562656087795491 6010015463343984131693237)
            ·
              refine ⟨563438949688498512346241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6010015463343984131693237 563438949688498512346241)
              ·
                refine ⟨422579212266373884259681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 563438949688498512346241 422579212266373884259681)
                ·
                  refine ⟨316934409199780413194761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 422579212266373884259681 316934409199780413194761)
                  ·
                    rfl

theorem cell20_694381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 5, 2, 2].length) (baseStart_694381 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_694381 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_694381 prefixEnd_694381 := by exact prefixLift 694381
  have htrace : WordTrace (prefixWord ++ tailWord_694381) baseStart_694381 baseEnd_694381 := by
    simpa [prefixWord, tailWord_694381, baseEnd_694381] using wordTrace_append hprefix tailTrace_694381
  have hstable : (prefixWord ++ tailWord_694381).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694381).length < 2 ^ (prefixWord ++ tailWord_694381).sum := by decide
  have hdescent : baseEnd_694381 < baseStart_694381 := by decide
  rcases family_descends (prefixWord ++ tailWord_694381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694422 : List Nat := [5, 3, 2, 1, 2, 7]
def baseStart_694422 : Nat := 118140960795 + 694422 * 2 ^ 59
def prefixEnd_694422 : Nat := 4983230072969 + 3 ^ 40 * 694422 * 2
def baseEnd_694422 : Nat := 11739004545072833067701

theorem tailTrace_694422 : CollatzResearch.WordTrace tailWord_694422 prefixEnd_694422 11739004545072833067701 := by
  unfold tailWord_694422
  simp only [CollatzResearch.WordTrace]
  refine ⟨1582978193139697917540845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16885100726823444453769013 1582978193139697917540845)
  ·
    refine ⟨593616822427386719077817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1582978193139697917540845 593616822427386719077817)
    ·
      refine ⟨445212616820540039308363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 593616822427386719077817 445212616820540039308363)
      ·
        refine ⟨667818925230810058962545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 445212616820540039308363 667818925230810058962545)
        ·
          refine ⟨500864193923107544221909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 667818925230810058962545 500864193923107544221909)
          ·
            refine ⟨11739004545072833067701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 500864193923107544221909 11739004545072833067701)
            ·
              rfl

theorem cell20_694422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 7].length) (baseStart_694422 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_694422 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_694422 prefixEnd_694422 := by exact prefixLift 694422
  have htrace : WordTrace (prefixWord ++ tailWord_694422) baseStart_694422 baseEnd_694422 := by
    simpa [prefixWord, tailWord_694422, baseEnd_694422] using wordTrace_append hprefix tailTrace_694422
  have hstable : (prefixWord ++ tailWord_694422).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694422).length < 2 ^ (prefixWord ++ tailWord_694422).sum := by decide
  have hdescent : baseEnd_694422 < baseStart_694422 := by decide
  rcases family_descends (prefixWord ++ tailWord_694422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694430 : List Nat := [4, 3, 1, 1, 11]
def baseStart_694430 : Nat := 118140960795 + 694430 * 2 ^ 59
def prefixEnd_694430 : Nat := 4983230072969 + 3 ^ 40 * 694430 * 2
def baseEnd_694430 : Nat := 3913046594258691611867

theorem tailTrace_694430 : CollatzResearch.WordTrace tailWord_694430 prefixEnd_694430 3913046594258691611867 := by
  unfold tailWord_694430
  simp only [CollatzResearch.WordTrace]
  refine ⟨3165992859275773005868093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16885295249470789364629829 3165992859275773005868093)
  ·
    refine ⟨1187247322228414877200535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3165992859275773005868093 1187247322228414877200535)
    ·
      refine ⟨1780870983342622315800803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1187247322228414877200535 1780870983342622315800803)
      ·
        refine ⟨2671306475013933473701205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1780870983342622315800803 2671306475013933473701205)
        ·
          refine ⟨3913046594258691611867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 2671306475013933473701205 3913046594258691611867)
          ·
            rfl

theorem cell20_694430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 11].length) (baseStart_694430 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_694430 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_694430 prefixEnd_694430 := by exact prefixLift 694430
  have htrace : WordTrace (prefixWord ++ tailWord_694430) baseStart_694430 baseEnd_694430 := by
    simpa [prefixWord, tailWord_694430, baseEnd_694430] using wordTrace_append hprefix tailTrace_694430
  have hstable : (prefixWord ++ tailWord_694430).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694430).length < 2 ^ (prefixWord ++ tailWord_694430).sum := by decide
  have hdescent : baseEnd_694430 < baseStart_694430 := by decide
  rcases family_descends (prefixWord ++ tailWord_694430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694436 : List Nat := [2, 3, 1, 2, 4, 2, 2, 2, 2]
def baseStart_694436 : Nat := 118140960795 + 694436 * 2 ^ 59
def prefixEnd_694436 : Nat := 4983230072969 + 3 ^ 40 * 694436 * 2
def baseEnd_694436 : Nat := 316959512698444666361203

theorem tailTrace_694436 : CollatzResearch.WordTrace tailWord_694436 prefixEnd_694436 316959512698444666361203 := by
  unfold tailWord_694436
  simp only [CollatzResearch.WordTrace]
  refine ⟨12664080856092223535831581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16885441141456298047775441 12664080856092223535831581)
  ·
    refine ⟨4749030321034583825936843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12664080856092223535831581 4749030321034583825936843)
    ·
      refine ⟨7123545481551875738905265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4749030321034583825936843 7123545481551875738905265)
      ·
        refine ⟨5342659111163906804178949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7123545481551875738905265 5342659111163906804178949)
        ·
          refine ⟨1001748583343232525783553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5342659111163906804178949 1001748583343232525783553)
          ·
            refine ⟨751311437507424394337665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1001748583343232525783553 751311437507424394337665)
            ·
              refine ⟨563483578130568295753249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 751311437507424394337665 563483578130568295753249)
              ·
                refine ⟨422612683597926221814937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 563483578130568295753249 422612683597926221814937)
                ·
                  refine ⟨316959512698444666361203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 422612683597926221814937 316959512698444666361203)
                  ·
                    rfl

theorem cell20_694436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 2, 2, 2].length) (baseStart_694436 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_694436 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_694436 prefixEnd_694436 := by exact prefixLift 694436
  have htrace : WordTrace (prefixWord ++ tailWord_694436) baseStart_694436 baseEnd_694436 := by
    simpa [prefixWord, tailWord_694436, baseEnd_694436] using wordTrace_append hprefix tailTrace_694436
  have hstable : (prefixWord ++ tailWord_694436).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694436).length < 2 ^ (prefixWord ++ tailWord_694436).sum := by decide
  have hdescent : baseEnd_694436 < baseStart_694436 := by decide
  rcases family_descends (prefixWord ++ tailWord_694436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694478 : List Nat := [4, 1, 1, 1, 4, 1, 1, 5, 2]
def baseStart_694478 : Nat := 118140960795 + 694478 * 2 ^ 59
def prefixEnd_694478 : Nat := 4983230072969 + 3 ^ 40 * 694478 * 2
def baseEnd_694478 : Nat := 316978682642879186961031

theorem tailTrace_694478 : CollatzResearch.WordTrace tailWord_694478 prefixEnd_694478 316978682642879186961031 := by
  unfold tailWord_694478
  simp only [CollatzResearch.WordTrace]
  refine ⟨3166211697254036030586511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16886462385354858829794725 3166211697254036030586511)
  ·
    refine ⟨4749317545881054045879767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3166211697254036030586511 4749317545881054045879767)
    ·
      refine ⟨7123976318821581068819651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4749317545881054045879767 7123976318821581068819651)
      ·
        refine ⟨10685964478232371603229477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7123976318821581068819651 10685964478232371603229477)
        ·
          refine ⟨2003618339668569675605527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10685964478232371603229477 2003618339668569675605527)
          ·
            refine ⟨3005427509502854513408291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2003618339668569675605527 3005427509502854513408291)
            ·
              refine ⟨4508141264254281770112437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3005427509502854513408291 4508141264254281770112437)
              ·
                refine ⟨422638243523838915948041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4508141264254281770112437 422638243523838915948041)
                ·
                  refine ⟨316978682642879186961031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 422638243523838915948041 316978682642879186961031)
                  ·
                    rfl

theorem cell20_694478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 5, 2].length) (baseStart_694478 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_694478 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_694478 prefixEnd_694478 := by exact prefixLift 694478
  have htrace : WordTrace (prefixWord ++ tailWord_694478) baseStart_694478 baseEnd_694478 := by
    simpa [prefixWord, tailWord_694478, baseEnd_694478] using wordTrace_append hprefix tailTrace_694478
  have hstable : (prefixWord ++ tailWord_694478).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694478).length < 2 ^ (prefixWord ++ tailWord_694478).sum := by decide
  have hdescent : baseEnd_694478 < baseStart_694478 := by decide
  rcases family_descends (prefixWord ++ tailWord_694478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694513 : List Nat := [1, 2, 2, 2, 2, 1, 2, 5, 3]
def baseStart_694513 : Nat := 118140960795 + 694513 * 2 ^ 59
def prefixEnd_694513 : Nat := 4983230072969 + 3 ^ 40 * 694513 * 2
def baseEnd_694513 : Nat := 316994657596574620794221

theorem tailTrace_694513 : CollatzResearch.WordTrace tailWord_694513 prefixEnd_694513 316994657596574620794221 := by
  unfold tailWord_694513
  simp only [CollatzResearch.WordTrace]
  refine ⟨25330970132905489222216193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16887313421936992814810795 25330970132905489222216193)
  ·
    refine ⟨18998227599679116916662145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25330970132905489222216193 18998227599679116916662145)
    ·
      refine ⟨14248670699759337687496609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18998227599679116916662145 14248670699759337687496609)
      ·
        refine ⟨10686503024819503265622457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14248670699759337687496609 10686503024819503265622457)
        ·
          refine ⟨8014877268614627449216843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10686503024819503265622457 8014877268614627449216843)
          ·
            refine ⟨12022315902921941173825265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8014877268614627449216843 12022315902921941173825265)
            ·
              refine ⟨9016736927191455880368949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12022315902921941173825265 9016736927191455880368949)
              ·
                refine ⟨845319086924198988784589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9016736927191455880368949 845319086924198988784589)
                ·
                  refine ⟨316994657596574620794221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 845319086924198988784589 316994657596574620794221)
                  ·
                    rfl

theorem cell20_694513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 5, 3].length) (baseStart_694513 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_694513 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_694513 prefixEnd_694513 := by exact prefixLift 694513
  have htrace : WordTrace (prefixWord ++ tailWord_694513) baseStart_694513 baseEnd_694513 := by
    simpa [prefixWord, tailWord_694513, baseEnd_694513] using wordTrace_append hprefix tailTrace_694513
  have hstable : (prefixWord ++ tailWord_694513).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694513).length < 2 ^ (prefixWord ++ tailWord_694513).sum := by decide
  have hdescent : baseEnd_694513 < baseStart_694513 := by decide
  rcases family_descends (prefixWord ++ tailWord_694513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694527 : List Nat := [1, 1, 2, 2, 1, 4, 3, 6]
def baseStart_694527 : Nat := 118140960795 + 694527 * 2 ^ 59
def prefixEnd_694527 : Nat := 4983230072969 + 3 ^ 40 * 694527 * 2
def baseEnd_694527 : Nat := 105667015859350931442499

theorem tailTrace_694527 : CollatzResearch.WordTrace tailWord_694527 prefixEnd_694527 105667015859350931442499 := by
  unfold tailWord_694527
  simp only [CollatzResearch.WordTrace]
  refine ⟨25331480754854769613225835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16887653836569846408817223 25331480754854769613225835)
  ·
    refine ⟨37997221132282154419838753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25331480754854769613225835 37997221132282154419838753)
    ·
      refine ⟨28497915849211615814879065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37997221132282154419838753 28497915849211615814879065)
      ·
        refine ⟨21373436886908711861159299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28497915849211615814879065 21373436886908711861159299)
        ·
          refine ⟨32060155330363067791738949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21373436886908711861159299 32060155330363067791738949)
          ·
            refine ⟨6011279124443075210951053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32060155330363067791738949 6011279124443075210951053)
            ·
              refine ⟨2254229671666153204106645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6011279124443075210951053 2254229671666153204106645)
              ·
                refine ⟨105667015859350931442499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2254229671666153204106645 105667015859350931442499)
                ·
                  rfl

theorem cell20_694527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 6].length) (baseStart_694527 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_694527 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_694527 prefixEnd_694527 := by exact prefixLift 694527
  have htrace : WordTrace (prefixWord ++ tailWord_694527) baseStart_694527 baseEnd_694527 := by
    simpa [prefixWord, tailWord_694527, baseEnd_694527] using wordTrace_append hprefix tailTrace_694527
  have hstable : (prefixWord ++ tailWord_694527).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694527).length < 2 ^ (prefixWord ++ tailWord_694527).sum := by decide
  have hdescent : baseEnd_694527 < baseStart_694527 := by decide
  rcases family_descends (prefixWord ++ tailWord_694527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694530 : List Nat := [3, 4, 1, 1, 2, 1, 1, 2, 5]
def baseStart_694530 : Nat := 118140960795 + 694530 * 2 ^ 59
def prefixEnd_694530 : Nat := 4983230072969 + 3 ^ 40 * 694530 * 2
def baseEnd_694530 : Nat := 317002416859798117227485

theorem tailTrace_694530 : CollatzResearch.WordTrace tailWord_694530 prefixEnd_694530 317002416859798117227485 := by
  unfold tailWord_694530
  simp only [CollatzResearch.WordTrace]
  refine ⟨6332897543460975281396261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16887726782562600750390029 6332897543460975281396261)
  ·
    refine ⟨1187418289398932865261799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6332897543460975281396261 1187418289398932865261799)
    ·
      refine ⟨1781127434098399297892699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1187418289398932865261799 1781127434098399297892699)
      ·
        refine ⟨2671691151147598946839049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1781127434098399297892699 2671691151147598946839049)
        ·
          refine ⟨2003768363360699210129287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2671691151147598946839049 2003768363360699210129287)
          ·
            refine ⟨3005652545041048815193931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2003768363360699210129287 3005652545041048815193931)
            ·
              refine ⟨4508478817561573222790897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3005652545041048815193931 4508478817561573222790897)
              ·
                refine ⟨3381359113171179917093173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4508478817561573222790897 3381359113171179917093173)
                ·
                  refine ⟨317002416859798117227485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3381359113171179917093173 317002416859798117227485)
                  ·
                    rfl

theorem cell20_694530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_694530 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_694530 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_694530 prefixEnd_694530 := by exact prefixLift 694530
  have htrace : WordTrace (prefixWord ++ tailWord_694530) baseStart_694530 baseEnd_694530 := by
    simpa [prefixWord, tailWord_694530, baseEnd_694530] using wordTrace_append hprefix tailTrace_694530
  have hstable : (prefixWord ++ tailWord_694530).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694530).length < 2 ^ (prefixWord ++ tailWord_694530).sum := by decide
  have hdescent : baseEnd_694530 < baseStart_694530 := by decide
  rcases family_descends (prefixWord ++ tailWord_694530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694551 : List Nat := [1, 1, 3, 4, 1, 2, 2, 1, 5]
def baseStart_694551 : Nat := 118140960795 + 694551 * 2 ^ 59
def prefixEnd_694551 : Nat := 4983230072969 + 3 ^ 40 * 694551 * 2
def baseEnd_694551 : Nat := 317012001832015377527399

theorem tailTrace_694551 : CollatzResearch.WordTrace tailWord_694551 prefixEnd_694551 317012001832015377527399 := by
  unfold tailWord_694551
  simp only [CollatzResearch.WordTrace]
  refine ⟨25332356106767821712099507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16888237404511881141399671 25332356106767821712099507)
  ·
    refine ⟨37998534160151732568149261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25332356106767821712099507 37998534160151732568149261)
    ·
      refine ⟨14249450310056899713055973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37998534160151732568149261 14249450310056899713055973)
      ·
        refine ⟨2671771933135668696197995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14249450310056899713055973 2671771933135668696197995)
        ·
          refine ⟨4007657899703503044296993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2671771933135668696197995 4007657899703503044296993)
          ·
            refine ⟨3005743424777627283222745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4007657899703503044296993 3005743424777627283222745)
            ·
              refine ⟨2254307568583220462417059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3005743424777627283222745 2254307568583220462417059)
              ·
                refine ⟨3381461352874830693625589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2254307568583220462417059 3381461352874830693625589)
                ·
                  refine ⟨317012001832015377527399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3381461352874830693625589 317012001832015377527399)
                  ·
                    rfl

theorem cell20_694551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 1, 5].length) (baseStart_694551 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_694551 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_694551 prefixEnd_694551 := by exact prefixLift 694551
  have htrace : WordTrace (prefixWord ++ tailWord_694551) baseStart_694551 baseEnd_694551 := by
    simpa [prefixWord, tailWord_694551, baseEnd_694551] using wordTrace_append hprefix tailTrace_694551
  have hstable : (prefixWord ++ tailWord_694551).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694551).length < 2 ^ (prefixWord ++ tailWord_694551).sum := by decide
  have hdescent : baseEnd_694551 < baseStart_694551 := by decide
  rcases family_descends (prefixWord ++ tailWord_694551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694554 : List Nat := [3, 1, 1, 3, 4, 2, 1, 1, 4]
def baseStart_694554 : Nat := 118140960795 + 694554 * 2 ^ 59
def prefixEnd_694554 : Nat := 4983230072969 + 3 ^ 40 * 694554 * 2
def baseEnd_694554 : Nat := 317013371113760700427387

theorem tailTrace_694554 : CollatzResearch.WordTrace tailWord_694554 prefixEnd_694554 317013371113760700427387 := by
  unfold tailWord_694554
  simp only [CollatzResearch.WordTrace]
  refine ⟨6333116381439238306114679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16888310350504635482972477 6333116381439238306114679)
  ·
    refine ⟨9499674572158857459172019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6333116381439238306114679 9499674572158857459172019)
    ·
      refine ⟨14249511858238286188758029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9499674572158857459172019 14249511858238286188758029)
      ·
        refine ⟨5343566946839357320784261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14249511858238286188758029 5343566946839357320784261)
        ·
          refine ⟨1001918802532379497647049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5343566946839357320784261 1001918802532379497647049)
          ·
            refine ⟨751439101899284623235287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1001918802532379497647049 751439101899284623235287)
            ·
              refine ⟨1127158652848926934852931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 751439101899284623235287 1127158652848926934852931)
              ·
                refine ⟨1690737979273390402279397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1127158652848926934852931 1690737979273390402279397)
                ·
                  refine ⟨317013371113760700427387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1690737979273390402279397 317013371113760700427387)
                  ·
                    rfl

theorem cell20_694554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 1, 1, 4].length) (baseStart_694554 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_694554 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_694554 prefixEnd_694554 := by exact prefixLift 694554
  have htrace : WordTrace (prefixWord ++ tailWord_694554) baseStart_694554 baseEnd_694554 := by
    simpa [prefixWord, tailWord_694554, baseEnd_694554] using wordTrace_append hprefix tailTrace_694554
  have hstable : (prefixWord ++ tailWord_694554).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694554).length < 2 ^ (prefixWord ++ tailWord_694554).sum := by decide
  have hdescent : baseEnd_694554 < baseStart_694554 := by decide
  rcases family_descends (prefixWord ++ tailWord_694554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694609 : List Nat := [1, 2, 2, 1, 4, 4, 2, 2, 2]
def baseStart_694609 : Nat := 118140960795 + 694609 * 2 ^ 59
def prefixEnd_694609 : Nat := 4983230072969 + 3 ^ 40 * 694609 * 2
def baseEnd_694609 : Nat := 317038474612424953593829

theorem tailTrace_694609 : CollatzResearch.WordTrace tailWord_694609 prefixEnd_694609 317038474612424953593829 := by
  unfold tailWord_694609
  simp only [CollatzResearch.WordTrace]
  refine ⟨25334471540557697617710881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16889647693705131745140587 25334471540557697617710881)
  ·
    refine ⟨19000853655418273213283161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25334471540557697617710881 19000853655418273213283161)
    ·
      refine ⟨14250640241563704909962371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19000853655418273213283161 14250640241563704909962371)
      ·
        refine ⟨21375960362345557364943557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14250640241563704909962371 21375960362345557364943557)
        ·
          refine ⟨4007992567939792005926917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21375960362345557364943557 4007992567939792005926917)
          ·
            refine ⟨751498606488711001111297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4007992567939792005926917 751498606488711001111297)
            ·
              refine ⟨563623954866533250833473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 751498606488711001111297 563623954866533250833473)
              ·
                refine ⟨422717966149899938125105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 563623954866533250833473 422717966149899938125105)
                ·
                  refine ⟨317038474612424953593829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 422717966149899938125105 317038474612424953593829)
                  ·
                    rfl

theorem cell20_694609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 2, 2, 2].length) (baseStart_694609 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_694609 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_694609 prefixEnd_694609 := by exact prefixLift 694609
  have htrace : WordTrace (prefixWord ++ tailWord_694609) baseStart_694609 baseEnd_694609 := by
    simpa [prefixWord, tailWord_694609, baseEnd_694609] using wordTrace_append hprefix tailTrace_694609
  have hstable : (prefixWord ++ tailWord_694609).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694609).length < 2 ^ (prefixWord ++ tailWord_694609).sum := by decide
  have hdescent : baseEnd_694609 < baseStart_694609 := by decide
  rcases family_descends (prefixWord ++ tailWord_694609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694627 : List Nat := [1, 1, 1, 5, 2, 1, 1, 5, 3]
def baseStart_694627 : Nat := 118140960795 + 694627 * 2 ^ 59
def prefixEnd_694627 : Nat := 4983230072969 + 3 ^ 40 * 694627 * 2
def baseEnd_694627 : Nat := 317046690302896890993755

theorem tailTrace_694627 : CollatzResearch.WordTrace tailWord_694627 prefixEnd_694627 317046690302896890993755 := by
  unfold tailWord_694627
  simp only [CollatzResearch.WordTrace]
  refine ⟨25335128054492486691866135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16890085369661657794577423 25335128054492486691866135)
  ·
    refine ⟨38002692081738730037799203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25335128054492486691866135 38002692081738730037799203)
    ·
      refine ⟨57004038122608095056698805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38002692081738730037799203 57004038122608095056698805)
      ·
        refine ⟨5344128573994508911565513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 57004038122608095056698805 5344128573994508911565513)
        ·
          refine ⟨4008096430495881683674135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5344128573994508911565513 4008096430495881683674135)
          ·
            refine ⟨6012144645743822525511203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4008096430495881683674135 6012144645743822525511203)
            ·
              refine ⟨9018216968615733788266805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6012144645743822525511203 9018216968615733788266805)
              ·
                refine ⟨845457840807725042650013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9018216968615733788266805 845457840807725042650013)
                ·
                  refine ⟨317046690302896890993755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 845457840807725042650013 317046690302896890993755)
                  ·
                    rfl

theorem cell20_694627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 5, 3].length) (baseStart_694627 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_694627 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_694627 prefixEnd_694627 := by exact prefixLift 694627
  have htrace : WordTrace (prefixWord ++ tailWord_694627) baseStart_694627 baseEnd_694627 := by
    simpa [prefixWord, tailWord_694627, baseEnd_694627] using wordTrace_append hprefix tailTrace_694627
  have hstable : (prefixWord ++ tailWord_694627).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694627).length < 2 ^ (prefixWord ++ tailWord_694627).sum := by decide
  have hdescent : baseEnd_694627 < baseStart_694627 := by decide
  rcases family_descends (prefixWord ++ tailWord_694627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694651 : List Nat := [1, 1, 1, 1, 1, 7, 1, 5, 2]
def baseStart_694651 : Nat := 118140960795 + 694651 * 2 ^ 59
def prefixEnd_694651 : Nat := 4983230072969 + 3 ^ 40 * 694651 * 2
def baseEnd_694651 : Nat := 317057644556859474193657

theorem tailTrace_694651 : CollatzResearch.WordTrace tailWord_694651 prefixEnd_694651 317057644556859474193657 := by
  unfold tailWord_694651
  simp only [CollatzResearch.WordTrace]
  refine ⟨25336003406405538790739807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16890668937603692527159871 25336003406405538790739807)
  ·
    refine ⟨38004005109608308186109711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25336003406405538790739807 38004005109608308186109711)
    ·
      refine ⟨57006007664412462279164567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38004005109608308186109711 57006007664412462279164567)
      ·
        refine ⟨85509011496618693418746851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57006007664412462279164567 85509011496618693418746851)
        ·
          refine ⟨128263517244928040128120277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85509011496618693418746851 128263517244928040128120277)
          ·
            refine ⟨3006176185428000940502819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 128263517244928040128120277 3006176185428000940502819)
            ·
              refine ⟨4509264278142001410754229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3006176185428000940502819 4509264278142001410754229)
              ·
                refine ⟨422743526075812632258209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4509264278142001410754229 422743526075812632258209)
                ·
                  refine ⟨317057644556859474193657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 422743526075812632258209 317057644556859474193657)
                  ·
                    rfl

theorem cell20_694651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 5, 2].length) (baseStart_694651 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_694651 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_694651 prefixEnd_694651 := by exact prefixLift 694651
  have htrace : WordTrace (prefixWord ++ tailWord_694651) baseStart_694651 baseEnd_694651 := by
    simpa [prefixWord, tailWord_694651, baseEnd_694651] using wordTrace_append hprefix tailTrace_694651
  have hstable : (prefixWord ++ tailWord_694651).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694651).length < 2 ^ (prefixWord ++ tailWord_694651).sum := by decide
  have hdescent : baseEnd_694651 < baseStart_694651 := by decide
  rcases family_descends (prefixWord ++ tailWord_694651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694665 : List Nat := [1, 2, 1, 1, 6, 2, 1, 1, 5]
def baseStart_694665 : Nat := 118140960795 + 694665 * 2 ^ 59
def prefixEnd_694665 : Nat := 4983230072969 + 3 ^ 40 * 694665 * 2
def baseEnd_694665 : Nat := 317064034538337647726933

theorem tailTrace_694665 : CollatzResearch.WordTrace tailWord_694665 prefixEnd_694665 317064034538337647726933 := by
  unfold tailWord_694665
  simp only [CollatzResearch.WordTrace]
  refine ⟨25336514028354819181749449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16891009352236546121166299 25336514028354819181749449)
  ·
    refine ⟨19002385521266114386312087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25336514028354819181749449 19002385521266114386312087)
    ·
      refine ⟨28503578281899171579468131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19002385521266114386312087 28503578281899171579468131)
      ·
        refine ⟨42755367422848757369202197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28503578281899171579468131 42755367422848757369202197)
        ·
          refine ⟨2004157847946035501681353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 42755367422848757369202197 2004157847946035501681353)
          ·
            refine ⟨1503118385959526626261015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2004157847946035501681353 1503118385959526626261015)
            ·
              refine ⟨2254677578939289939391523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1503118385959526626261015 2254677578939289939391523)
              ·
                refine ⟨3382016368408934909087285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2254677578939289939391523 3382016368408934909087285)
                ·
                  refine ⟨317064034538337647726933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3382016368408934909087285 317064034538337647726933)
                  ·
                    rfl

theorem cell20_694665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 1, 5].length) (baseStart_694665 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_694665 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_694665 prefixEnd_694665 := by exact prefixLift 694665
  have htrace : WordTrace (prefixWord ++ tailWord_694665) baseStart_694665 baseEnd_694665 := by
    simpa [prefixWord, tailWord_694665, baseEnd_694665] using wordTrace_append hprefix tailTrace_694665
  have hstable : (prefixWord ++ tailWord_694665).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694665).length < 2 ^ (prefixWord ++ tailWord_694665).sum := by decide
  have hdescent : baseEnd_694665 < baseStart_694665 := by decide
  rcases family_descends (prefixWord ++ tailWord_694665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694698 : List Nat := [3, 1, 6, 1, 2, 1, 1, 3, 2]
def baseStart_694698 : Nat := 118140960795 + 694698 * 2 ^ 59
def prefixEnd_694698 : Nat := 4983230072969 + 3 ^ 40 * 694698 * 2
def baseEnd_694698 : Nat := 317079096637536199626799

theorem tailTrace_694698 : CollatzResearch.WordTrace tailWord_694698 prefixEnd_694698 317079096637536199626799 := by
  unfold tailWord_694698
  simp only [CollatzResearch.WordTrace]
  refine ⟨6334429409308816454425187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16891811758156843878467165 6334429409308816454425187)
  ·
    refine ⟨9501644113963224681637781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6334429409308816454425187 9501644113963224681637781)
    ·
      refine ⟨445389567842026156951771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 9501644113963224681637781 445389567842026156951771)
      ·
        refine ⟨668084351763039235427657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 445389567842026156951771 668084351763039235427657)
        ·
          refine ⟨501063263822279426570743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 668084351763039235427657 501063263822279426570743)
          ·
            refine ⟨751594895733419139856115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 501063263822279426570743 751594895733419139856115)
            ·
              refine ⟨1127392343600128709784173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 751594895733419139856115 1127392343600128709784173)
              ·
                refine ⟨422772128850048266169065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1127392343600128709784173 422772128850048266169065)
                ·
                  refine ⟨317079096637536199626799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 422772128850048266169065 317079096637536199626799)
                  ·
                    rfl

theorem cell20_694698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 1, 3, 2].length) (baseStart_694698 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_694698 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_694698 prefixEnd_694698 := by exact prefixLift 694698
  have htrace : WordTrace (prefixWord ++ tailWord_694698) baseStart_694698 baseEnd_694698 := by
    simpa [prefixWord, tailWord_694698, baseEnd_694698] using wordTrace_append hprefix tailTrace_694698
  have hstable : (prefixWord ++ tailWord_694698).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694698).length < 2 ^ (prefixWord ++ tailWord_694698).sum := by decide
  have hdescent : baseEnd_694698 < baseStart_694698 := by decide
  rcases family_descends (prefixWord ++ tailWord_694698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694717 : List Nat := [1, 4, 1, 2, 2, 2, 8]
def baseStart_694717 : Nat := 118140960795 + 694717 * 2 ^ 59
def prefixEnd_694717 : Nat := 4983230072969 + 3 ^ 40 * 694717 * 2
def baseEnd_694717 : Nat := 35231974306139619777043

theorem tailTrace_694717 : CollatzResearch.WordTrace tailWord_694717 prefixEnd_694717 35231974306139619777043 := by
  unfold tailWord_694717
  simp only [CollatzResearch.WordTrace]
  refine ⟨25338410624166432062642405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16892273749444288041761603 25338410624166432062642405)
  ·
    refine ⟨4750951992031206011745451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25338410624166432062642405 4750951992031206011745451)
    ·
      refine ⟨7126427988046809017618177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4750951992031206011745451 7126427988046809017618177)
      ·
        refine ⟨5344820991035106763213633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7126427988046809017618177 5344820991035106763213633)
        ·
          refine ⟨4008615743276330072410225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5344820991035106763213633 4008615743276330072410225)
          ·
            refine ⟨3006461807457247554307669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4008615743276330072410225 3006461807457247554307669)
            ·
              refine ⟨35231974306139619777043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3006461807457247554307669 35231974306139619777043)
              ·
                rfl

theorem cell20_694717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 8].length) (baseStart_694717 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_694717 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_694717 prefixEnd_694717 := by exact prefixLift 694717
  have htrace : WordTrace (prefixWord ++ tailWord_694717) baseStart_694717 baseEnd_694717 := by
    simpa [prefixWord, tailWord_694717, baseEnd_694717] using wordTrace_append hprefix tailTrace_694717
  have hstable : (prefixWord ++ tailWord_694717).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694717).length < 2 ^ (prefixWord ++ tailWord_694717).sum := by decide
  have hdescent : baseEnd_694717 < baseStart_694717 := by decide
  rcases family_descends (prefixWord ++ tailWord_694717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694727 : List Nat := [1, 1, 4, 1, 1, 6, 1, 1, 4]
def baseStart_694727 : Nat := 118140960795 + 694727 * 2 ^ 59
def prefixEnd_694727 : Nat := 4983230072969 + 3 ^ 40 * 694727 * 2
def baseEnd_694727 : Nat := 317092333027740987660013

theorem tailTrace_694727 : CollatzResearch.WordTrace tailWord_694727 prefixEnd_694727 317092333027740987660013 := by
  unfold tailWord_694727
  simp only [CollatzResearch.WordTrace]
  refine ⟨25338775354130203770506435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16892516902753469180337623 25338775354130203770506435)
  ·
    refine ⟨38008163031195305655759653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25338775354130203770506435 38008163031195305655759653)
    ·
      refine ⟨7126530568349119810454935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38008163031195305655759653 7126530568349119810454935)
      ·
        refine ⟨10689795852523679715682403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7126530568349119810454935 10689795852523679715682403)
        ·
          refine ⟨16034693778785519573523605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10689795852523679715682403 16034693778785519573523605)
          ·
            refine ⟨751626270880571230008919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 16034693778785519573523605 751626270880571230008919)
            ·
              refine ⟨1127439406320856845013379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 751626270880571230008919 1127439406320856845013379)
              ·
                refine ⟨1691159109481285267520069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1127439406320856845013379 1691159109481285267520069)
                ·
                  refine ⟨317092333027740987660013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1691159109481285267520069 317092333027740987660013)
                  ·
                    rfl

theorem cell20_694727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 1, 1, 4].length) (baseStart_694727 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_694727 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_694727 prefixEnd_694727 := by exact prefixLift 694727
  have htrace : WordTrace (prefixWord ++ tailWord_694727) baseStart_694727 baseEnd_694727 := by
    simpa [prefixWord, tailWord_694727, baseEnd_694727] using wordTrace_append hprefix tailTrace_694727
  have hstable : (prefixWord ++ tailWord_694727).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694727).length < 2 ^ (prefixWord ++ tailWord_694727).sum := by decide
  have hdescent : baseEnd_694727 < baseStart_694727 := by decide
  rcases family_descends (prefixWord ++ tailWord_694727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694830 : List Nat := [4, 1, 3, 1, 4, 1, 1, 2, 3]
def baseStart_694830 : Nat := 118140960795 + 694830 * 2 ^ 59
def prefixEnd_694830 : Nat := 4983230072969 + 3 ^ 40 * 694830 * 2
def baseEnd_694830 : Nat := 317139345034330407226259

theorem tailTrace_694830 : CollatzResearch.WordTrace tailWord_694830 prefixEnd_694830 317139345034330407226259 := by
  unfold tailWord_694830
  simp only [CollatzResearch.WordTrace]
  refine ⟨3167816509094631545188243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16895021381838034907670629 3167816509094631545188243)
  ·
    refine ⟨4751724763641947317782365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3167816509094631545188243 4751724763641947317782365)
    ·
      refine ⟨1781896786365730244168387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4751724763641947317782365 1781896786365730244168387)
      ·
        refine ⟨2672845179548595366252581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1781896786365730244168387 2672845179548595366252581)
        ·
          refine ⟨501158471165361631172359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2672845179548595366252581 501158471165361631172359)
          ·
            refine ⟨751737706748042446758539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 501158471165361631172359 751737706748042446758539)
            ·
              refine ⟨1127606560122063670137809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 751737706748042446758539 1127606560122063670137809)
              ·
                refine ⟨845704920091547752603357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1127606560122063670137809 845704920091547752603357)
                ·
                  refine ⟨317139345034330407226259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 845704920091547752603357 317139345034330407226259)
                  ·
                    rfl

theorem cell20_694830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 1, 2, 3].length) (baseStart_694830 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_694830 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_694830 prefixEnd_694830 := by exact prefixLift 694830
  have htrace : WordTrace (prefixWord ++ tailWord_694830) baseStart_694830 baseEnd_694830 := by
    simpa [prefixWord, tailWord_694830, baseEnd_694830] using wordTrace_append hprefix tailTrace_694830
  have hstable : (prefixWord ++ tailWord_694830).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694830).length < 2 ^ (prefixWord ++ tailWord_694830).sum := by decide
  have hdescent : baseEnd_694830 < baseStart_694830 := by decide
  rcases family_descends (prefixWord ++ tailWord_694830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694841 : List Nat := [1, 2, 1, 5, 1, 1, 1, 6, 2]
def baseStart_694841 : Nat := 118140960795 + 694841 * 2 ^ 59
def prefixEnd_694841 : Nat := 4983230072969 + 3 ^ 40 * 694841 * 2
def baseEnd_694841 : Nat := 317144365734063257859547

theorem tailTrace_694841 : CollatzResearch.WordTrace tailWord_694841 prefixEnd_694841 317144365734063257859547 := by
  unfold tailWord_694841
  simp only [CollatzResearch.WordTrace]
  refine ⟨25342933275717201240156377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16895288850478134160104251 25342933275717201240156377)
  ·
    refine ⟨19007199956787900930117283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25342933275717201240156377 19007199956787900930117283)
    ·
      refine ⟨28510799935181851395175925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19007199956787900930117283 28510799935181851395175925)
      ·
        refine ⟨2672887493923298568297743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28510799935181851395175925 2672887493923298568297743)
        ·
          refine ⟨4009331240884947852446615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2672887493923298568297743 4009331240884947852446615)
          ·
            refine ⟨6013996861327421778669923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4009331240884947852446615 6013996861327421778669923)
            ·
              refine ⟨9020995291991132668004885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6013996861327421778669923 9020995291991132668004885)
              ·
                refine ⟨422859154312084343812729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9020995291991132668004885 422859154312084343812729)
                ·
                  refine ⟨317144365734063257859547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 422859154312084343812729 317144365734063257859547)
                  ·
                    rfl

theorem cell20_694841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 6, 2].length) (baseStart_694841 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_694841 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_694841 prefixEnd_694841 := by exact prefixLift 694841
  have htrace : WordTrace (prefixWord ++ tailWord_694841) baseStart_694841 baseEnd_694841 := by
    simpa [prefixWord, tailWord_694841, baseEnd_694841] using wordTrace_append hprefix tailTrace_694841
  have hstable : (prefixWord ++ tailWord_694841).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694841).length < 2 ^ (prefixWord ++ tailWord_694841).sum := by decide
  have hdescent : baseEnd_694841 < baseStart_694841 := by decide
  rcases family_descends (prefixWord ++ tailWord_694841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694862 : List Nat := [4, 1, 1, 1, 1, 2, 4, 2, 4]
def baseStart_694862 : Nat := 118140960795 + 694862 * 2 ^ 59
def prefixEnd_694862 : Nat := 4983230072969 + 3 ^ 40 * 694862 * 2
def baseEnd_694862 : Nat := 317153950706280518159461

theorem tailTrace_694862 : CollatzResearch.WordTrace tailWord_694862 prefixEnd_694862 317153950706280518159461 := by
  unfold tailWord_694862
  simp only [CollatzResearch.WordTrace]
  refine ⟨3167962401080140228333855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16895799472427414551113893 3167962401080140228333855)
  ·
    refine ⟨4751943601620210342500783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3167962401080140228333855 4751943601620210342500783)
    ·
      refine ⟨7127915402430315513751175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4751943601620210342500783 7127915402430315513751175)
      ·
        refine ⟨10691873103645473270626763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7127915402430315513751175 10691873103645473270626763)
        ·
          refine ⟨16037809655468209905940145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10691873103645473270626763 16037809655468209905940145)
          ·
            refine ⟨12028357241601157429455109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16037809655468209905940145 12028357241601157429455109)
            ·
              refine ⟨2255316982800217018022833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12028357241601157429455109 2255316982800217018022833)
              ·
                refine ⟨1691487737100162763517125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2255316982800217018022833 1691487737100162763517125)
                ·
                  refine ⟨317153950706280518159461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1691487737100162763517125 317153950706280518159461)
                  ·
                    rfl

theorem cell20_694862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 2, 4].length) (baseStart_694862 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_694862 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_694862 prefixEnd_694862 := by exact prefixLift 694862
  have htrace : WordTrace (prefixWord ++ tailWord_694862) baseStart_694862 baseEnd_694862 := by
    simpa [prefixWord, tailWord_694862, baseEnd_694862] using wordTrace_append hprefix tailTrace_694862
  have hstable : (prefixWord ++ tailWord_694862).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694862).length < 2 ^ (prefixWord ++ tailWord_694862).sum := by decide
  have hdescent : baseEnd_694862 < baseStart_694862 := by decide
  rcases family_descends (prefixWord ++ tailWord_694862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694882 : List Nat := [3, 3, 2, 3, 2, 1, 6]
def baseStart_694882 : Nat := 118140960795 + 694882 * 2 ^ 59
def prefixEnd_694882 : Nat := 4983230072969 + 3 ^ 40 * 694882 * 2
def baseEnd_694882 : Nat := 35240342139027704165857

theorem tailTrace_694882 : CollatzResearch.WordTrace tailWord_694882 prefixEnd_694882 35240342139027704165857 := by
  unfold tailWord_694882
  simp only [CollatzResearch.WordTrace]
  refine ⟨6336107167142166310599725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16896285779045776828265933 6336107167142166310599725)
  ·
    refine ⟨2376040187678312366474897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6336107167142166310599725 2376040187678312366474897)
    ·
      refine ⟨1782030140758734274856173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2376040187678312366474897 1782030140758734274856173)
      ·
        refine ⟨668261302784525353071065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1782030140758734274856173 668261302784525353071065)
        ·
          refine ⟨501195977088394014803299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 668261302784525353071065 501195977088394014803299)
          ·
            refine ⟨751793965632591022204949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 501195977088394014803299 751793965632591022204949)
            ·
              refine ⟨35240342139027704165857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 751793965632591022204949 35240342139027704165857)
              ·
                rfl

theorem cell20_694882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 6].length) (baseStart_694882 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_694882 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_694882 prefixEnd_694882 := by exact prefixLift 694882
  have htrace : WordTrace (prefixWord ++ tailWord_694882) baseStart_694882 baseEnd_694882 := by
    simpa [prefixWord, tailWord_694882, baseEnd_694882] using wordTrace_append hprefix tailTrace_694882
  have hstable : (prefixWord ++ tailWord_694882).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694882).length < 2 ^ (prefixWord ++ tailWord_694882).sum := by decide
  have hdescent : baseEnd_694882 < baseStart_694882 := by decide
  rcases family_descends (prefixWord ++ tailWord_694882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694893 : List Nat := [1, 5, 1, 1, 3, 1, 2, 1, 5]
def baseStart_694893 : Nat := 118140960795 + 694893 * 2 ^ 59
def prefixEnd_694893 : Nat := 4983230072969 + 3 ^ 40 * 694893 * 2
def baseEnd_694893 : Nat := 317168099950982188126001

theorem tailTrace_694893 : CollatzResearch.WordTrace tailWord_694893 prefixEnd_694893 317168099950982188126001 := by
  unfold tailWord_694893
  simp only [CollatzResearch.WordTrace]
  refine ⟨25344829871528814121049333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16896553247685876080699555 25344829871528814121049333)
  ·
    refine ⟨2376077800455826323848375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25344829871528814121049333 2376077800455826323848375)
    ·
      refine ⟨3564116700683739485772563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2376077800455826323848375 3564116700683739485772563)
      ·
        refine ⟨5346175051025609228658845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3564116700683739485772563 5346175051025609228658845)
        ·
          refine ⟨2004815644134603460747067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5346175051025609228658845 2004815644134603460747067)
          ·
            refine ⟨3007223466201905191120601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2004815644134603460747067 3007223466201905191120601)
            ·
              refine ⟨2255417599651428893340451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3007223466201905191120601 2255417599651428893340451)
              ·
                refine ⟨3383126399477143340010677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2255417599651428893340451 3383126399477143340010677)
                ·
                  refine ⟨317168099950982188126001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3383126399477143340010677 317168099950982188126001)
                  ·
                    rfl

theorem cell20_694893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_694893 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_694893 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_694893 prefixEnd_694893 := by exact prefixLift 694893
  have htrace : WordTrace (prefixWord ++ tailWord_694893) baseStart_694893 baseEnd_694893 := by
    simpa [prefixWord, tailWord_694893, baseEnd_694893] using wordTrace_append hprefix tailTrace_694893
  have hstable : (prefixWord ++ tailWord_694893).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694893).length < 2 ^ (prefixWord ++ tailWord_694893).sum := by decide
  have hdescent : baseEnd_694893 < baseStart_694893 := by decide
  rcases family_descends (prefixWord ++ tailWord_694893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694896 : List Nat := [2, 1, 1, 1, 8, 1, 1, 1, 4]
def baseStart_694896 : Nat := 118140960795 + 694896 * 2 ^ 59
def prefixEnd_694896 : Nat := 4983230072969 + 3 ^ 40 * 694896 * 2
def baseEnd_694896 : Nat := 317169469232727511025989

theorem tailTrace_694896 : CollatzResearch.WordTrace tailWord_694896 prefixEnd_694896 317169469232727511025989 := by
  unfold tailWord_694896
  simp only [CollatzResearch.WordTrace]
  refine ⟨12672469645258972816704271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16896626193678630422272361 12672469645258972816704271)
  ·
    refine ⟨19008704467888459225056407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12672469645258972816704271 19008704467888459225056407)
    ·
      refine ⟨28513056701832688837584611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19008704467888459225056407 28513056701832688837584611)
      ·
        refine ⟨42769585052749033256376917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28513056701832688837584611 42769585052749033256376917)
        ·
          refine ⟨501206074836902733473167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 42769585052749033256376917 501206074836902733473167)
          ·
            refine ⟨751809112255354100209751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 501206074836902733473167 751809112255354100209751)
            ·
              refine ⟨1127713668383031150314627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 751809112255354100209751 1127713668383031150314627)
              ·
                refine ⟨1691570502574546725471941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1127713668383031150314627 1691570502574546725471941)
                ·
                  refine ⟨317169469232727511025989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1691570502574546725471941 317169469232727511025989)
                  ·
                    rfl

theorem cell20_694896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 1, 1, 4].length) (baseStart_694896 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_694896 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_694896 prefixEnd_694896 := by exact prefixLift 694896
  have htrace : WordTrace (prefixWord ++ tailWord_694896) baseStart_694896 baseEnd_694896 := by
    simpa [prefixWord, tailWord_694896, baseEnd_694896] using wordTrace_append hprefix tailTrace_694896
  have hstable : (prefixWord ++ tailWord_694896).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694896).length < 2 ^ (prefixWord ++ tailWord_694896).sum := by decide
  have hdescent : baseEnd_694896 < baseStart_694896 := by decide
  rcases family_descends (prefixWord ++ tailWord_694896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694921 : List Nat := [1, 2, 1, 1, 4, 1, 1, 3, 6]
def baseStart_694921 : Nat := 118140960795 + 694921 * 2 ^ 59
def prefixEnd_694921 : Nat := 4983230072969 + 3 ^ 40 * 694921 * 2
def baseEnd_694921 : Nat := 317180879913938535192553

theorem tailTrace_694921 : CollatzResearch.WordTrace tailWord_694921 prefixEnd_694921 317180879913938535192553 := by
  unfold tailWord_694921
  simp only [CollatzResearch.WordTrace]
  refine ⟨25345851115427374903068617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16897234076951583268712411 25345851115427374903068617)
  ·
    refine ⟨19009388336570531177301463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25345851115427374903068617 19009388336570531177301463)
    ·
      refine ⟨28514082504855796765952195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19009388336570531177301463 28514082504855796765952195)
      ·
        refine ⟨42771123757283695148928293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28514082504855796765952195 42771123757283695148928293)
        ·
          refine ⟨8019585704490692840424055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42771123757283695148928293 8019585704490692840424055)
          ·
            refine ⟨12029378556736039260636083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8019585704490692840424055 12029378556736039260636083)
            ·
              refine ⟨18044067835104058890954125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12029378556736039260636083 18044067835104058890954125)
              ·
                refine ⟨6766525438164022084107797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18044067835104058890954125 6766525438164022084107797)
                ·
                  refine ⟨317180879913938535192553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6766525438164022084107797 317180879913938535192553)
                  ·
                    rfl

theorem cell20_694921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 3, 6].length) (baseStart_694921 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_694921 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_694921 prefixEnd_694921 := by exact prefixLift 694921
  have htrace : WordTrace (prefixWord ++ tailWord_694921) baseStart_694921 baseEnd_694921 := by
    simpa [prefixWord, tailWord_694921, baseEnd_694921] using wordTrace_append hprefix tailTrace_694921
  have hstable : (prefixWord ++ tailWord_694921).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694921).length < 2 ^ (prefixWord ++ tailWord_694921).sum := by decide
  have hdescent : baseEnd_694921 < baseStart_694921 := by decide
  rcases family_descends (prefixWord ++ tailWord_694921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694945 : List Nat := [1, 2, 3, 3, 3, 8]
def baseStart_694945 : Nat := 118140960795 + 694945 * 2 ^ 59
def prefixEnd_694945 : Nat := 4983230072969 + 3 ^ 40 * 694945 * 2
def baseEnd_694945 : Nat := 11747845709922263644165

theorem tailTrace_694945 : CollatzResearch.WordTrace tailWord_694945 prefixEnd_694945 11747845709922263644165 := by
  unfold tailWord_694945
  simp only [CollatzResearch.WordTrace]
  refine ⟨25346726467340427001942289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16897817644893618001294859 25346726467340427001942289)
  ·
    refine ⟨19010044850505320251456717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25346726467340427001942289 19010044850505320251456717)
    ·
      refine ⟨7128766818939495094296269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19010044850505320251456717 7128766818939495094296269)
      ·
        refine ⟨2673287557102310660361101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7128766818939495094296269 2673287557102310660361101)
        ·
          refine ⟨1002482833913366497635413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2673287557102310660361101 1002482833913366497635413)
          ·
            refine ⟨11747845709922263644165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1002482833913366497635413 11747845709922263644165)
            ·
              rfl

theorem cell20_694945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 8].length) (baseStart_694945 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_694945 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_694945 prefixEnd_694945 := by exact prefixLift 694945
  have htrace : WordTrace (prefixWord ++ tailWord_694945) baseStart_694945 baseEnd_694945 := by
    simpa [prefixWord, tailWord_694945, baseEnd_694945] using wordTrace_append hprefix tailTrace_694945
  have hstable : (prefixWord ++ tailWord_694945).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694945).length < 2 ^ (prefixWord ++ tailWord_694945).sum := by decide
  have hdescent : baseEnd_694945 < baseStart_694945 := by decide
  rcases family_descends (prefixWord ++ tailWord_694945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694951 : List Nat := [1, 1, 6, 3, 1, 1, 1, 4, 2]
def baseStart_694951 : Nat := 118140960795 + 694951 * 2 ^ 59
def prefixEnd_694951 : Nat := 4983230072969 + 3 ^ 40 * 694951 * 2
def baseEnd_694951 : Nat := 317194572731391764192431

theorem tailTrace_694951 : CollatzResearch.WordTrace tailWord_694951 prefixEnd_694951 317194572731391764192431 := by
  unfold tailWord_694951
  simp only [CollatzResearch.WordTrace]
  refine ⟨25346945305318690026660707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16897963536879126684440471 25346945305318690026660707)
  ·
    refine ⟨38020417957978035039991061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25346945305318690026660707 38020417957978035039991061)
    ·
      refine ⟨1782207091780220392499581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 38020417957978035039991061 1782207091780220392499581)
      ·
        refine ⟨668327659417582647187343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1782207091780220392499581 668327659417582647187343)
        ·
          refine ⟨1002491489126373970781015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 668327659417582647187343 1002491489126373970781015)
          ·
            refine ⟨1503737233689560956171523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1002491489126373970781015 1503737233689560956171523)
            ·
              refine ⟨2255605850534341434257285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1503737233689560956171523 2255605850534341434257285)
              ·
                refine ⟨422926096975189018923241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2255605850534341434257285 422926096975189018923241)
                ·
                  refine ⟨317194572731391764192431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 422926096975189018923241 317194572731391764192431)
                  ·
                    rfl

theorem cell20_694951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 4, 2].length) (baseStart_694951 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_694951 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_694951 prefixEnd_694951 := by exact prefixLift 694951
  have htrace : WordTrace (prefixWord ++ tailWord_694951) baseStart_694951 baseEnd_694951 := by
    simpa [prefixWord, tailWord_694951, baseEnd_694951] using wordTrace_append hprefix tailTrace_694951
  have hstable : (prefixWord ++ tailWord_694951).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694951).length < 2 ^ (prefixWord ++ tailWord_694951).sum := by decide
  have hdescent : baseEnd_694951 < baseStart_694951 := by decide
  rcases family_descends (prefixWord ++ tailWord_694951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694976 : List Nat := [2, 1, 1, 2, 4, 3, 1, 2, 4]
def baseStart_694976 : Nat := 118140960795 + 694976 * 2 ^ 59
def prefixEnd_694976 : Nat := 4983230072969 + 3 ^ 40 * 694976 * 2
def baseEnd_694976 : Nat := 317205983412602788358995

theorem tailTrace_694976 : CollatzResearch.WordTrace tailWord_694976 prefixEnd_694976 317205983412602788358995 := by
  unfold tailWord_694976
  simp only [CollatzResearch.WordTrace]
  refine ⟨12673928565114059648160391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16898571420152079530880521 12673928565114059648160391)
  ·
    refine ⟨19010892847671089472240587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12673928565114059648160391 19010892847671089472240587)
    ·
      refine ⟨28516339271506634208360881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19010892847671089472240587 28516339271506634208360881)
      ·
        refine ⟨21387254453629975656270661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28516339271506634208360881 21387254453629975656270661)
        ·
          refine ⟨4010110210055620435550749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21387254453629975656270661 4010110210055620435550749)
          ·
            refine ⟨1503791328770857663331531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4010110210055620435550749 1503791328770857663331531)
            ·
              refine ⟨2255686993156286494997297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1503791328770857663331531 2255686993156286494997297)
              ·
                refine ⟨1691765244867214871247973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2255686993156286494997297 1691765244867214871247973)
                ·
                  refine ⟨317205983412602788358995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1691765244867214871247973 317205983412602788358995)
                  ·
                    rfl

theorem cell20_694976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 2, 4].length) (baseStart_694976 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_694976 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_694976 prefixEnd_694976 := by exact prefixLift 694976
  have htrace : WordTrace (prefixWord ++ tailWord_694976) baseStart_694976 baseEnd_694976 := by
    simpa [prefixWord, tailWord_694976, baseEnd_694976] using wordTrace_append hprefix tailTrace_694976
  have hstable : (prefixWord ++ tailWord_694976).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694976).length < 2 ^ (prefixWord ++ tailWord_694976).sum := by decide
  have hdescent : baseEnd_694976 < baseStart_694976 := by decide
  rcases family_descends (prefixWord ++ tailWord_694976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_694993 : List Nat := [1, 2, 2, 1, 2, 3, 4, 3, 2]
def baseStart_694993 : Nat := 118140960795 + 694993 * 2 ^ 59
def prefixEnd_694993 : Nat := 4983230072969 + 3 ^ 40 * 694993 * 2
def baseEnd_694993 : Nat := 317213742675826284792259

theorem tailTrace_694993 : CollatzResearch.WordTrace tailWord_694993 prefixEnd_694993 317213742675826284792259 := by
  unfold tailWord_694993
  simp only [CollatzResearch.WordTrace]
  refine ⟨25348477171166531199689633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16898984780777687466459755 25348477171166531199689633)
  ·
    refine ⟨19011357878374898399767225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25348477171166531199689633 19011357878374898399767225)
    ·
      refine ⟨14258518408781173799825419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19011357878374898399767225 14258518408781173799825419)
      ·
        refine ⟨21387777613171760699738129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14258518408781173799825419 21387777613171760699738129)
        ·
          refine ⟨16040833209878820524803597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21387777613171760699738129 16040833209878820524803597)
          ·
            refine ⟨6015312453704557696801349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16040833209878820524803597 6015312453704557696801349)
            ·
              refine ⟨1127871085069604568150253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6015312453704557696801349 1127871085069604568150253)
              ·
                refine ⟨422951656901101713056345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1127871085069604568150253 422951656901101713056345)
                ·
                  refine ⟨317213742675826284792259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 422951656901101713056345 317213742675826284792259)
                  ·
                    rfl

theorem cell20_694993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 4, 3, 2].length) (baseStart_694993 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_694993 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_694993 prefixEnd_694993 := by exact prefixLift 694993
  have htrace : WordTrace (prefixWord ++ tailWord_694993) baseStart_694993 baseEnd_694993 := by
    simpa [prefixWord, tailWord_694993, baseEnd_694993] using wordTrace_append hprefix tailTrace_694993
  have hstable : (prefixWord ++ tailWord_694993).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_694993).length < 2 ^ (prefixWord ++ tailWord_694993).sum := by decide
  have hdescent : baseEnd_694993 < baseStart_694993 := by decide
  rcases family_descends (prefixWord ++ tailWord_694993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695007 : List Nat := [1, 1, 2, 3, 2, 3, 3, 2, 3]
def baseStart_695007 : Nat := 118140960795 + 695007 * 2 ^ 59
def prefixEnd_695007 : Nat := 4983230072969 + 3 ^ 40 * 695007 * 2
def baseEnd_695007 : Nat := 317220132657304458325535

theorem tailTrace_695007 : CollatzResearch.WordTrace tailWord_695007 prefixEnd_695007 317220132657304458325535 := by
  unfold tailWord_695007
  simp only [CollatzResearch.WordTrace]
  refine ⟨25348987793115811590699275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16899325195410541060466183 25348987793115811590699275)
  ·
    refine ⟨38023481689673717386048913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25348987793115811590699275 38023481689673717386048913)
    ·
      refine ⟨28517611267255288039536685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38023481689673717386048913 28517611267255288039536685)
      ·
        refine ⟨10694104225220733014826257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28517611267255288039536685 10694104225220733014826257)
        ·
          refine ⟨8020578168915549761119693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10694104225220733014826257 8020578168915549761119693)
          ·
            refine ⟨3007716813343331160419885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8020578168915549761119693 3007716813343331160419885)
            ·
              refine ⟨1127893805003749185157457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3007716813343331160419885 1127893805003749185157457)
              ·
                refine ⟨845920353752811888868093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1127893805003749185157457 845920353752811888868093)
                ·
                  refine ⟨317220132657304458325535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 845920353752811888868093 317220132657304458325535)
                  ·
                    rfl

theorem cell20_695007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 3, 2, 3].length) (baseStart_695007 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_695007 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_695007 prefixEnd_695007 := by exact prefixLift 695007
  have htrace : WordTrace (prefixWord ++ tailWord_695007) baseStart_695007 baseEnd_695007 := by
    simpa [prefixWord, tailWord_695007, baseEnd_695007] using wordTrace_append hprefix tailTrace_695007
  have hstable : (prefixWord ++ tailWord_695007).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695007).length < 2 ^ (prefixWord ++ tailWord_695007).sum := by decide
  have hdescent : baseEnd_695007 < baseStart_695007 := by decide
  rcases family_descends (prefixWord ++ tailWord_695007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695021 : List Nat := [1, 5, 1, 2, 1, 1, 2, 7]
def baseStart_695021 : Nat := 118140960795 + 695021 * 2 ^ 59
def prefixEnd_695021 : Nat := 4983230072969 + 3 ^ 40 * 695021 * 2
def baseEnd_695021 : Nat := 105742174212927543952937

theorem tailTrace_695021 : CollatzResearch.WordTrace tailWord_695021 prefixEnd_695021 105742174212927543952937 := by
  unfold tailWord_695021
  simp only [CollatzResearch.WordTrace]
  refine ⟨25349498415065091981708917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16899665610043394654472611 25349498415065091981708917)
  ·
    refine ⟨2376515476412352373285211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25349498415065091981708917 2376515476412352373285211)
    ·
      refine ⟨3564773214618528559927817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2376515476412352373285211 3564773214618528559927817)
      ·
        refine ⟨2673579910963896419945863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3564773214618528559927817 2673579910963896419945863)
        ·
          refine ⟨4010369866445844629918795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2673579910963896419945863 4010369866445844629918795)
          ·
            refine ⟨6015554799668766944878193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4010369866445844629918795 6015554799668766944878193)
            ·
              refine ⟨4511666099751575208658645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6015554799668766944878193 4511666099751575208658645)
              ·
                refine ⟨105742174212927543952937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4511666099751575208658645 105742174212927543952937)
                ·
                  rfl

theorem cell20_695021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 7].length) (baseStart_695021 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_695021 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_695021 prefixEnd_695021 := by exact prefixLift 695021
  have htrace : WordTrace (prefixWord ++ tailWord_695021) baseStart_695021 baseEnd_695021 := by
    simpa [prefixWord, tailWord_695021, baseEnd_695021] using wordTrace_append hprefix tailTrace_695021
  have hstable : (prefixWord ++ tailWord_695021).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695021).length < 2 ^ (prefixWord ++ tailWord_695021).sum := by decide
  have hdescent : baseEnd_695021 < baseStart_695021 := by decide
  rcases family_descends (prefixWord ++ tailWord_695021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695038 : List Nat := [4, 2, 2, 1, 2, 2, 1, 6]
def baseStart_695038 : Nat := 118140960795 + 695038 * 2 ^ 59
def prefixEnd_695038 : Nat := 4983230072969 + 3 ^ 40 * 695038 * 2
def baseEnd_695038 : Nat := 105744760634002042764025

theorem tailTrace_695038 : CollatzResearch.WordTrace tailWord_695038 prefixEnd_695038 105744760634002042764025 := by
  unfold tailWord_695038
  simp only [CollatzResearch.WordTrace]
  refine ⟨3168764807000437985634721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16900078970669002590051845 3168764807000437985634721)
  ·
    refine ⟨2376573605250328489226041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3168764807000437985634721 2376573605250328489226041)
    ·
      refine ⟨1782430203937746366919531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2376573605250328489226041 1782430203937746366919531)
      ·
        refine ⟨2673645305906619550379297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1782430203937746366919531 2673645305906619550379297)
        ·
          refine ⟨2005233979429964662784473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2673645305906619550379297 2005233979429964662784473)
          ·
            refine ⟨1503925484572473497088355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2005233979429964662784473 1503925484572473497088355)
            ·
              refine ⟨2255888226858710245632533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1503925484572473497088355 2255888226858710245632533)
              ·
                refine ⟨105744760634002042764025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2255888226858710245632533 105744760634002042764025)
                ·
                  rfl

theorem cell20_695038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 6].length) (baseStart_695038 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_695038 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_695038 prefixEnd_695038 := by exact prefixLift 695038
  have htrace : WordTrace (prefixWord ++ tailWord_695038) baseStart_695038 baseEnd_695038 := by
    simpa [prefixWord, tailWord_695038, baseEnd_695038] using wordTrace_append hprefix tailTrace_695038
  have hstable : (prefixWord ++ tailWord_695038).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695038).length < 2 ^ (prefixWord ++ tailWord_695038).sum := by decide
  have hdescent : baseEnd_695038 < baseStart_695038 := by decide
  rcases family_descends (prefixWord ++ tailWord_695038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695048 : List Nat := [2, 1, 3, 2, 2, 4, 1, 3, 2]
def baseStart_695048 : Nat := 118140960795 + 695048 * 2 ^ 59
def prefixEnd_695048 : Nat := 4983230072969 + 3 ^ 40 * 695048 * 2
def baseEnd_695048 : Nat := 317238846174490537958701

theorem tailTrace_695048 : CollatzResearch.WordTrace tailWord_695048 prefixEnd_695048 317238846174490537958701 := by
  unfold tailWord_695048
  simp only [CollatzResearch.WordTrace]
  refine ⟨12675241592983637796470899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16900322123978183728627865 12675241592983637796470899)
  ·
    refine ⟨19012862389475456694706349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12675241592983637796470899 19012862389475456694706349)
    ·
      refine ⟨7129823396053296260514881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19012862389475456694706349 7129823396053296260514881)
      ·
        refine ⟨5347367547039972195386161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7129823396053296260514881 5347367547039972195386161)
        ·
          refine ⟨4010525660279979146539621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5347367547039972195386161 4010525660279979146539621)
          ·
            refine ⟨751973561302496089976179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4010525660279979146539621 751973561302496089976179)
            ·
              refine ⟨1127960341953744134964269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 751973561302496089976179 1127960341953744134964269)
              ·
                refine ⟨422985128232654050611601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1127960341953744134964269 422985128232654050611601)
                ·
                  refine ⟨317238846174490537958701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 422985128232654050611601 317238846174490537958701)
                  ·
                    rfl

theorem cell20_695048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 1, 3, 2].length) (baseStart_695048 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_695048 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_695048 prefixEnd_695048 := by exact prefixLift 695048
  have htrace : WordTrace (prefixWord ++ tailWord_695048) baseStart_695048 baseEnd_695048 := by
    simpa [prefixWord, tailWord_695048, baseEnd_695048] using wordTrace_append hprefix tailTrace_695048
  have hstable : (prefixWord ++ tailWord_695048).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695048).length < 2 ^ (prefixWord ++ tailWord_695048).sum := by decide
  have hdescent : baseEnd_695048 < baseStart_695048 := by decide
  rcases family_descends (prefixWord ++ tailWord_695048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695066 : List Nat := [3, 1, 1, 3, 2, 1, 1, 3, 5]
def baseStart_695066 : Nat := 118140960795 + 695066 * 2 ^ 59
def prefixEnd_695066 : Nat := 4983230072969 + 3 ^ 40 * 695066 * 2
def baseEnd_695066 : Nat := 317247061864962475358627

theorem tailTrace_695066 : CollatzResearch.WordTrace tailWord_695066 prefixEnd_695066 317247061864962475358627 := by
  unfold tailWord_695066
  simp only [CollatzResearch.WordTrace]
  refine ⟨6337784924975516166774263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16900759799934709778064701 6337784924975516166774263)
  ·
    refine ⟨9506677387463274250161395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6337784924975516166774263 9506677387463274250161395)
    ·
      refine ⟨14260016081194911375242093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9506677387463274250161395 14260016081194911375242093)
      ·
        refine ⟨5347506030448091765715785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14260016081194911375242093 5347506030448091765715785)
        ·
          refine ⟨4010629522836068824286839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5347506030448091765715785 4010629522836068824286839)
          ·
            refine ⟨6015944284254103236430259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4010629522836068824286839 6015944284254103236430259)
            ·
              refine ⟨9023916426381154854645389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6015944284254103236430259 9023916426381154854645389)
              ·
                refine ⟨3383968659892933070492021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9023916426381154854645389 3383968659892933070492021)
                ·
                  refine ⟨317247061864962475358627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3383968659892933070492021 317247061864962475358627)
                  ·
                    rfl

theorem cell20_695066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 3, 5].length) (baseStart_695066 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_695066 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_695066 prefixEnd_695066 := by exact prefixLift 695066
  have htrace : WordTrace (prefixWord ++ tailWord_695066) baseStart_695066 baseEnd_695066 := by
    simpa [prefixWord, tailWord_695066, baseEnd_695066] using wordTrace_append hprefix tailTrace_695066
  have hstable : (prefixWord ++ tailWord_695066).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695066).length < 2 ^ (prefixWord ++ tailWord_695066).sum := by decide
  have hdescent : baseEnd_695066 < baseStart_695066 := by decide
  rcases family_descends (prefixWord ++ tailWord_695066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695076 : List Nat := [2, 3, 1, 3, 3, 1, 2, 5]
def baseStart_695076 : Nat := 118140960795 + 695076 * 2 ^ 59
def prefixEnd_695076 : Nat := 4983230072969 + 3 ^ 40 * 695076 * 2
def baseEnd_695076 : Nat := 105750542045815628341751

theorem tailTrace_695076 : CollatzResearch.WordTrace tailWord_695076 prefixEnd_695076 105750542045815628341751 := by
  unfold tailWord_695076
  simp only [CollatzResearch.WordTrace]
  refine ⟨12675752214932918187480541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16901002953243890916640721 12675752214932918187480541)
  ·
    refine ⟨4753407080599844320305203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12675752214932918187480541 4753407080599844320305203)
    ·
      refine ⟨7130110620899766480457805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4753407080599844320305203 7130110620899766480457805)
      ·
        refine ⟨2673791482837412430171677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7130110620899766480457805 2673791482837412430171677)
        ·
          refine ⟨1002671806064029661314379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2673791482837412430171677 1002671806064029661314379)
          ·
            refine ⟨1504007709096044491971569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1002671806064029661314379 1504007709096044491971569)
            ·
              refine ⟨1128005781822033368978677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1504007709096044491971569 1128005781822033368978677)
              ·
                refine ⟨105750542045815628341751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1128005781822033368978677 105750542045815628341751)
                ·
                  rfl

theorem cell20_695076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 2, 5].length) (baseStart_695076 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_695076 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_695076 prefixEnd_695076 := by exact prefixLift 695076
  have htrace : WordTrace (prefixWord ++ tailWord_695076) baseStart_695076 baseEnd_695076 := by
    simpa [prefixWord, tailWord_695076, baseEnd_695076] using wordTrace_append hprefix tailTrace_695076
  have hstable : (prefixWord ++ tailWord_695076).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695076).length < 2 ^ (prefixWord ++ tailWord_695076).sum := by decide
  have hdescent : baseEnd_695076 < baseStart_695076 := by decide
  rcases family_descends (prefixWord ++ tailWord_695076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695117 : List Nat := [1, 6, 1, 2, 2, 1, 2, 2, 3]
def baseStart_695117 : Nat := 118140960795 + 695117 * 2 ^ 59
def prefixEnd_695117 : Nat := 4983230072969 + 3 ^ 40 * 695117 * 2
def baseEnd_695117 : Nat := 317270339654632964658419

theorem tailTrace_695117 : CollatzResearch.WordTrace tailWord_695117 prefixEnd_695117 317270339654632964658419 := by
  unfold tailWord_695117
  simp only [CollatzResearch.WordTrace]
  refine ⟨25352999822717300377203605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16901999881811533584802403 25352999822717300377203605)
  ·
    refine ⟨1188421866689873455181419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 25352999822717300377203605 1188421866689873455181419)
    ·
      refine ⟨1782632800034810182772129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1188421866689873455181419 1782632800034810182772129)
      ·
        refine ⟨1336974600026107637079097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1782632800034810182772129 1336974600026107637079097)
        ·
          refine ⟨1002730950019580727809323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1336974600026107637079097 1002730950019580727809323)
          ·
            refine ⟨1504096425029371091713985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1002730950019580727809323 1504096425029371091713985)
            ·
              refine ⟨1128072318772028318785489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1504096425029371091713985 1128072318772028318785489)
              ·
                refine ⟨846054239079021239089117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1128072318772028318785489 846054239079021239089117)
                ·
                  refine ⟨317270339654632964658419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 846054239079021239089117 317270339654632964658419)
                  ·
                    rfl

theorem cell20_695117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_695117 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_695117 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_695117 prefixEnd_695117 := by exact prefixLift 695117
  have htrace : WordTrace (prefixWord ++ tailWord_695117) baseStart_695117 baseEnd_695117 := by
    simpa [prefixWord, tailWord_695117, baseEnd_695117] using wordTrace_append hprefix tailTrace_695117
  have hstable : (prefixWord ++ tailWord_695117).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695117).length < 2 ^ (prefixWord ++ tailWord_695117).sum := by decide
  have hdescent : baseEnd_695117 < baseStart_695117 := by decide
  rcases family_descends (prefixWord ++ tailWord_695117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695124 : List Nat := [2, 4, 1, 1, 4, 1, 1, 4, 2]
def baseStart_695124 : Nat := 118140960795 + 695124 * 2 ^ 59
def prefixEnd_695124 : Nat := 4983230072969 + 3 ^ 40 * 695124 * 2
def baseEnd_695124 : Nat := 317273534645372051425057

theorem tailTrace_695124 : CollatzResearch.WordTrace tailWord_695124 prefixEnd_695124 317273534645372051425057 := by
  unfold tailWord_695124
  simp only [CollatzResearch.WordTrace]
  refine ⟨12676627566845970286354213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16902170089127960381805617 12676627566845970286354213)
  ·
    refine ⟨2376867668783619428691415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12676627566845970286354213 2376867668783619428691415)
    ·
      refine ⟨3565301503175429143037123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2376867668783619428691415 3565301503175429143037123)
      ·
        refine ⟨5347952254763143714555685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3565301503175429143037123 5347952254763143714555685)
        ·
          refine ⟨1002741047768089446479191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5347952254763143714555685 1002741047768089446479191)
          ·
            refine ⟨1504111571652134169718787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1002741047768089446479191 1504111571652134169718787)
            ·
              refine ⟨2256167357478201254578181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1504111571652134169718787 2256167357478201254578181)
              ·
                refine ⟨423031379527162735233409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2256167357478201254578181 423031379527162735233409)
                ·
                  refine ⟨317273534645372051425057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 423031379527162735233409 317273534645372051425057)
                  ·
                    rfl

theorem cell20_695124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 4, 2].length) (baseStart_695124 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_695124 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_695124 prefixEnd_695124 := by exact prefixLift 695124
  have htrace : WordTrace (prefixWord ++ tailWord_695124) baseStart_695124 baseEnd_695124 := by
    simpa [prefixWord, tailWord_695124, baseEnd_695124] using wordTrace_append hprefix tailTrace_695124
  have hstable : (prefixWord ++ tailWord_695124).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695124).length < 2 ^ (prefixWord ++ tailWord_695124).sum := by decide
  have hdescent : baseEnd_695124 < baseStart_695124 := by decide
  rcases family_descends (prefixWord ++ tailWord_695124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695176 : List Nat := [2, 1, 3, 3, 2, 3, 1, 2, 3]
def baseStart_695176 : Nat := 118140960795 + 695176 * 2 ^ 59
def prefixEnd_695176 : Nat := 4983230072969 + 3 ^ 40 * 695176 * 2
def baseEnd_695176 : Nat := 317297268862290981691511

theorem tailTrace_695176 : CollatzResearch.WordTrace tailWord_695176 prefixEnd_695176 317297268862290981691511 := by
  unfold tailWord_695176
  simp only [CollatzResearch.WordTrace]
  refine ⟨12677575864751776726800691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16903434486335702302400921 12677575864751776726800691)
  ·
    refine ⟨19016363797127665090201037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12677575864751776726800691 19016363797127665090201037)
    ·
      refine ⟨7131136423922874408825389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19016363797127665090201037 7131136423922874408825389)
      ·
        refine ⟨2674176158971077903309521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7131136423922874408825389 2674176158971077903309521)
        ·
          refine ⟨2005632119228308427482141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2674176158971077903309521 2005632119228308427482141)
          ·
            refine ⟨752112044710615660305803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2005632119228308427482141 752112044710615660305803)
            ·
              refine ⟨1128168067065923490458705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 752112044710615660305803 1128168067065923490458705)
              ·
                refine ⟨846126050299442617844029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1128168067065923490458705 846126050299442617844029)
                ·
                  refine ⟨317297268862290981691511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 846126050299442617844029 317297268862290981691511)
                  ·
                    rfl

theorem cell20_695176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 1, 2, 3].length) (baseStart_695176 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_695176 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_695176 prefixEnd_695176 := by exact prefixLift 695176
  have htrace : WordTrace (prefixWord ++ tailWord_695176) baseStart_695176 baseEnd_695176 := by
    simpa [prefixWord, tailWord_695176, baseEnd_695176] using wordTrace_append hprefix tailTrace_695176
  have hstable : (prefixWord ++ tailWord_695176).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695176).length < 2 ^ (prefixWord ++ tailWord_695176).sum := by decide
  have hdescent : baseEnd_695176 < baseStart_695176 := by decide
  rcases family_descends (prefixWord ++ tailWord_695176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695207 : List Nat := [1, 1, 6, 1, 3, 2, 2, 4]
def baseStart_695207 : Nat := 118140960795 + 695207 * 2 ^ 59
def prefixEnd_695207 : Nat := 4983230072969 + 3 ^ 40 * 695207 * 2
def baseEnd_695207 : Nat := 105770472702330883886017

theorem tailTrace_695207 : CollatzResearch.WordTrace tailWord_695207 prefixEnd_695207 105770472702330883886017 := by
  unfold tailWord_695207
  simp only [CollatzResearch.WordTrace]
  refine ⟨25356282392391245747979875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16904188261594163831986583 25356282392391245747979875)
  ·
    refine ⟨38034423588586868621969813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25356282392391245747979875 38034423588586868621969813)
    ·
      refine ⟨1782863605715009466654835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 38034423588586868621969813 1782863605715009466654835)
      ·
        refine ⟨2674295408572514199982253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1782863605715009466654835 2674295408572514199982253)
        ·
          refine ⟨1002860778214692824993345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2674295408572514199982253 1002860778214692824993345)
          ·
            refine ⟨752145583661019618745009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1002860778214692824993345 752145583661019618745009)
            ·
              refine ⟨564109187745764714058757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 752145583661019618745009 564109187745764714058757)
              ·
                refine ⟨105770472702330883886017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 564109187745764714058757 105770472702330883886017)
                ·
                  rfl

theorem cell20_695207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 2, 4].length) (baseStart_695207 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_695207 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_695207 prefixEnd_695207 := by exact prefixLift 695207
  have htrace : WordTrace (prefixWord ++ tailWord_695207) baseStart_695207 baseEnd_695207 := by
    simpa [prefixWord, tailWord_695207, baseEnd_695207] using wordTrace_append hprefix tailTrace_695207
  have hstable : (prefixWord ++ tailWord_695207).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695207).length < 2 ^ (prefixWord ++ tailWord_695207).sum := by decide
  have hdescent : baseEnd_695207 < baseStart_695207 := by decide
  rcases family_descends (prefixWord ++ tailWord_695207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695217 : List Nat := [1, 2, 2, 4, 4, 1, 1, 3, 2]
def baseStart_695217 : Nat := 118140960795 + 695217 * 2 ^ 59
def prefixEnd_695217 : Nat := 4983230072969 + 3 ^ 40 * 695217 * 2
def baseEnd_695217 : Nat := 317315982379477061324677

theorem tailTrace_695217 : CollatzResearch.WordTrace tailWord_695217 prefixEnd_695217 317315982379477061324677 := by
  unfold tailWord_695217
  simp only [CollatzResearch.WordTrace]
  refine ⟨25356647122355017455843905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16904431414903344970562603 25356647122355017455843905)
  ·
    refine ⟨19017485341766263091882929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25356647122355017455843905 19017485341766263091882929)
    ·
      refine ⟨14263114006324697318912197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19017485341766263091882929 14263114006324697318912197)
      ·
        refine ⟨2674333876185880747296037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14263114006324697318912197 2674333876185880747296037)
        ·
          refine ⟨501437601784852640118007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2674333876185880747296037 501437601784852640118007)
          ·
            refine ⟨752156402677278960177011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 501437601784852640118007 752156402677278960177011)
            ·
              refine ⟨1128234604015918440265517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 752156402677278960177011 1128234604015918440265517)
              ·
                refine ⟨423087976505969415099569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1128234604015918440265517 423087976505969415099569)
                ·
                  refine ⟨317315982379477061324677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 423087976505969415099569 317315982379477061324677)
                  ·
                    rfl

theorem cell20_695217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 1, 3, 2].length) (baseStart_695217 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_695217 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_695217 prefixEnd_695217 := by exact prefixLift 695217
  have htrace : WordTrace (prefixWord ++ tailWord_695217) baseStart_695217 baseEnd_695217 := by
    simpa [prefixWord, tailWord_695217, baseEnd_695217] using wordTrace_append hprefix tailTrace_695217
  have hstable : (prefixWord ++ tailWord_695217).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695217).length < 2 ^ (prefixWord ++ tailWord_695217).sum := by decide
  have hdescent : baseEnd_695217 < baseStart_695217 := by decide
  rcases family_descends (prefixWord ++ tailWord_695217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695232 : List Nat := [2, 1, 1, 2, 3, 3, 8]
def baseStart_695232 : Nat := 118140960795 + 695232 * 2 ^ 59
def prefixEnd_695232 : Nat := 4983230072969 + 3 ^ 40 * 695232 * 2
def baseEnd_695232 : Nat := 35258092087578186202735

theorem tailTrace_695232 : CollatzResearch.WordTrace tailWord_695232 prefixEnd_695232 35258092087578186202735 := by
  unfold tailWord_695232
  simp only [CollatzResearch.WordTrace]
  refine ⟨12678597108650337508819975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16904796144867116678426633 12678597108650337508819975)
  ·
    refine ⟨19017895662975506263229963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12678597108650337508819975 19017895662975506263229963)
    ·
      refine ⟨28526843494463259394844945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19017895662975506263229963 28526843494463259394844945)
      ·
        refine ⟨21395132620847444546133709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28526843494463259394844945 21395132620847444546133709)
        ·
          refine ⟨8023174732817791704800141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21395132620847444546133709 8023174732817791704800141)
          ·
            refine ⟨3008690524806671889300053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8023174732817791704800141 3008690524806671889300053)
            ·
              refine ⟨35258092087578186202735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3008690524806671889300053 35258092087578186202735)
              ·
                rfl

theorem cell20_695232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 8].length) (baseStart_695232 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_695232 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_695232 prefixEnd_695232 := by exact prefixLift 695232
  have htrace : WordTrace (prefixWord ++ tailWord_695232) baseStart_695232 baseEnd_695232 := by
    simpa [prefixWord, tailWord_695232, baseEnd_695232] using wordTrace_append hprefix tailTrace_695232
  have hstable : (prefixWord ++ tailWord_695232).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695232).length < 2 ^ (prefixWord ++ tailWord_695232).sum := by decide
  have hdescent : baseEnd_695232 < baseStart_695232 := by decide
  rcases family_descends (prefixWord ++ tailWord_695232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695252 : List Nat := [2, 4, 1, 2, 1, 2, 4, 1, 3]
def baseStart_695252 : Nat := 118140960795 + 695252 * 2 ^ 59
def prefixEnd_695252 : Nat := 4983230072969 + 3 ^ 40 * 695252 * 2
def baseEnd_695252 : Nat := 317331957333172495157867

theorem tailTrace_695252 : CollatzResearch.WordTrace tailWord_695252 prefixEnd_695252 317331957333172495157867 := by
  unfold tailWord_695252
  simp only [CollatzResearch.WordTrace]
  refine ⟨12678961838614109216684005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16905282451485478955578673 12678961838614109216684005)
  ·
    refine ⟨2377305344740145478128251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12678961838614109216684005 2377305344740145478128251)
    ·
      refine ⟨3565958017110218217192377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2377305344740145478128251 3565958017110218217192377)
      ·
        refine ⟨2674468512832663662894283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3565958017110218217192377 2674468512832663662894283)
        ·
          refine ⟨4011702769248995494341425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2674468512832663662894283 4011702769248995494341425)
          ·
            refine ⟨3008777076936746620756069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4011702769248995494341425 3008777076936746620756069)
            ·
              refine ⟨564145701925639991391763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3008777076936746620756069 564145701925639991391763)
              ·
                refine ⟨846218552888459987087645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 564145701925639991391763 846218552888459987087645)
                ·
                  refine ⟨317331957333172495157867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 846218552888459987087645 317331957333172495157867)
                  ·
                    rfl

theorem cell20_695252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 4, 1, 3].length) (baseStart_695252 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_695252 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_695252 prefixEnd_695252 := by exact prefixLift 695252
  have htrace : WordTrace (prefixWord ++ tailWord_695252) baseStart_695252 baseEnd_695252 := by
    simpa [prefixWord, tailWord_695252, baseEnd_695252] using wordTrace_append hprefix tailTrace_695252
  have hstable : (prefixWord ++ tailWord_695252).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695252).length < 2 ^ (prefixWord ++ tailWord_695252).sum := by decide
  have hdescent : baseEnd_695252 < baseStart_695252 := by decide
  rcases family_descends (prefixWord ++ tailWord_695252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695266 : List Nat := [3, 3, 3, 1, 1, 1, 2, 6]
def baseStart_695266 : Nat := 118140960795 + 695266 * 2 ^ 59
def prefixEnd_695266 : Nat := 4983230072969 + 3 ^ 40 * 695266 * 2
def baseEnd_695266 : Nat := 105779449104883556230381

theorem tailTrace_695266 : CollatzResearch.WordTrace tailWord_695266 prefixEnd_695266 105779449104883556230381 := by
  unfold tailWord_695266
  simp only [CollatzResearch.WordTrace]
  refine ⟨6339608574794374706094413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16905622866118332549585101 6339608574794374706094413)
  ·
    refine ⟨2377353215547890514785405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6339608574794374706094413 2377353215547890514785405)
    ·
      refine ⟨891507455830458943044527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2377353215547890514785405 891507455830458943044527)
      ·
        refine ⟨1337261183745688414566791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 891507455830458943044527 1337261183745688414566791)
        ·
          refine ⟨2005891775618532621850187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1337261183745688414566791 2005891775618532621850187)
          ·
            refine ⟨3008837663427798932775281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2005891775618532621850187 3008837663427798932775281)
            ·
              refine ⟨2256628247570849199581461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3008837663427798932775281 2256628247570849199581461)
              ·
                refine ⟨105779449104883556230381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2256628247570849199581461 105779449104883556230381)
                ·
                  rfl

theorem cell20_695266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 6].length) (baseStart_695266 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_695266 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_695266 prefixEnd_695266 := by exact prefixLift 695266
  have htrace : WordTrace (prefixWord ++ tailWord_695266) baseStart_695266 baseEnd_695266 := by
    simpa [prefixWord, tailWord_695266, baseEnd_695266] using wordTrace_append hprefix tailTrace_695266
  have hstable : (prefixWord ++ tailWord_695266).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695266).length < 2 ^ (prefixWord ++ tailWord_695266).sum := by decide
  have hdescent : baseEnd_695266 < baseStart_695266 := by decide
  rcases family_descends (prefixWord ++ tailWord_695266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695280 : List Nat := [2, 1, 1, 1, 3, 2, 1, 7, 2]
def baseStart_695280 : Nat := 118140960795 + 695280 * 2 ^ 59
def prefixEnd_695280 : Nat := 4983230072969 + 3 ^ 40 * 695280 * 2
def baseEnd_695280 : Nat := 317344737296128842224419

theorem tailTrace_695280 : CollatzResearch.WordTrace tailWord_695280 prefixEnd_695280 317344737296128842224419 := by
  unfold tailWord_695280
  simp only [CollatzResearch.WordTrace]
  refine ⟨12679472460563389607693647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16905963280751186143591529 12679472460563389607693647)
  ·
    refine ⟨19019208690845084411540471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12679472460563389607693647 19019208690845084411540471)
    ·
      refine ⟨28528813036267626617310707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19019208690845084411540471 28528813036267626617310707)
      ·
        refine ⟨42793219554401439925966061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28528813036267626617310707 42793219554401439925966061)
        ·
          refine ⟨16047457332900539972237273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42793219554401439925966061 16047457332900539972237273)
          ·
            refine ⟨12035592999675404979177955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16047457332900539972237273 12035592999675404979177955)
            ·
              refine ⟨18053389499513107468766933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12035592999675404979177955 18053389499513107468766933)
              ·
                refine ⟨423126316394838456299225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 18053389499513107468766933 423126316394838456299225)
                ·
                  refine ⟨317344737296128842224419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 423126316394838456299225 317344737296128842224419)
                  ·
                    rfl

theorem cell20_695280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 7, 2].length) (baseStart_695280 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_695280 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_695280 prefixEnd_695280 := by exact prefixLift 695280
  have htrace : WordTrace (prefixWord ++ tailWord_695280) baseStart_695280 baseEnd_695280 := by
    simpa [prefixWord, tailWord_695280, baseEnd_695280] using wordTrace_append hprefix tailTrace_695280
  have hstable : (prefixWord ++ tailWord_695280).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695280).length < 2 ^ (prefixWord ++ tailWord_695280).sum := by decide
  have hdescent : baseEnd_695280 < baseStart_695280 := by decide
  rcases family_descends (prefixWord ++ tailWord_695280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695297 : List Nat := [1, 2, 4, 1, 2, 3, 1, 4, 2]
def baseStart_695297 : Nat := 118140960795 + 695297 * 2 ^ 59
def prefixEnd_695297 : Nat := 4983230072969 + 3 ^ 40 * 695297 * 2
def baseEnd_695297 : Nat := 317352496559352338657683

theorem tailTrace_695297 : CollatzResearch.WordTrace tailWord_695297 prefixEnd_695297 317352496559352338657683 := by
  unfold tailWord_695297
  simp only [CollatzResearch.WordTrace]
  refine ⟨25359564962065191118756145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16906376641376794079170763 25359564962065191118756145)
  ·
    refine ⟨19019673721548893339067109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25359564962065191118756145 19019673721548893339067109)
    ·
      refine ⟨3566188822790417501075083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19019673721548893339067109 3566188822790417501075083)
      ·
        refine ⟨5349283234185626251612625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3566188822790417501075083 5349283234185626251612625)
        ·
          refine ⟨4011962425639219688709469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5349283234185626251612625 4011962425639219688709469)
          ·
            refine ⟨1504485909614707383266051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4011962425639219688709469 1504485909614707383266051)
            ·
              refine ⟨2256728864422061074899077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1504485909614707383266051 2256728864422061074899077)
              ·
                refine ⟨423136662079136451543577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2256728864422061074899077 423136662079136451543577)
                ·
                  refine ⟨317352496559352338657683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 423136662079136451543577 317352496559352338657683)
                  ·
                    rfl

theorem cell20_695297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 4, 2].length) (baseStart_695297 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_695297 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_695297 prefixEnd_695297 := by exact prefixLift 695297
  have htrace : WordTrace (prefixWord ++ tailWord_695297) baseStart_695297 baseEnd_695297 := by
    simpa [prefixWord, tailWord_695297, baseEnd_695297] using wordTrace_append hprefix tailTrace_695297
  have hstable : (prefixWord ++ tailWord_695297).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695297).length < 2 ^ (prefixWord ++ tailWord_695297).sum := by decide
  have hdescent : baseEnd_695297 < baseStart_695297 := by decide
  rcases family_descends (prefixWord ++ tailWord_695297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695301 : List Nat := [1, 3, 1, 1, 2, 3, 2, 3, 4]
def baseStart_695301 : Nat := 118140960795 + 695301 * 2 ^ 59
def prefixEnd_695301 : Nat := 4983230072969 + 3 ^ 40 * 695301 * 2
def baseEnd_695301 : Nat := 317354322268346102524333

theorem tailTrace_695301 : CollatzResearch.WordTrace tailWord_695301 prefixEnd_695301 317354322268346102524333 := by
  unfold tailWord_695301
  simp only [CollatzResearch.WordTrace]
  refine ⟨25359710854050699801901757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16906473902700466534601171 25359710854050699801901757)
  ·
    refine ⟨9509891570269012425713159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25359710854050699801901757 9509891570269012425713159)
    ·
      refine ⟨14264837355403518638569739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9509891570269012425713159 14264837355403518638569739)
      ·
        refine ⟨21397256033105277957854609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14264837355403518638569739 21397256033105277957854609)
        ·
          refine ⟨16047942024828958468390957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21397256033105277957854609 16047942024828958468390957)
          ·
            refine ⟨6017978259310859425646609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16047942024828958468390957 6017978259310859425646609)
            ·
              refine ⟨4513483694483144569234957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6017978259310859425646609 4513483694483144569234957)
              ·
                refine ⟨1692556385431179213463109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4513483694483144569234957 1692556385431179213463109)
                ·
                  refine ⟨317354322268346102524333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1692556385431179213463109 317354322268346102524333)
                  ·
                    rfl

theorem cell20_695301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 3, 4].length) (baseStart_695301 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_695301 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_695301 prefixEnd_695301 := by exact prefixLift 695301
  have htrace : WordTrace (prefixWord ++ tailWord_695301) baseStart_695301 baseEnd_695301 := by
    simpa [prefixWord, tailWord_695301, baseEnd_695301] using wordTrace_append hprefix tailTrace_695301
  have hstable : (prefixWord ++ tailWord_695301).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695301).length < 2 ^ (prefixWord ++ tailWord_695301).sum := by decide
  have hdescent : baseEnd_695301 < baseStart_695301 := by decide
  rcases family_descends (prefixWord ++ tailWord_695301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695315 : List Nat := [1, 1, 1, 2, 1, 4, 1, 2, 7]
def baseStart_695315 : Nat := 118140960795 + 695315 * 2 ^ 59
def prefixEnd_695315 : Nat := 4983230072969 + 3 ^ 40 * 695315 * 2
def baseEnd_695315 : Nat := 317360712249824276057609

theorem tailTrace_695315 : CollatzResearch.WordTrace tailWord_695315 prefixEnd_695315 317360712249824276057609 := by
  unfold tailWord_695315
  simp only [CollatzResearch.WordTrace]
  refine ⟨25360221475999980192911399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16906814317333320128607599 25360221475999980192911399)
  ·
    refine ⟨38040332213999970289367099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25360221475999980192911399 38040332213999970289367099)
    ·
      refine ⟨57060498320999955434050649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38040332213999970289367099 57060498320999955434050649)
      ·
        refine ⟨42795373740749966575537987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57060498320999955434050649 42795373740749966575537987)
        ·
          refine ⟨64193060611124949863306981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42795373740749966575537987 64193060611124949863306981)
          ·
            refine ⟨12036198864585928099370059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64193060611124949863306981 12036198864585928099370059)
            ·
              refine ⟨18054298296878892149055089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12036198864585928099370059 18054298296878892149055089)
              ·
                refine ⟨13540723722659169111791317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18054298296878892149055089 13540723722659169111791317)
                ·
                  refine ⟨317360712249824276057609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13540723722659169111791317 317360712249824276057609)
                  ·
                    rfl

theorem cell20_695315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 2, 7].length) (baseStart_695315 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_695315 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_695315 prefixEnd_695315 := by exact prefixLift 695315
  have htrace : WordTrace (prefixWord ++ tailWord_695315) baseStart_695315 baseEnd_695315 := by
    simpa [prefixWord, tailWord_695315, baseEnd_695315] using wordTrace_append hprefix tailTrace_695315
  have hstable : (prefixWord ++ tailWord_695315).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695315).length < 2 ^ (prefixWord ++ tailWord_695315).sum := by decide
  have hdescent : baseEnd_695315 < baseStart_695315 := by decide
  rcases family_descends (prefixWord ++ tailWord_695315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695346 : List Nat := [3, 2, 1, 1, 2, 2, 9]
def baseStart_695346 : Nat := 118140960795 + 695346 * 2 ^ 59
def prefixEnd_695346 : Nat := 4983230072969 + 3 ^ 40 * 695346 * 2
def baseEnd_695346 : Nat := 35263873499391771780461

theorem tailTrace_695346 : CollatzResearch.WordTrace tailWord_695346 prefixEnd_695346 35263873499391771780461 := by
  unfold tailWord_695346
  simp only [CollatzResearch.WordTrace]
  refine ⟨6340338034721918121822473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16907568092591781658193261 6340338034721918121822473)
  ·
    refine ⟨4755253526041438591366855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6340338034721918121822473 4755253526041438591366855)
    ·
      refine ⟨7132880289062157887050283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4755253526041438591366855 7132880289062157887050283)
      ·
        refine ⟨10699320433593236830575425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7132880289062157887050283 10699320433593236830575425)
        ·
          refine ⟨8024490325194927622931569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10699320433593236830575425 8024490325194927622931569)
          ·
            refine ⟨6018367743896195717198677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8024490325194927622931569 6018367743896195717198677)
            ·
              refine ⟨35263873499391771780461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6018367743896195717198677 35263873499391771780461)
              ·
                rfl

theorem cell20_695346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 9].length) (baseStart_695346 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_695346 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_695346 prefixEnd_695346 := by exact prefixLift 695346
  have htrace : WordTrace (prefixWord ++ tailWord_695346) baseStart_695346 baseEnd_695346 := by
    simpa [prefixWord, tailWord_695346, baseEnd_695346] using wordTrace_append hprefix tailTrace_695346
  have hstable : (prefixWord ++ tailWord_695346).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695346).length < 2 ^ (prefixWord ++ tailWord_695346).sum := by decide
  have hdescent : baseEnd_695346 < baseStart_695346 := by decide
  rcases family_descends (prefixWord ++ tailWord_695346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695356 : List Nat := [2, 2, 2, 2, 2, 3, 2, 1, 4]
def baseStart_695356 : Nat := 118140960795 + 695356 * 2 ^ 59
def prefixEnd_695356 : Nat := 4983230072969 + 3 ^ 40 * 695356 * 2
def baseEnd_695356 : Nat := 317379425767010355690775

theorem tailTrace_695356 : CollatzResearch.WordTrace tailWord_695356 prefixEnd_695356 317379425767010355690775 := by
  unfold tailWord_695356
  simp only [CollatzResearch.WordTrace]
  refine ⟨12680858434425722097576961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16907811245900962796769281 12680858434425722097576961)
  ·
    refine ⟨9510643825819291573182721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12680858434425722097576961 9510643825819291573182721)
    ·
      refine ⟨7132982869364468679887041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9510643825819291573182721 7132982869364468679887041)
      ·
        refine ⟨5349737152023351509915281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7132982869364468679887041 5349737152023351509915281)
        ·
          refine ⟨4012302864017513632436461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5349737152023351509915281 4012302864017513632436461)
          ·
            refine ⟨1504613574006567612163673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4012302864017513632436461 1504613574006567612163673)
            ·
              refine ⟨1128460180504925709122755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1504613574006567612163673 1128460180504925709122755)
              ·
                refine ⟨1692690270757388563684133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1128460180504925709122755 1692690270757388563684133)
                ·
                  refine ⟨317379425767010355690775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1692690270757388563684133 317379425767010355690775)
                  ·
                    rfl

theorem cell20_695356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 2, 1, 4].length) (baseStart_695356 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_695356 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_695356 prefixEnd_695356 := by exact prefixLift 695356
  have htrace : WordTrace (prefixWord ++ tailWord_695356) baseStart_695356 baseEnd_695356 := by
    simpa [prefixWord, tailWord_695356, baseEnd_695356] using wordTrace_append hprefix tailTrace_695356
  have hstable : (prefixWord ++ tailWord_695356).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695356).length < 2 ^ (prefixWord ++ tailWord_695356).sum := by decide
  have hdescent : baseEnd_695356 < baseStart_695356 := by decide
  rcases family_descends (prefixWord ++ tailWord_695356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695370 : List Nat := [3, 1, 2, 1, 1, 2, 2, 5, 3]
def baseStart_695370 : Nat := 118140960795 + 695370 * 2 ^ 59
def prefixEnd_695370 : Nat := 4983230072969 + 3 ^ 40 * 695370 * 2
def baseEnd_695370 : Nat := 317385815748488529224051

theorem tailTrace_695370 : CollatzResearch.WordTrace tailWord_695370 prefixEnd_695370 317385815748488529224051 := by
  unfold tailWord_695370
  simp only [CollatzResearch.WordTrace]
  refine ⟨6340556872700181146540891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16908151660533816390775709 6340556872700181146540891)
  ·
    refine ⟨9510835309050271719811337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6340556872700181146540891 9510835309050271719811337)
    ·
      refine ⟨7133126481787703789858503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9510835309050271719811337 7133126481787703789858503)
      ·
        refine ⟨10699689722681555684787755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7133126481787703789858503 10699689722681555684787755)
        ·
          refine ⟨16049534584022333527181633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10699689722681555684787755 16049534584022333527181633)
          ·
            refine ⟨12037150938016750145386225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16049534584022333527181633 12037150938016750145386225)
            ·
              refine ⟨9027863203512562609039669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12037150938016750145386225 9027863203512562609039669)
              ·
                refine ⟨846362175329302744597469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9027863203512562609039669 846362175329302744597469)
                ·
                  refine ⟨317385815748488529224051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 846362175329302744597469 317385815748488529224051)
                  ·
                    rfl

theorem cell20_695370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 5, 3].length) (baseStart_695370 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_695370 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_695370 prefixEnd_695370 := by exact prefixLift 695370
  have htrace : WordTrace (prefixWord ++ tailWord_695370) baseStart_695370 baseEnd_695370 := by
    simpa [prefixWord, tailWord_695370, baseEnd_695370] using wordTrace_append hprefix tailTrace_695370
  have hstable : (prefixWord ++ tailWord_695370).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695370).length < 2 ^ (prefixWord ++ tailWord_695370).sum := by decide
  have hdescent : baseEnd_695370 < baseStart_695370 := by decide
  rcases family_descends (prefixWord ++ tailWord_695370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695377 : List Nat := [1, 2, 2, 1, 3, 1, 4, 2, 4]
def baseStart_695377 : Nat := 118140960795 + 695377 * 2 ^ 59
def prefixEnd_695377 : Nat := 4983230072969 + 3 ^ 40 * 695377 * 2
def baseEnd_695377 : Nat := 317389010739227615990689

theorem tailTrace_695377 : CollatzResearch.WordTrace tailWord_695377 prefixEnd_695377 317389010739227615990689 := by
  unfold tailWord_695377
  simp only [CollatzResearch.WordTrace]
  refine ⟨25362482801775364781668385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16908321867850243187778923 25362482801775364781668385)
  ·
    refine ⟨19021862101331523586251289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25362482801775364781668385 19021862101331523586251289)
    ·
      refine ⟨14266396575998642689688467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19021862101331523586251289 14266396575998642689688467)
      ·
        refine ⟨21399594863997964034532701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14266396575998642689688467 21399594863997964034532701)
        ·
          refine ⟨8024848073999236512949763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21399594863997964034532701 8024848073999236512949763)
          ·
            refine ⟨12037272110998854769424645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8024848073999236512949763 12037272110998854769424645)
            ·
              refine ⟨2256988520812285269267121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12037272110998854769424645 2256988520812285269267121)
              ·
                refine ⟨1692741390609213951950341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2256988520812285269267121 1692741390609213951950341)
                ·
                  refine ⟨317389010739227615990689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1692741390609213951950341 317389010739227615990689)
                  ·
                    rfl

theorem cell20_695377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 2, 4].length) (baseStart_695377 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_695377 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_695377 prefixEnd_695377 := by exact prefixLift 695377
  have htrace : WordTrace (prefixWord ++ tailWord_695377) baseStart_695377 baseEnd_695377 := by
    simpa [prefixWord, tailWord_695377, baseEnd_695377] using wordTrace_append hprefix tailTrace_695377
  have hstable : (prefixWord ++ tailWord_695377).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695377).length < 2 ^ (prefixWord ++ tailWord_695377).sum := by decide
  have hdescent : baseEnd_695377 < baseStart_695377 := by decide
  rcases family_descends (prefixWord ++ tailWord_695377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695384 : List Nat := [2, 1, 2, 2, 1, 3, 3, 6]
def baseStart_695384 : Nat := 118140960795 + 695384 * 2 ^ 59
def prefixEnd_695384 : Nat := 4983230072969 + 3 ^ 40 * 695384 * 2
def baseEnd_695384 : Nat := 105797401909988900919109

theorem tailTrace_695384 : CollatzResearch.WordTrace tailWord_695384 prefixEnd_695384 105797401909988900919109 := by
  unfold tailWord_695384
  simp only [CollatzResearch.WordTrace]
  refine ⟨12681369056375002488586603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16908492075166669984782137 12681369056375002488586603)
  ·
    refine ⟨19022053584562503732879905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12681369056375002488586603 19022053584562503732879905)
    ·
      refine ⟨14266540188421877799659929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19022053584562503732879905 14266540188421877799659929)
      ·
        refine ⟨10699905141316408349744947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14266540188421877799659929 10699905141316408349744947)
        ·
          refine ⟨16049857711974612524617421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10699905141316408349744947 16049857711974612524617421)
          ·
            refine ⟨6018696641990479696731533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16049857711974612524617421 6018696641990479696731533)
            ·
              refine ⟨2257011240746429886274325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6018696641990479696731533 2257011240746429886274325)
              ·
                refine ⟨105797401909988900919109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2257011240746429886274325 105797401909988900919109)
                ·
                  rfl

theorem cell20_695384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 6].length) (baseStart_695384 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_695384 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_695384 prefixEnd_695384 := by exact prefixLift 695384
  have htrace : WordTrace (prefixWord ++ tailWord_695384) baseStart_695384 baseEnd_695384 := by
    simpa [prefixWord, tailWord_695384, baseEnd_695384] using wordTrace_append hprefix tailTrace_695384
  have hstable : (prefixWord ++ tailWord_695384).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695384).length < 2 ^ (prefixWord ++ tailWord_695384).sum := by decide
  have hdescent : baseEnd_695384 < baseStart_695384 := by decide
  rcases family_descends (prefixWord ++ tailWord_695384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695391 : List Nat := [1, 1, 2, 3, 1, 1, 3, 1, 7]
def baseStart_695391 : Nat := 118140960795 + 695391 * 2 ^ 59
def prefixEnd_695391 : Nat := 4983230072969 + 3 ^ 40 * 695391 * 2
def baseEnd_695391 : Nat := 317395400720705789523965

theorem tailTrace_695391 : CollatzResearch.WordTrace tailWord_695391 prefixEnd_695391 317395400720705789523965 := by
  unfold tailWord_695391
  simp only [CollatzResearch.WordTrace]
  refine ⟨25362993423724645172678027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16908662282483096781785351 25362993423724645172678027)
  ·
    refine ⟨38044490135586967759017041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25362993423724645172678027 38044490135586967759017041)
    ·
      refine ⟨28533367601690225819262781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38044490135586967759017041 28533367601690225819262781)
      ·
        refine ⟨10700012850633834682223543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28533367601690225819262781 10700012850633834682223543)
        ·
          refine ⟨16050019275950752023335315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10700012850633834682223543 16050019275950752023335315)
          ·
            refine ⟨24075028913926128035002973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16050019275950752023335315 24075028913926128035002973)
            ·
              refine ⟨9028135842722298013126115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24075028913926128035002973 9028135842722298013126115)
              ·
                refine ⟨13542203764083447019689173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9028135842722298013126115 13542203764083447019689173)
                ·
                  refine ⟨317395400720705789523965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13542203764083447019689173 317395400720705789523965)
                  ·
                    rfl

theorem cell20_695391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 1, 7].length) (baseStart_695391 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_695391 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_695391 prefixEnd_695391 := by exact prefixLift 695391
  have htrace : WordTrace (prefixWord ++ tailWord_695391) baseStart_695391 baseEnd_695391 := by
    simpa [prefixWord, tailWord_695391, baseEnd_695391] using wordTrace_append hprefix tailTrace_695391
  have hstable : (prefixWord ++ tailWord_695391).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695391).length < 2 ^ (prefixWord ++ tailWord_695391).sum := by decide
  have hdescent : baseEnd_695391 < baseStart_695391 := by decide
  rcases family_descends (prefixWord ++ tailWord_695391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695408 : List Nat := [2, 1, 1, 1, 5, 1, 2, 4, 3]
def baseStart_695408 : Nat := 118140960795 + 695408 * 2 ^ 59
def prefixEnd_695408 : Nat := 4983230072969 + 3 ^ 40 * 695408 * 2
def baseEnd_695408 : Nat := 317403159983929285957229

theorem tailTrace_695408 : CollatzResearch.WordTrace tailWord_695408 prefixEnd_695408 317403159983929285957229 := by
  unfold tailWord_695408
  simp only [CollatzResearch.WordTrace]
  refine ⟨12681806732331528538023439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16909075643108704717364585 12681806732331528538023439)
  ·
    refine ⟨19022710098497292807035159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12681806732331528538023439 19022710098497292807035159)
    ·
      refine ⟨28534065147745939210552739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19022710098497292807035159 28534065147745939210552739)
      ·
        refine ⟨42801097721618908815829109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28534065147745939210552739 42801097721618908815829109)
        ·
          refine ⟨4012602911401772701483979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42801097721618908815829109 4012602911401772701483979)
          ·
            refine ⟨6018904367102659052225969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4012602911401772701483979 6018904367102659052225969)
            ·
              refine ⟨4514178275326994289169477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6018904367102659052225969 4514178275326994289169477)
              ·
                refine ⟨846408426623811429219277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4514178275326994289169477 846408426623811429219277)
                ·
                  refine ⟨317403159983929285957229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 846408426623811429219277 317403159983929285957229)
                  ·
                    rfl

theorem cell20_695408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 4, 3].length) (baseStart_695408 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_695408 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_695408 prefixEnd_695408 := by exact prefixLift 695408
  have htrace : WordTrace (prefixWord ++ tailWord_695408) baseStart_695408 baseEnd_695408 := by
    simpa [prefixWord, tailWord_695408, baseEnd_695408] using wordTrace_append hprefix tailTrace_695408
  have hstable : (prefixWord ++ tailWord_695408).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695408).length < 2 ^ (prefixWord ++ tailWord_695408).sum := by decide
  have hdescent : baseEnd_695408 < baseStart_695408 := by decide
  rcases family_descends (prefixWord ++ tailWord_695408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695425 : List Nat := [1, 2, 4, 2, 2, 2, 1, 3, 3]
def baseStart_695425 : Nat := 118140960795 + 695425 * 2 ^ 59
def prefixEnd_695425 : Nat := 4983230072969 + 3 ^ 40 * 695425 * 2
def baseEnd_695425 : Nat := 317410919247152782390493

theorem tailTrace_695425 : CollatzResearch.WordTrace tailWord_695425 prefixEnd_695425 317410919247152782390493 := by
  unfold tailWord_695425
  simp only [CollatzResearch.WordTrace]
  refine ⟨25364233505601468979415729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16909489003734312652943819 25364233505601468979415729)
  ·
    refine ⟨19023175129201101734561797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25364233505601468979415729 19023175129201101734561797)
    ·
      refine ⟨3566845336725206575230337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19023175129201101734561797 3566845336725206575230337)
      ·
        refine ⟨2675134002543904931422753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3566845336725206575230337 2675134002543904931422753)
        ·
          refine ⟨2006350501907928698567065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2675134002543904931422753 2006350501907928698567065)
          ·
            refine ⟨1504762876430946523925299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2006350501907928698567065 1504762876430946523925299)
            ·
              refine ⟨2257144314646419785887949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1504762876430946523925299 2257144314646419785887949)
              ·
                refine ⟨846429117992407419707981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2257144314646419785887949 846429117992407419707981)
                ·
                  refine ⟨317410919247152782390493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 846429117992407419707981 317410919247152782390493)
                  ·
                    rfl

theorem cell20_695425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 3, 3].length) (baseStart_695425 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_695425 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_695425 prefixEnd_695425 := by exact prefixLift 695425
  have htrace : WordTrace (prefixWord ++ tailWord_695425) baseStart_695425 baseEnd_695425 := by
    simpa [prefixWord, tailWord_695425, baseEnd_695425] using wordTrace_append hprefix tailTrace_695425
  have hstable : (prefixWord ++ tailWord_695425).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695425).length < 2 ^ (prefixWord ++ tailWord_695425).sum := by decide
  have hdescent : baseEnd_695425 < baseStart_695425 := by decide
  rcases family_descends (prefixWord ++ tailWord_695425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695460 : List Nat := [2, 3, 1, 2, 3, 9]
def baseStart_695460 : Nat := 118140960795 + 695460 * 2 ^ 59
def prefixEnd_695460 : Nat := 4983230072969 + 3 ^ 40 * 695460 * 2
def baseEnd_695460 : Nat := 11756551637068452452729

theorem tailTrace_695460 : CollatzResearch.WordTrace tailWord_695460 prefixEnd_695460 11756551637068452452729 := by
  unfold tailWord_695460
  simp only [CollatzResearch.WordTrace]
  refine ⟨12682755030237334978469917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16910340040316446637959889 12682755030237334978469917)
  ·
    refine ⟨4756033136339000616926219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12682755030237334978469917 4756033136339000616926219)
    ·
      refine ⟨7134049704508500925389329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4756033136339000616926219 7134049704508500925389329)
      ·
        refine ⟨5350537278381375694041997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7134049704508500925389329 5350537278381375694041997)
        ·
          refine ⟨2006451479393015885265749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5350537278381375694041997 2006451479393015885265749)
          ·
            refine ⟨11756551637068452452729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2006451479393015885265749 11756551637068452452729)
            ·
              rfl

theorem cell20_695460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 9].length) (baseStart_695460 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_695460 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_695460 prefixEnd_695460 := by exact prefixLift 695460
  have htrace : WordTrace (prefixWord ++ tailWord_695460) baseStart_695460 baseEnd_695460 := by
    simpa [prefixWord, tailWord_695460, baseEnd_695460] using wordTrace_append hprefix tailTrace_695460
  have hstable : (prefixWord ++ tailWord_695460).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695460).length < 2 ^ (prefixWord ++ tailWord_695460).sum := by decide
  have hdescent : baseEnd_695460 < baseStart_695460 := by decide
  rcases family_descends (prefixWord ++ tailWord_695460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695463 : List Nat := [1, 1, 6, 2, 1, 1, 1, 4, 3]
def baseStart_695463 : Nat := 118140960795 + 695463 * 2 ^ 59
def prefixEnd_695463 : Nat := 4983230072969 + 3 ^ 40 * 695463 * 2
def baseEnd_695463 : Nat := 317428263482593539123671

theorem tailTrace_695463 : CollatzResearch.WordTrace tailWord_695463 prefixEnd_695463 317428263482593539123671 := by
  unfold tailWord_695463
  simp only [CollatzResearch.WordTrace]
  refine ⟨25365619479463801469299043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16910412986309200979532695 25365619479463801469299043)
  ·
    refine ⟨38048429219195702203948565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25365619479463801469299043 38048429219195702203948565)
    ·
      refine ⟨1783520119649798540810089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 38048429219195702203948565 1783520119649798540810089)
      ·
        refine ⟨1337640089737348905607567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1783520119649798540810089 1337640089737348905607567)
        ·
          refine ⟨2006460134606023358411351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1337640089737348905607567 2006460134606023358411351)
          ·
            refine ⟨3009690201909035037617027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2006460134606023358411351 3009690201909035037617027)
            ·
              refine ⟨4514535302863552556425541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3009690201909035037617027 4514535302863552556425541)
              ·
                refine ⟨846475369286916104329789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4514535302863552556425541 846475369286916104329789)
                ·
                  refine ⟨317428263482593539123671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 846475369286916104329789 317428263482593539123671)
                  ·
                    rfl

theorem cell20_695463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 4, 3].length) (baseStart_695463 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_695463 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_695463 prefixEnd_695463 := by exact prefixLift 695463
  have htrace : WordTrace (prefixWord ++ tailWord_695463) baseStart_695463 baseEnd_695463 := by
    simpa [prefixWord, tailWord_695463, baseEnd_695463] using wordTrace_append hprefix tailTrace_695463
  have hstable : (prefixWord ++ tailWord_695463).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695463).length < 2 ^ (prefixWord ++ tailWord_695463).sum := by decide
  have hdescent : baseEnd_695463 < baseStart_695463 := by decide
  rcases family_descends (prefixWord ++ tailWord_695463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695466 : List Nat := [3, 1, 5, 1, 1, 2, 1, 4, 2]
def baseStart_695466 : Nat := 118140960795 + 695466 * 2 ^ 59
def prefixEnd_695466 : Nat := 4983230072969 + 3 ^ 40 * 695466 * 2
def baseEnd_695466 : Nat := 317429632764338862023659

theorem tailTrace_695466 : CollatzResearch.WordTrace tailWord_695466 prefixEnd_695466 317429632764338862023659 := by
  unfold tailWord_695466
  simp only [CollatzResearch.WordTrace]
  refine ⟨6341432224613233245414563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16910485932301955321105501 6341432224613233245414563)
  ·
    refine ⟨9512148336919849868121845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6341432224613233245414563 9512148336919849868121845)
    ·
      refine ⟨891763906586235925136423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9512148336919849868121845 891763906586235925136423)
      ·
        refine ⟨1337645859879353887704635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 891763906586235925136423 1337645859879353887704635)
        ·
          refine ⟨2006468789819030831556953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1337645859879353887704635 2006468789819030831556953)
          ·
            refine ⟨1504851592364273123667715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2006468789819030831556953 1504851592364273123667715)
            ·
              refine ⟨2257277388546409685501573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1504851592364273123667715 2257277388546409685501573)
              ·
                refine ⟨423239510352451816031545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2257277388546409685501573 423239510352451816031545)
                ·
                  refine ⟨317429632764338862023659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 423239510352451816031545 317429632764338862023659)
                  ·
                    rfl

theorem cell20_695466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 4, 2].length) (baseStart_695466 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_695466 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_695466 prefixEnd_695466 := by exact prefixLift 695466
  have htrace : WordTrace (prefixWord ++ tailWord_695466) baseStart_695466 baseEnd_695466 := by
    simpa [prefixWord, tailWord_695466, baseEnd_695466] using wordTrace_append hprefix tailTrace_695466
  have hstable : (prefixWord ++ tailWord_695466).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695466).length < 2 ^ (prefixWord ++ tailWord_695466).sum := by decide
  have hdescent : baseEnd_695466 < baseStart_695466 := by decide
  rcases family_descends (prefixWord ++ tailWord_695466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695490 : List Nat := [3, 5, 1, 1, 2, 1, 3, 4]
def baseStart_695490 : Nat := 118140960795 + 695490 * 2 ^ 59
def prefixEnd_695490 : Nat := 4983230072969 + 3 ^ 40 * 695490 * 2
def baseEnd_695490 : Nat := 105813529006100481741187

theorem tailTrace_695490 : CollatzResearch.WordTrace tailWord_695490 prefixEnd_695490 105813529006100481741187 := by
  unfold tailWord_695490
  simp only [CollatzResearch.WordTrace]
  refine ⟨6341651062591496270132981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16911069500243990053687949 6341651062591496270132981)
  ·
    refine ⟨594529787117952775324967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6341651062591496270132981 594529787117952775324967)
    ·
      refine ⟨891794680676929162987451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 594529787117952775324967 891794680676929162987451)
      ·
        refine ⟨1337692021015393744481177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 891794680676929162987451 1337692021015393744481177)
        ·
          refine ⟨1003269015761545308360883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1337692021015393744481177 1003269015761545308360883)
          ·
            refine ⟨1504903523642317962541325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1003269015761545308360883 1504903523642317962541325)
            ·
              refine ⟨564338821365869235952997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1504903523642317962541325 564338821365869235952997)
              ·
                refine ⟨105813529006100481741187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 564338821365869235952997 105813529006100481741187)
                ·
                  rfl

theorem cell20_695490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 3, 4].length) (baseStart_695490 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_695490 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_695490 prefixEnd_695490 := by exact prefixLift 695490
  have htrace : WordTrace (prefixWord ++ tailWord_695490) baseStart_695490 baseEnd_695490 := by
    simpa [prefixWord, tailWord_695490, baseEnd_695490] using wordTrace_append hprefix tailTrace_695490
  have hstable : (prefixWord ++ tailWord_695490).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695490).length < 2 ^ (prefixWord ++ tailWord_695490).sum := by decide
  have hdescent : baseEnd_695490 < baseStart_695490 := by decide
  rcases family_descends (prefixWord ++ tailWord_695490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695505 : List Nat := [1, 2, 2, 1, 2, 2, 1, 4, 5]
def baseStart_695505 : Nat := 118140960795 + 695505 * 2 ^ 59
def prefixEnd_695505 : Nat := 4983230072969 + 3 ^ 40 * 695505 * 2
def baseEnd_695505 : Nat := 317447433427028059723499

theorem tailTrace_695505 : CollatzResearch.WordTrace tailWord_695505 prefixEnd_695505 317447433427028059723499 := by
  unfold tailWord_695505
  simp only [CollatzResearch.WordTrace]
  refine ⟨25367151345311642642327969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16911434230207761761551979 25367151345311642642327969)
  ·
    refine ⟨19025363508983731981745977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25367151345311642642327969 19025363508983731981745977)
    ·
      refine ⟨14269022631737798986309483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19025363508983731981745977 14269022631737798986309483)
      ·
        refine ⟨21403533947606698479464225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14269022631737798986309483 21403533947606698479464225)
        ·
          refine ⟨16052650460705023859598169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21403533947606698479464225 16052650460705023859598169)
          ·
            refine ⟨12039487845528767894698627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16052650460705023859598169 12039487845528767894698627)
            ·
              refine ⟨18059231768293151842047941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12039487845528767894698627 18059231768293151842047941)
              ·
                refine ⟨3386105956554965970383989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18059231768293151842047941 3386105956554965970383989)
                ·
                  refine ⟨317447433427028059723499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3386105956554965970383989 317447433427028059723499)
                  ·
                    rfl

theorem cell20_695505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 4, 5].length) (baseStart_695505 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_695505 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_695505 prefixEnd_695505 := by exact prefixLift 695505
  have htrace : WordTrace (prefixWord ++ tailWord_695505) baseStart_695505 baseEnd_695505 := by
    simpa [prefixWord, tailWord_695505, baseEnd_695505] using wordTrace_append hprefix tailTrace_695505
  have hstable : (prefixWord ++ tailWord_695505).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695505).length < 2 ^ (prefixWord ++ tailWord_695505).sum := by decide
  have hdescent : baseEnd_695505 < baseStart_695505 := by decide
  rcases family_descends (prefixWord ++ tailWord_695505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695539 : List Nat := [1, 1, 1, 2, 2, 6, 3, 1, 3]
def baseStart_695539 : Nat := 118140960795 + 695539 * 2 ^ 59
def prefixEnd_695539 : Nat := 4983230072969 + 3 ^ 40 * 695539 * 2
def baseEnd_695539 : Nat := 317462951953475052590027

theorem tailTrace_695539 : CollatzResearch.WordTrace tailWord_695539 prefixEnd_695539 317462951953475052590027 := by
  unfold tailWord_695539
  simp only [CollatzResearch.WordTrace]
  refine ⟨25368391427188466449065671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16912260951458977632710447 25368391427188466449065671)
  ·
    refine ⟨38052587140782699673598507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25368391427188466449065671 38052587140782699673598507)
    ·
      refine ⟨57078880711174049510397761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38052587140782699673598507 57078880711174049510397761)
      ·
        refine ⟨42809160533380537132798321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57078880711174049510397761 42809160533380537132798321)
        ·
          refine ⟨32106870400035402849598741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42809160533380537132798321 32106870400035402849598741)
          ·
            refine ⟨1505009550001659508574941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 32106870400035402849598741 1505009550001659508574941)
            ·
              refine ⟨564378581250622315715603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1505009550001659508574941 564378581250622315715603)
              ·
                refine ⟨846567871875933473573405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 564378581250622315715603 846567871875933473573405)
                ·
                  refine ⟨317462951953475052590027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 846567871875933473573405 317462951953475052590027)
                  ·
                    rfl

theorem cell20_695539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 3, 1, 3].length) (baseStart_695539 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_695539 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_695539 prefixEnd_695539 := by exact prefixLift 695539
  have htrace : WordTrace (prefixWord ++ tailWord_695539) baseStart_695539 baseEnd_695539 := by
    simpa [prefixWord, tailWord_695539, baseEnd_695539] using wordTrace_append hprefix tailTrace_695539
  have hstable : (prefixWord ++ tailWord_695539).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695539).length < 2 ^ (prefixWord ++ tailWord_695539).sum := by decide
  have hdescent : baseEnd_695539 < baseStart_695539 := by decide
  rcases family_descends (prefixWord ++ tailWord_695539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695553 : List Nat := [1, 2, 4, 1, 1, 3, 4, 4]
def baseStart_695553 : Nat := 118140960795 + 695553 * 2 ^ 59
def prefixEnd_695553 : Nat := 4983230072969 + 3 ^ 40 * 695553 * 2
def baseEnd_695553 : Nat := 105823113978317742041101

theorem tailTrace_695553 : CollatzResearch.WordTrace tailWord_695553 prefixEnd_695553 105823113978317742041101 := by
  unfold tailWord_695553
  simp only [CollatzResearch.WordTrace]
  refine ⟨25368902049137746840075313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16912601366091831226716875 25368902049137746840075313)
  ·
    refine ⟨19026676536853310130056485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25368902049137746840075313 19026676536853310130056485)
    ·
      refine ⟨3567501850659995649385591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19026676536853310130056485 3567501850659995649385591)
      ·
        refine ⟨5351252775989993474078387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3567501850659995649385591 5351252775989993474078387)
        ·
          refine ⟨8026879163984990211117581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5351252775989993474078387 8026879163984990211117581)
          ·
            refine ⟨3010079686494371329169093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8026879163984990211117581 3010079686494371329169093)
            ·
              refine ⟨564389941217694624219205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3010079686494371329169093 564389941217694624219205)
              ·
                refine ⟨105823113978317742041101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 564389941217694624219205 105823113978317742041101)
                ·
                  rfl

theorem cell20_695553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 4, 4].length) (baseStart_695553 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_695553 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_695553 prefixEnd_695553 := by exact prefixLift 695553
  have htrace : WordTrace (prefixWord ++ tailWord_695553) baseStart_695553 baseEnd_695553 := by
    simpa [prefixWord, tailWord_695553, baseEnd_695553] using wordTrace_append hprefix tailTrace_695553
  have hstable : (prefixWord ++ tailWord_695553).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695553).length < 2 ^ (prefixWord ++ tailWord_695553).sum := by decide
  have hdescent : baseEnd_695553 < baseStart_695553 := by decide
  rcases family_descends (prefixWord ++ tailWord_695553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695563 : List Nat := [1, 1, 1, 1, 5, 5, 1, 3, 2]
def baseStart_695563 : Nat := 118140960795 + 695563 * 2 ^ 59
def prefixEnd_695563 : Nat := 4983230072969 + 3 ^ 40 * 695563 * 2
def baseEnd_695563 : Nat := 317473906207437635789929

theorem tailTrace_695563 : CollatzResearch.WordTrace tailWord_695563 prefixEnd_695563 317473906207437635789929 := by
  unfold tailWord_695563
  simp only [CollatzResearch.WordTrace]
  refine ⟨25369266779101518547939343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16912844519401012365292895 25369266779101518547939343)
  ·
    refine ⟨38053900168652277821909015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25369266779101518547939343 38053900168652277821909015)
    ·
      refine ⟨57080850252978416732863523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38053900168652277821909015 57080850252978416732863523)
      ·
        refine ⟨85621275379467625099295285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57080850252978416732863523 85621275379467625099295285)
        ·
          refine ⟨8026994566825089853058933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 85621275379467625099295285 8026994566825089853058933)
          ·
            refine ⟨752530740639852173724275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8026994566825089853058933 752530740639852173724275)
            ·
              refine ⟨1128796110959778260586413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 752530740639852173724275 1128796110959778260586413)
              ·
                refine ⟨423298541609916847719905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1128796110959778260586413 423298541609916847719905)
                ·
                  refine ⟨317473906207437635789929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 423298541609916847719905 317473906207437635789929)
                  ·
                    rfl

theorem cell20_695563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 1, 3, 2].length) (baseStart_695563 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_695563 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_695563 prefixEnd_695563 := by exact prefixLift 695563
  have htrace : WordTrace (prefixWord ++ tailWord_695563) baseStart_695563 baseEnd_695563 := by
    simpa [prefixWord, tailWord_695563, baseEnd_695563] using wordTrace_append hprefix tailTrace_695563
  have hstable : (prefixWord ++ tailWord_695563).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695563).length < 2 ^ (prefixWord ++ tailWord_695563).sum := by decide
  have hdescent : baseEnd_695563 < baseStart_695563 := by decide
  rcases family_descends (prefixWord ++ tailWord_695563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695594 : List Nat := [3, 1, 4, 2, 1, 1, 4, 1, 3]
def baseStart_695594 : Nat := 118140960795 + 695594 * 2 ^ 59
def prefixEnd_695594 : Nat := 4983230072969 + 3 ^ 40 * 695594 * 2
def baseEnd_695594 : Nat := 317488055452139305756469

theorem tailTrace_695594 : CollatzResearch.WordTrace tailWord_695594 prefixEnd_695594 317488055452139305756469 := by
  unfold tailWord_695594
  simp only [CollatzResearch.WordTrace]
  refine ⟨6342599360497302710579459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16913598294659473894878557 6342599360497302710579459)
  ·
    refine ⟨9513899040745954065869189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6342599360497302710579459 9513899040745954065869189)
    ·
      refine ⟨1783856070139866387350473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9513899040745954065869189 1783856070139866387350473)
      ·
        refine ⟨1337892052604899790512855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1783856070139866387350473 1337892052604899790512855)
        ·
          refine ⟨2006838078907349685769283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1337892052604899790512855 2006838078907349685769283)
          ·
            refine ⟨3010257118361024528653925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2006838078907349685769283 3010257118361024528653925)
            ·
              refine ⟨564423209692692099122611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3010257118361024528653925 564423209692692099122611)
              ·
                refine ⟨846634814539038148683917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 564423209692692099122611 846634814539038148683917)
                ·
                  refine ⟨317488055452139305756469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 846634814539038148683917 317488055452139305756469)
                  ·
                    rfl

theorem cell20_695594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 4, 1, 3].length) (baseStart_695594 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_695594 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_695594 prefixEnd_695594 := by exact prefixLift 695594
  have htrace : WordTrace (prefixWord ++ tailWord_695594) baseStart_695594 baseEnd_695594 := by
    simpa [prefixWord, tailWord_695594, baseEnd_695594] using wordTrace_append hprefix tailTrace_695594
  have hstable : (prefixWord ++ tailWord_695594).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695594).length < 2 ^ (prefixWord ++ tailWord_695594).sum := by decide
  have hdescent : baseEnd_695594 < baseStart_695594 := by decide
  rcases family_descends (prefixWord ++ tailWord_695594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695612 : List Nat := [2, 2, 2, 2, 1, 3, 2, 6]
def baseStart_695612 : Nat := 118140960795 + 695612 * 2 ^ 59
def prefixEnd_695612 : Nat := 4983230072969 + 3 ^ 40 * 695612 * 2
def baseEnd_695612 : Nat := 105832090380870414385465

theorem tailTrace_695612 : CollatzResearch.WordTrace tailWord_695612 prefixEnd_695612 105832090380870414385465 := by
  unfold tailWord_695612
  simp only [CollatzResearch.WordTrace]
  refine ⟨12685526977961999958236545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16914035970615999944315393 12685526977961999958236545)
  ·
    refine ⟨9514145233471499968677409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12685526977961999958236545 9514145233471499968677409)
    ·
      refine ⟨7135608925103624976508057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9514145233471499968677409 7135608925103624976508057)
      ·
        refine ⟨5351706693827718732381043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7135608925103624976508057 5351706693827718732381043)
        ·
          refine ⟨8027560040741578098571565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5351706693827718732381043 8027560040741578098571565)
          ·
            refine ⟨3010335015278091786964337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8027560040741578098571565 3010335015278091786964337)
            ·
              refine ⟨2257751261458568840223253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3010335015278091786964337 2257751261458568840223253)
              ·
                refine ⟨105832090380870414385465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2257751261458568840223253 105832090380870414385465)
                ·
                  rfl

theorem cell20_695612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 6].length) (baseStart_695612 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_695612 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_695612 prefixEnd_695612 := by exact prefixLift 695612
  have htrace : WordTrace (prefixWord ++ tailWord_695612) baseStart_695612 baseEnd_695612 := by
    simpa [prefixWord, tailWord_695612, baseEnd_695612] using wordTrace_append hprefix tailTrace_695612
  have hstable : (prefixWord ++ tailWord_695612).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695612).length < 2 ^ (prefixWord ++ tailWord_695612).sum := by decide
  have hdescent : baseEnd_695612 < baseStart_695612 := by decide
  rcases family_descends (prefixWord ++ tailWord_695612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695629 : List Nat := [1, 6, 1, 3, 9]
def baseStart_695629 : Nat := 118140960795 + 695629 * 2 ^ 59
def prefixEnd_695629 : Nat := 4983230072969 + 3 ^ 40 * 695629 * 2
def baseEnd_695629 : Nat := 3919802844516478266539

theorem tailTrace_695629 : CollatzResearch.WordTrace tailWord_695629 prefixEnd_695629 3919802844516478266539 := by
  unfold tailWord_695629
  simp only [CollatzResearch.WordTrace]
  refine ⟨25371673996862411819841941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16914449331241607879894627 25371673996862411819841941)
  ·
    refine ⟨1189297218602925554055091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 25371673996862411819841941 1189297218602925554055091)
    ·
      refine ⟨1783945827904388331082637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1189297218602925554055091 1783945827904388331082637)
      ·
        refine ⟨668979685464145624155989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1783945827904388331082637 668979685464145624155989)
        ·
          refine ⟨3919802844516478266539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 668979685464145624155989 3919802844516478266539)
          ·
            rfl

theorem cell20_695629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 9].length) (baseStart_695629 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_695629 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_695629 prefixEnd_695629 := by exact prefixLift 695629
  have htrace : WordTrace (prefixWord ++ tailWord_695629) baseStart_695629 baseEnd_695629 := by
    simpa [prefixWord, tailWord_695629, baseEnd_695629] using wordTrace_append hprefix tailTrace_695629
  have hstable : (prefixWord ++ tailWord_695629).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695629).length < 2 ^ (prefixWord ++ tailWord_695629).sum := by decide
  have hdescent : baseEnd_695629 < baseStart_695629 := by decide
  rcases family_descends (prefixWord ++ tailWord_695629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695639 : List Nat := [1, 1, 3, 2, 3, 2, 4, 2, 2]
def baseStart_695639 : Nat := 118140960795 + 695639 * 2 ^ 59
def prefixEnd_695639 : Nat := 4983230072969 + 3 ^ 40 * 695639 * 2
def baseEnd_695639 : Nat := 317508594678319149256285

theorem tailTrace_695639 : CollatzResearch.WordTrace tailWord_695639 prefixEnd_695639 317508594678319149256285 := by
  unfold tailWord_695639
  simp only [CollatzResearch.WordTrace]
  refine ⟨25372038726826183527705971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16914692484550789018470647 25372038726826183527705971)
  ·
    refine ⟨38058058090239275291558957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25372038726826183527705971 38058058090239275291558957)
    ·
      refine ⟨14271771783839728234334609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38058058090239275291558957 14271771783839728234334609)
      ·
        refine ⟨10703828837879796175750957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14271771783839728234334609 10703828837879796175750957)
        ·
          refine ⟨4013935814204923565906609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10703828837879796175750957 4013935814204923565906609)
          ·
            refine ⟨3010451860653692674429957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4013935814204923565906609 3010451860653692674429957)
            ·
              refine ⟨564459723872567376455617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3010451860653692674429957 564459723872567376455617)
              ·
                refine ⟨423344792904425532341713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 564459723872567376455617 423344792904425532341713)
                ·
                  refine ⟨317508594678319149256285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 423344792904425532341713 317508594678319149256285)
                  ·
                    rfl

theorem cell20_695639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 4, 2, 2].length) (baseStart_695639 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_695639 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_695639 prefixEnd_695639 := by exact prefixLift 695639
  have htrace : WordTrace (prefixWord ++ tailWord_695639) baseStart_695639 baseEnd_695639 := by
    simpa [prefixWord, tailWord_695639, baseEnd_695639] using wordTrace_append hprefix tailTrace_695639
  have hstable : (prefixWord ++ tailWord_695639).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695639).length < 2 ^ (prefixWord ++ tailWord_695639).sum := by decide
  have hdescent : baseEnd_695639 < baseStart_695639 := by decide
  rcases family_descends (prefixWord ++ tailWord_695639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695688 : List Nat := [2, 1, 3, 3, 1, 3, 7]
def baseStart_695688 : Nat := 118140960795 + 695688 * 2 ^ 59
def prefixEnd_695688 : Nat := 4983230072969 + 3 ^ 40 * 695688 * 2
def baseEnd_695688 : Nat := 35281217734832528513639

theorem tailTrace_695688 : CollatzResearch.WordTrace tailWord_695688 prefixEnd_695688 35281217734832528513639 := by
  unfold tailWord_695688
  simp only [CollatzResearch.WordTrace]
  refine ⟨12686912951824332448119859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16915883935765776597493145 12686912951824332448119859)
  ·
    refine ⟨19030369427736498672179789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12686912951824332448119859 19030369427736498672179789)
    ·
      refine ⟨7136388535401187002067421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19030369427736498672179789 7136388535401187002067421)
      ·
        refine ⟨2676145700775445125775283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7136388535401187002067421 2676145700775445125775283)
        ·
          refine ⟨4014218551163167688662925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2676145700775445125775283 4014218551163167688662925)
          ·
            refine ⟨1505331956686187883248597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4014218551163167688662925 1505331956686187883248597)
            ·
              refine ⟨35281217734832528513639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1505331956686187883248597 35281217734832528513639)
              ·
                rfl

theorem cell20_695688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 7].length) (baseStart_695688 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_695688 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_695688 prefixEnd_695688 := by exact prefixLift 695688
  have htrace : WordTrace (prefixWord ++ tailWord_695688) baseStart_695688 baseEnd_695688 := by
    simpa [prefixWord, tailWord_695688, baseEnd_695688] using wordTrace_append hprefix tailTrace_695688
  have hstable : (prefixWord ++ tailWord_695688).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695688).length < 2 ^ (prefixWord ++ tailWord_695688).sum := by decide
  have hdescent : baseEnd_695688 < baseStart_695688 := by decide
  rcases family_descends (prefixWord ++ tailWord_695688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695719 : List Nat := [1, 1, 6, 1, 1, 1, 1, 4, 4]
def baseStart_695719 : Nat := 118140960795 + 695719 * 2 ^ 59
def prefixEnd_695719 : Nat := 4983230072969 + 3 ^ 40 * 695719 * 2
def baseEnd_695719 : Nat := 317545108858194426589291

theorem tailTrace_695719 : CollatzResearch.WordTrace tailWord_695719 prefixEnd_695719 317545108858194426589291 := by
  unfold tailWord_695719
  simp only [CollatzResearch.WordTrace]
  refine ⟨25374956566536357190618211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16916637711024238127078807 25374956566536357190618211)
  ·
    refine ⟨38062434849804535785927317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25374956566536357190618211 38062434849804535785927317)
    ·
      refine ⟨1784176633584587614965343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 38062434849804535785927317 1784176633584587614965343)
      ·
        refine ⟨2676264950376881422448015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1784176633584587614965343 2676264950376881422448015)
        ·
          refine ⟨4014397425565322133672023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2676264950376881422448015 4014397425565322133672023)
          ·
            refine ⟨6021596138347983200508035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4014397425565322133672023 6021596138347983200508035)
            ·
              refine ⟨9032394207521974800762053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6021596138347983200508035 9032394207521974800762053)
              ·
                refine ⟨1693573913910370275142885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9032394207521974800762053 1693573913910370275142885)
                ·
                  refine ⟨317545108858194426589291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1693573913910370275142885 317545108858194426589291)
                  ·
                    rfl

theorem cell20_695719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 4, 4].length) (baseStart_695719 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_695719 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_695719 prefixEnd_695719 := by exact prefixLift 695719
  have htrace : WordTrace (prefixWord ++ tailWord_695719) baseStart_695719 baseEnd_695719 := by
    simpa [prefixWord, tailWord_695719, baseEnd_695719] using wordTrace_append hprefix tailTrace_695719
  have hstable : (prefixWord ++ tailWord_695719).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695719).length < 2 ^ (prefixWord ++ tailWord_695719).sum := by decide
  have hdescent : baseEnd_695719 < baseStart_695719 := by decide
  rcases family_descends (prefixWord ++ tailWord_695719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695736 : List Nat := [2, 1, 2, 1, 2, 2, 5, 3, 2]
def baseStart_695736 : Nat := 118140960795 + 695736 * 2 ^ 59
def prefixEnd_695736 : Nat := 4983230072969 + 3 ^ 40 * 695736 * 2
def baseEnd_695736 : Nat := 317552868121417923022555

theorem tailTrace_695736 : CollatzResearch.WordTrace tailWord_695736 prefixEnd_695736 317552868121417923022555 := by
  unfold tailWord_695736
  simp only [CollatzResearch.WordTrace]
  refine ⟨12687788303737384546993531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16917051071649846062658041 12687788303737384546993531)
  ·
    refine ⟨19031682455606076820490297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12687788303737384546993531 19031682455606076820490297)
    ·
      refine ⟨14273761841704557615367723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19031682455606076820490297 14273761841704557615367723)
      ·
        refine ⟨21410642762556836423051585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14273761841704557615367723 21410642762556836423051585)
        ·
          refine ⟨16057982071917627317288689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21410642762556836423051585 16057982071917627317288689)
          ·
            refine ⟨12043486553938220487966517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16057982071917627317288689 12043486553938220487966517)
            ·
              refine ⟨1129076864431708170746861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12043486553938220487966517 1129076864431708170746861)
              ·
                refine ⟨423403824161890564030073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1129076864431708170746861 423403824161890564030073)
                ·
                  refine ⟨317552868121417923022555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 423403824161890564030073 317552868121417923022555)
                  ·
                    rfl

theorem cell20_695736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 5, 3, 2].length) (baseStart_695736 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_695736 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_695736 prefixEnd_695736 := by exact prefixLift 695736
  have htrace : WordTrace (prefixWord ++ tailWord_695736) baseStart_695736 baseEnd_695736 := by
    simpa [prefixWord, tailWord_695736, baseEnd_695736] using wordTrace_append hprefix tailTrace_695736
  have hstable : (prefixWord ++ tailWord_695736).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695736).length < 2 ^ (prefixWord ++ tailWord_695736).sum := by decide
  have hdescent : baseEnd_695736 < baseStart_695736 := by decide
  rcases family_descends (prefixWord ++ tailWord_695736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695747 : List Nat := [1, 1, 1, 3, 1, 1, 12]
def baseStart_695747 : Nat := 118140960795 + 695747 * 2 ^ 59
def prefixEnd_695747 : Nat := 4983230072969 + 3 ^ 40 * 695747 * 2
def baseEnd_695747 : Nat := 35284209869016752628427

theorem tailTrace_695747 : CollatzResearch.WordTrace tailWord_695747 prefixEnd_695747 35284209869016752628427 := by
  unfold tailWord_695747
  simp only [CollatzResearch.WordTrace]
  refine ⟨25375977810434917972637495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16917318540289945315091663 25375977810434917972637495)
  ·
    refine ⟨38063966715652376958956243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25375977810434917972637495 38063966715652376958956243)
    ·
      refine ⟨57095950073478565438434365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38063966715652376958956243 57095950073478565438434365)
      ·
        refine ⟨21410981277554462039412887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57095950073478565438434365 21410981277554462039412887)
        ·
          refine ⟨32116471916331693059119331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21410981277554462039412887 32116471916331693059119331)
          ·
            refine ⟨48174707874497539588678997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32116471916331693059119331 48174707874497539588678997)
            ·
              refine ⟨35284209869016752628427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 48174707874497539588678997 35284209869016752628427)
              ·
                rfl

theorem cell20_695747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 12].length) (baseStart_695747 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_695747 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_695747 prefixEnd_695747 := by exact prefixLift 695747
  have htrace : WordTrace (prefixWord ++ tailWord_695747) baseStart_695747 baseEnd_695747 := by
    simpa [prefixWord, tailWord_695747, baseEnd_695747] using wordTrace_append hprefix tailTrace_695747
  have hstable : (prefixWord ++ tailWord_695747).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695747).length < 2 ^ (prefixWord ++ tailWord_695747).sum := by decide
  have hdescent : baseEnd_695747 < baseStart_695747 := by decide
  rcases family_descends (prefixWord ++ tailWord_695747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695819 : List Nat := [1, 1, 1, 1, 8, 2, 1, 5]
def baseStart_695819 : Nat := 118140960795 + 695819 * 2 ^ 59
def prefixEnd_695819 : Nat := 4983230072969 + 3 ^ 40 * 695819 * 2
def baseEnd_695819 : Nat := 105863583861012841085183

theorem tailTrace_695819 : CollatzResearch.WordTrace tailWord_695819 prefixEnd_695819 105863583861012841085183 := by
  unfold tailWord_695819
  simp only [CollatzResearch.WordTrace]
  refine ⟨25378603866174074269258511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16919069244116049512839007 25378603866174074269258511)
  ·
    refine ⟨38067905799261111403887767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25378603866174074269258511 38067905799261111403887767)
    ·
      refine ⟨57101858698891667105831651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38067905799261111403887767 57101858698891667105831651)
      ·
        refine ⟨85652788048337500658747477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57101858698891667105831651 85652788048337500658747477)
        ·
          refine ⟨1003743609941455085844697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 85652788048337500658747477 1003743609941455085844697)
          ·
            refine ⟨752807707456091314383523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1003743609941455085844697 752807707456091314383523)
            ·
              refine ⟨1129211561184136971575285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 752807707456091314383523 1129211561184136971575285)
              ·
                refine ⟨105863583861012841085183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1129211561184136971575285 105863583861012841085183)
                ·
                  rfl

theorem cell20_695819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 1, 5].length) (baseStart_695819 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_695819 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_695819 prefixEnd_695819 := by exact prefixLift 695819
  have htrace : WordTrace (prefixWord ++ tailWord_695819) baseStart_695819 baseEnd_695819 := by
    simpa [prefixWord, tailWord_695819, baseEnd_695819] using wordTrace_append hprefix tailTrace_695819
  have hstable : (prefixWord ++ tailWord_695819).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695819).length < 2 ^ (prefixWord ++ tailWord_695819).sum := by decide
  have hdescent : baseEnd_695819 < baseStart_695819 := by decide
  rcases family_descends (prefixWord ++ tailWord_695819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695864 : List Nat := [2, 1, 2, 1, 4, 2, 3, 2, 3]
def baseStart_695864 : Nat := 118140960795 + 695864 * 2 ^ 59
def prefixEnd_695864 : Nat := 4983230072969 + 3 ^ 40 * 695864 * 2
def baseEnd_695864 : Nat := 317611290809218366755365

theorem tailTrace_695864 : CollatzResearch.WordTrace tailWord_695864 prefixEnd_695864 317611290809218366755365 := by
  unfold tailWord_695864
  simp only [CollatzResearch.WordTrace]
  refine ⟨12690122575505523477323323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16920163434007364636431097 12690122575505523477323323)
  ·
    refine ⟨19035183863258285215984985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12690122575505523477323323 19035183863258285215984985)
    ·
      refine ⟨14276387897443713911988739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19035183863258285215984985 14276387897443713911988739)
      ·
        refine ⟨21414581846165570867983109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14276387897443713911988739 21414581846165570867983109)
        ·
          refine ⟨4015234096156044537746833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21414581846165570867983109 4015234096156044537746833)
          ·
            refine ⟨3011425572117033403310125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4015234096156044537746833 3011425572117033403310125)
            ·
              refine ⟨1129284589543887526241297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3011425572117033403310125 1129284589543887526241297)
              ·
                refine ⟨846963442157915644680973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1129284589543887526241297 846963442157915644680973)
                ·
                  refine ⟨317611290809218366755365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 846963442157915644680973 317611290809218366755365)
                  ·
                    rfl

theorem cell20_695864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 3, 2, 3].length) (baseStart_695864 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_695864 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_695864 prefixEnd_695864 := by exact prefixLift 695864
  have htrace : WordTrace (prefixWord ++ tailWord_695864) baseStart_695864 baseEnd_695864 := by
    simpa [prefixWord, tailWord_695864, baseEnd_695864] using wordTrace_append hprefix tailTrace_695864
  have hstable : (prefixWord ++ tailWord_695864).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695864).length < 2 ^ (prefixWord ++ tailWord_695864).sum := by decide
  have hdescent : baseEnd_695864 < baseStart_695864 := by decide
  rcases family_descends (prefixWord ++ tailWord_695864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695871 : List Nat := [1, 1, 2, 2, 3, 4, 2, 1, 4]
def baseStart_695871 : Nat := 118140960795 + 695871 * 2 ^ 59
def prefixEnd_695871 : Nat := 4983230072969 + 3 ^ 40 * 695871 * 2
def baseEnd_695871 : Nat := 317614485799957453522003

theorem tailTrace_695871 : CollatzResearch.WordTrace tailWord_695871 prefixEnd_695871 317614485799957453522003 := by
  unfold tailWord_695871
  simp only [CollatzResearch.WordTrace]
  refine ⟨25380500461985687150151467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16920333641323791433434311 25380500461985687150151467)
  ·
    refine ⟨38070750692978530725227201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25380500461985687150151467 38070750692978530725227201)
    ·
      refine ⟨28553063019733898043920401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38070750692978530725227201 28553063019733898043920401)
      ·
        refine ⟨21414797264800423532940301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28553063019733898043920401 21414797264800423532940301)
        ·
          refine ⟨8030548974300158824852613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21414797264800423532940301 8030548974300158824852613)
          ·
            refine ⟨1505727932681279779659865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8030548974300158824852613 1505727932681279779659865)
            ·
              refine ⟨1129295949510959834744899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1505727932681279779659865 1129295949510959834744899)
              ·
                refine ⟨1693943924266439752117349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1129295949510959834744899 1693943924266439752117349)
                ·
                  refine ⟨317614485799957453522003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1693943924266439752117349 317614485799957453522003)
                  ·
                    rfl

theorem cell20_695871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 2, 1, 4].length) (baseStart_695871 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_695871 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_695871 prefixEnd_695871 := by exact prefixLift 695871
  have htrace : WordTrace (prefixWord ++ tailWord_695871) baseStart_695871 baseEnd_695871 := by
    simpa [prefixWord, tailWord_695871, baseEnd_695871] using wordTrace_append hprefix tailTrace_695871
  have hstable : (prefixWord ++ tailWord_695871).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695871).length < 2 ^ (prefixWord ++ tailWord_695871).sum := by decide
  have hdescent : baseEnd_695871 < baseStart_695871 := by decide
  rcases family_descends (prefixWord ++ tailWord_695871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695895 : List Nat := [1, 1, 3, 2, 2, 5, 2, 4]
def baseStart_695895 : Nat := 118140960795 + 695895 * 2 ^ 59
def prefixEnd_695895 : Nat := 4983230072969 + 3 ^ 40 * 695895 * 2
def baseEnd_695895 : Nat := 105875146684640012240635

theorem tailTrace_695895 : CollatzResearch.WordTrace tailWord_695895 prefixEnd_695895 105875146684640012240635 := by
  unfold tailWord_695895
  simp only [CollatzResearch.WordTrace]
  refine ⟨25381375813898739249025139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16920917209265826166016759 25381375813898739249025139)
  ·
    refine ⟨38072063720848108873537709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25381375813898739249025139 38072063720848108873537709)
    ·
      refine ⟨14277023895318040827576641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38072063720848108873537709 14277023895318040827576641)
      ·
        refine ⟨10707767921488530620682481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14277023895318040827576641 10707767921488530620682481)
        ·
          refine ⟨8030825941116397965511861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10707767921488530620682481 8030825941116397965511861)
          ·
            refine ⟨752889931979662309266737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8030825941116397965511861 752889931979662309266737)
            ·
              refine ⟨564667448984746731950053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 752889931979662309266737 564667448984746731950053)
              ·
                refine ⟨105875146684640012240635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 564667448984746731950053 105875146684640012240635)
                ·
                  rfl

theorem cell20_695895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 2, 4].length) (baseStart_695895 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_695895 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_695895 prefixEnd_695895 := by exact prefixLift 695895
  have htrace : WordTrace (prefixWord ++ tailWord_695895) baseStart_695895 baseEnd_695895 := by
    simpa [prefixWord, tailWord_695895, baseEnd_695895] using wordTrace_append hprefix tailTrace_695895
  have hstable : (prefixWord ++ tailWord_695895).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695895).length < 2 ^ (prefixWord ++ tailWord_695895).sum := by decide
  have hdescent : baseEnd_695895 < baseStart_695895 := by decide
  rcases family_descends (prefixWord ++ tailWord_695895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695901 : List Nat := [1, 4, 4, 2, 1, 2, 1, 3, 2]
def baseStart_695901 : Nat := 118140960795 + 695901 * 2 ^ 59
def prefixEnd_695901 : Nat := 4983230072969 + 3 ^ 40 * 695901 * 2
def baseEnd_695901 : Nat := 317628178617410682521881

theorem tailTrace_695901 : CollatzResearch.WordTrace tailWord_695901 prefixEnd_695901 317628178617410682521881 := by
  unfold tailWord_695901
  simp only [CollatzResearch.WordTrace]
  refine ⟨25381594651877002273743557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16921063101251334849162371 25381594651877002273743557)
  ·
    refine ⟨4759048997226937926326917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25381594651877002273743557 4759048997226937926326917)
    ·
      refine ⟨892321686980050861186297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4759048997226937926326917 892321686980050861186297)
      ·
        refine ⟨669241265235038145889723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 892321686980050861186297 669241265235038145889723)
        ·
          refine ⟨1003861897852557218834585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 669241265235038145889723 1003861897852557218834585)
          ·
            refine ⟨752896423389417914125939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1003861897852557218834585 752896423389417914125939)
            ·
              refine ⟨1129344635084126871188909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 752896423389417914125939 1129344635084126871188909)
              ·
                refine ⟨423504238156547576695841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1129344635084126871188909 423504238156547576695841)
                ·
                  refine ⟨317628178617410682521881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 423504238156547576695841 317628178617410682521881)
                  ·
                    rfl

theorem cell20_695901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 1, 3, 2].length) (baseStart_695901 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_695901 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_695901 prefixEnd_695901 := by exact prefixLift 695901
  have htrace : WordTrace (prefixWord ++ tailWord_695901) baseStart_695901 baseEnd_695901 := by
    simpa [prefixWord, tailWord_695901, baseEnd_695901] using wordTrace_append hprefix tailTrace_695901
  have hstable : (prefixWord ++ tailWord_695901).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695901).length < 2 ^ (prefixWord ++ tailWord_695901).sum := by decide
  have hdescent : baseEnd_695901 < baseStart_695901 := by decide
  rcases family_descends (prefixWord ++ tailWord_695901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695926 : List Nat := [5, 1, 1, 2, 2, 1, 3, 1, 4]
def baseStart_695926 : Nat := 118140960795 + 695926 * 2 ^ 59
def prefixEnd_695926 : Nat := 4983230072969 + 3 ^ 40 * 695926 * 2
def baseEnd_695926 : Nat := 317639589298621706688445

theorem tailTrace_695926 : CollatzResearch.WordTrace tailWord_695926 prefixEnd_695926 317639589298621706688445 := by
  unfold tailWord_695926
  simp only [CollatzResearch.WordTrace]
  refine ⟨1586406654799151971462727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16921670984524287695602421 1586406654799151971462727)
  ·
    refine ⟨2379609982198727957194091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1586406654799151971462727 2379609982198727957194091)
    ·
      refine ⟨3569414973298091935791137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2379609982198727957194091 3569414973298091935791137)
      ·
        refine ⟨2677061229973568951843353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3569414973298091935791137 2677061229973568951843353)
        ·
          refine ⟨2007795922480176713882515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2677061229973568951843353 2007795922480176713882515)
          ·
            refine ⟨3011693883720265070823773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2007795922480176713882515 3011693883720265070823773)
            ·
              refine ⟨1129385206395099401558915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3011693883720265070823773 1129385206395099401558915)
              ·
                refine ⟨1694077809592649102338373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1129385206395099401558915 1694077809592649102338373)
                ·
                  refine ⟨317639589298621706688445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1694077809592649102338373 317639589298621706688445)
                  ·
                    rfl

theorem cell20_695926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_695926 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_695926 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_695926 prefixEnd_695926 := by exact prefixLift 695926
  have htrace : WordTrace (prefixWord ++ tailWord_695926) baseStart_695926 baseEnd_695926 := by
    simpa [prefixWord, tailWord_695926, baseEnd_695926] using wordTrace_append hprefix tailTrace_695926
  have hstable : (prefixWord ++ tailWord_695926).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695926).length < 2 ^ (prefixWord ++ tailWord_695926).sum := by decide
  have hdescent : baseEnd_695926 < baseStart_695926 := by decide
  rcases family_descends (prefixWord ++ tailWord_695926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695930 : List Nat := [3, 1, 1, 1, 1, 1, 1, 7, 4]
def baseStart_695930 : Nat := 118140960795 + 695930 * 2 ^ 59
def prefixEnd_695930 : Nat := 4983230072969 + 3 ^ 40 * 695930 * 2
def baseEnd_695930 : Nat := 317641415007615470555095

theorem tailTrace_695930 : CollatzResearch.WordTrace tailWord_695930 prefixEnd_695930 317641415007615470555095 := by
  unfold tailWord_695930
  simp only [CollatzResearch.WordTrace]
  refine ⟨6345663092192985056637311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16921768245847960151032829 6345663092192985056637311)
  ·
    refine ⟨9518494638289477584955967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6345663092192985056637311 9518494638289477584955967)
    ·
      refine ⟨14277741957434216377433951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9518494638289477584955967 14277741957434216377433951)
      ·
        refine ⟨21416612936151324566150927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14277741957434216377433951 21416612936151324566150927)
        ·
          refine ⟨32124919404226986849226391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21416612936151324566150927 32124919404226986849226391)
          ·
            refine ⟨48187379106340480273839587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32124919404226986849226391 48187379106340480273839587)
            ·
              refine ⟨72281068659510720410759381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48187379106340480273839587 72281068659510720410759381)
              ·
                refine ⟨1694087546707282509627173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 72281068659510720410759381 1694087546707282509627173)
                ·
                  refine ⟨317641415007615470555095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1694087546707282509627173 317641415007615470555095)
                  ·
                    rfl

theorem cell20_695930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 7, 4].length) (baseStart_695930 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_695930 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_695930 prefixEnd_695930 := by exact prefixLift 695930
  have htrace : WordTrace (prefixWord ++ tailWord_695930) baseStart_695930 baseEnd_695930 := by
    simpa [prefixWord, tailWord_695930, baseEnd_695930] using wordTrace_append hprefix tailTrace_695930
  have hstable : (prefixWord ++ tailWord_695930).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695930).length < 2 ^ (prefixWord ++ tailWord_695930).sum := by decide
  have hdescent : baseEnd_695930 < baseStart_695930 := by decide
  rcases family_descends (prefixWord ++ tailWord_695930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695975 : List Nat := [1, 1, 6, 12]
def baseStart_695975 : Nat := 118140960795 + 695975 * 2 ^ 59
def prefixEnd_695975 : Nat := 4983230072969 + 3 ^ 40 * 695975 * 2
def baseEnd_695975 : Nat := 1307250840468293473477

theorem tailTrace_695975 : CollatzResearch.WordTrace tailWord_695975 prefixEnd_695975 1307250840468293473477 := by
  unfold tailWord_695975
  simp only [CollatzResearch.WordTrace]
  refine ⟨25384293653608912911937379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16922862435739275274624919 25384293653608912911937379)
  ·
    refine ⟨38076440480413369367906069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25384293653608912911937379 38076440480413369367906069)
    ·
      refine ⟨1784833147519376689120597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 38076440480413369367906069 1784833147519376689120597)
      ·
        refine ⟨1307250840468293473477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 12 1784833147519376689120597 1307250840468293473477)
        ·
          rfl

theorem cell20_695975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 12].length) (baseStart_695975 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_695975 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_695975 prefixEnd_695975 := by exact prefixLift 695975
  have htrace : WordTrace (prefixWord ++ tailWord_695975) baseStart_695975 baseEnd_695975 := by
    simpa [prefixWord, tailWord_695975, baseEnd_695975] using wordTrace_append hprefix tailTrace_695975
  have hstable : (prefixWord ++ tailWord_695975).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695975).length < 2 ^ (prefixWord ++ tailWord_695975).sum := by decide
  have hdescent : baseEnd_695975 < baseStart_695975 := by decide
  rcases family_descends (prefixWord ++ tailWord_695975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_695999 : List Nat := [1, 1, 2, 2, 2, 3, 1, 5, 3]
def baseStart_695999 : Nat := 118140960795 + 695999 * 2 ^ 59
def prefixEnd_695999 : Nat := 4983230072969 + 3 ^ 40 * 695999 * 2
def baseEnd_695999 : Nat := 317672908487757897254813

theorem tailTrace_695999 : CollatzResearch.WordTrace tailWord_695999 prefixEnd_695999 317672908487757897254813 := by
  unfold tailWord_695999
  simp only [CollatzResearch.WordTrace]
  refine ⟨25385169005521965010811051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16923446003681310007207367 25385169005521965010811051)
  ·
    refine ⟨38077753508282947516216577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25385169005521965010811051 38077753508282947516216577)
    ·
      refine ⟨28558315131212210637162433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38077753508282947516216577 28558315131212210637162433)
      ·
        refine ⟨21418736348409157977871825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28558315131212210637162433 21418736348409157977871825)
        ·
          refine ⟨16064052261306868483403869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21418736348409157977871825 16064052261306868483403869)
          ·
            refine ⟨6024019597990075681276451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16064052261306868483403869 6024019597990075681276451)
            ·
              refine ⟨9036029396985113521914677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6024019597990075681276451 9036029396985113521914677)
              ·
                refine ⟨847127755967354392679501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9036029396985113521914677 847127755967354392679501)
                ·
                  refine ⟨317672908487757897254813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 847127755967354392679501 317672908487757897254813)
                  ·
                    rfl

theorem cell20_695999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 5, 3].length) (baseStart_695999 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_695999 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_695999 prefixEnd_695999 := by exact prefixLift 695999
  have htrace : WordTrace (prefixWord ++ tailWord_695999) baseStart_695999 baseEnd_695999 := by
    simpa [prefixWord, tailWord_695999, baseEnd_695999] using wordTrace_append hprefix tailTrace_695999
  have hstable : (prefixWord ++ tailWord_695999).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_695999).length < 2 ^ (prefixWord ++ tailWord_695999).sum := by decide
  have hdescent : baseEnd_695999 < baseStart_695999 := by decide
  rcases family_descends (prefixWord ++ tailWord_695999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696029 : List Nat := [1, 4, 3, 3, 2, 1, 1, 2, 3]
def baseStart_696029 : Nat := 118140960795 + 696029 * 2 ^ 59
def prefixEnd_696029 : Nat := 4983230072969 + 3 ^ 40 * 696029 * 2
def baseEnd_696029 : Nat := 317686601305211126254691

theorem tailTrace_696029 : CollatzResearch.WordTrace tailWord_696029 prefixEnd_696029 317686601305211126254691 := by
  unfold tailWord_696029
  simp only [CollatzResearch.WordTrace]
  refine ⟨25386263195413280134403141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16924175463608853422935427 25386263195413280134403141)
  ·
    refine ⟨4759924349139990025200589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25386263195413280134403141 4759924349139990025200589)
    ·
      refine ⟨1784971630927496259450221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4759924349139990025200589 1784971630927496259450221)
      ·
        refine ⟨669364361597811097293833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1784971630927496259450221 669364361597811097293833)
        ·
          refine ⟨502023271198358322970375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 669364361597811097293833 502023271198358322970375)
          ·
            refine ⟨753034906797537484455563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 502023271198358322970375 753034906797537484455563)
            ·
              refine ⟨1129552360196306226683345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 753034906797537484455563 1129552360196306226683345)
              ·
                refine ⟨847164270147229670012509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1129552360196306226683345 847164270147229670012509)
                ·
                  refine ⟨317686601305211126254691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 847164270147229670012509 317686601305211126254691)
                  ·
                    rfl

theorem cell20_696029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 1, 2, 3].length) (baseStart_696029 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_696029 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_696029 prefixEnd_696029 := by exact prefixLift 696029
  have htrace : WordTrace (prefixWord ++ tailWord_696029) baseStart_696029 baseEnd_696029 := by
    simpa [prefixWord, tailWord_696029, baseEnd_696029] using wordTrace_append hprefix tailTrace_696029
  have hstable : (prefixWord ++ tailWord_696029).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696029).length < 2 ^ (prefixWord ++ tailWord_696029).sum := by decide
  have hdescent : baseEnd_696029 < baseStart_696029 := by decide
  rcases family_descends (prefixWord ++ tailWord_696029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696033 : List Nat := [1, 2, 3, 1, 5, 2, 1, 2, 3]
def baseStart_696033 : Nat := 118140960795 + 696033 * 2 ^ 59
def prefixEnd_696033 : Nat := 4983230072969 + 3 ^ 40 * 696033 * 2
def baseEnd_696033 : Nat := 317688427014204890121341

theorem tailTrace_696033 : CollatzResearch.WordTrace tailWord_696033 prefixEnd_696033 317688427014204890121341 := by
  unfold tailWord_696033
  simp only [CollatzResearch.WordTrace]
  refine ⟨25386409087398788817548753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16924272724932525878365835 25386409087398788817548753)
  ·
    refine ⟨19039806815549091613161565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25386409087398788817548753 19039806815549091613161565)
    ·
      refine ⟨7139927555830909354935587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19039806815549091613161565 7139927555830909354935587)
      ·
        refine ⟨10709891333746364032403381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7139927555830909354935587 10709891333746364032403381)
        ·
          refine ⟨1004052312538721628037817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10709891333746364032403381 1004052312538721628037817)
          ·
            refine ⟨753039234404041221028363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1004052312538721628037817 753039234404041221028363)
            ·
              refine ⟨1129558851606061831542545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 753039234404041221028363 1129558851606061831542545)
              ·
                refine ⟨847169138704546373656909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1129558851606061831542545 847169138704546373656909)
                ·
                  refine ⟨317688427014204890121341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 847169138704546373656909 317688427014204890121341)
                  ·
                    rfl

theorem cell20_696033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 1, 2, 3].length) (baseStart_696033 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_696033 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_696033 prefixEnd_696033 := by exact prefixLift 696033
  have htrace : WordTrace (prefixWord ++ tailWord_696033) baseStart_696033 baseEnd_696033 := by
    simpa [prefixWord, tailWord_696033, baseEnd_696033] using wordTrace_append hprefix tailTrace_696033
  have hstable : (prefixWord ++ tailWord_696033).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696033).length < 2 ^ (prefixWord ++ tailWord_696033).sum := by decide
  have hdescent : baseEnd_696033 < baseStart_696033 := by decide
  rcases family_descends (prefixWord ++ tailWord_696033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696037 : List Nat := [1, 3, 1, 4, 1, 1, 3, 1, 5]
def baseStart_696037 : Nat := 118140960795 + 696037 * 2 ^ 59
def prefixEnd_696037 : Nat := 4983230072969 + 3 ^ 40 * 696037 * 2
def baseEnd_696037 : Nat := 317690252723198653987991

theorem tailTrace_696037 : CollatzResearch.WordTrace tailWord_696037 prefixEnd_696037 317690252723198653987991 := by
  unfold tailWord_696037
  simp only [CollatzResearch.WordTrace]
  refine ⟨25386554979384297500694365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16924369986256198333796243 25386554979384297500694365)
  ·
    refine ⟨9519958117269111562760387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25386554979384297500694365 9519958117269111562760387)
    ·
      refine ⟨14279937175903667344140581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9519958117269111562760387 14279937175903667344140581)
      ·
        refine ⟨2677488220481937627026359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14279937175903667344140581 2677488220481937627026359)
        ·
          refine ⟨4016232330722906440539539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2677488220481937627026359 4016232330722906440539539)
          ·
            refine ⟨6024348496084359660809309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4016232330722906440539539 6024348496084359660809309)
            ·
              refine ⟨2259130686031634872803491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6024348496084359660809309 2259130686031634872803491)
              ·
                refine ⟨3388696029047452309205237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2259130686031634872803491 3388696029047452309205237)
                ·
                  refine ⟨317690252723198653987991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3388696029047452309205237 317690252723198653987991)
                  ·
                    rfl

theorem cell20_696037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 1, 5].length) (baseStart_696037 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_696037 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_696037 prefixEnd_696037 := by exact prefixLift 696037
  have htrace : WordTrace (prefixWord ++ tailWord_696037) baseStart_696037 baseEnd_696037 := by
    simpa [prefixWord, tailWord_696037, baseEnd_696037] using wordTrace_append hprefix tailTrace_696037
  have hstable : (prefixWord ++ tailWord_696037).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696037).length < 2 ^ (prefixWord ++ tailWord_696037).sum := by decide
  have hdescent : baseEnd_696037 < baseStart_696037 := by decide
  rcases family_descends (prefixWord ++ tailWord_696037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696040 : List Nat := [2, 1, 4, 1, 3, 1, 2, 4, 2]
def baseStart_696040 : Nat := 118140960795 + 696040 * 2 ^ 59
def prefixEnd_696040 : Nat := 4983230072969 + 3 ^ 40 * 696040 * 2
def baseEnd_696040 : Nat := 317691622004943976887979

theorem tailTrace_696040 : CollatzResearch.WordTrace tailWord_696040 prefixEnd_696040 317691622004943976887979 := by
  unfold tailWord_696040
  simp only [CollatzResearch.WordTrace]
  refine ⟨12693332199186714506526787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16924442932248952675369049 12693332199186714506526787)
  ·
    refine ⟨19039998298780071759790181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12693332199186714506526787 19039998298780071759790181)
    ·
      refine ⟨3569999681021263454960659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19039998298780071759790181 3569999681021263454960659)
      ·
        refine ⟨5354999521531895182440989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3569999681021263454960659 5354999521531895182440989)
        ·
          refine ⟨2008124820574460693415371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5354999521531895182440989 2008124820574460693415371)
          ·
            refine ⟨3012187230861691040123057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2008124820574460693415371 3012187230861691040123057)
            ·
              refine ⟨2259140423146268280092293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3012187230861691040123057 2259140423146268280092293)
              ·
                refine ⟨423588829339925302517305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2259140423146268280092293 423588829339925302517305)
                ·
                  refine ⟨317691622004943976887979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 423588829339925302517305 317691622004943976887979)
                  ·
                    rfl

theorem cell20_696040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 4, 2].length) (baseStart_696040 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_696040 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_696040 prefixEnd_696040 := by exact prefixLift 696040
  have htrace : WordTrace (prefixWord ++ tailWord_696040) baseStart_696040 baseEnd_696040 := by
    simpa [prefixWord, tailWord_696040, baseEnd_696040] using wordTrace_append hprefix tailTrace_696040
  have hstable : (prefixWord ++ tailWord_696040).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696040).length < 2 ^ (prefixWord ++ tailWord_696040).sum := by decide
  have hdescent : baseEnd_696040 < baseStart_696040 := by decide
  rcases family_descends (prefixWord ++ tailWord_696040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696044 : List Nat := [2, 2, 1, 1, 2, 2, 3, 3, 4]
def baseStart_696044 : Nat := 118140960795 + 696044 * 2 ^ 59
def prefixEnd_696044 : Nat := 4983230072969 + 3 ^ 40 * 696044 * 2
def baseEnd_696044 : Nat := 317693447713937740754629

theorem tailTrace_696044 : CollatzResearch.WordTrace tailWord_696044 prefixEnd_696044 317693447713937740754629 := by
  unfold tailWord_696044
  simp only [CollatzResearch.WordTrace]
  refine ⟨12693405145179468848099593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16924540193572625130799457 12693405145179468848099593)
  ·
    refine ⟨9520053858884601636074695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12693405145179468848099593 9520053858884601636074695)
    ·
      refine ⟨14280080788326902454112043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9520053858884601636074695 14280080788326902454112043)
      ·
        refine ⟨21420121182490353681168065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14280080788326902454112043 21420121182490353681168065)
        ·
          refine ⟨16065090886867765260876049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21420121182490353681168065 16065090886867765260876049)
          ·
            refine ⟨12048818165150823945657037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16065090886867765260876049 12048818165150823945657037)
            ·
              refine ⟨4518306811931558979621389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12048818165150823945657037 4518306811931558979621389)
              ·
                refine ⟨1694365054474334617358021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4518306811931558979621389 1694365054474334617358021)
                ·
                  refine ⟨317693447713937740754629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1694365054474334617358021 317693447713937740754629)
                  ·
                    rfl

theorem cell20_696044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 4].length) (baseStart_696044 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_696044 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_696044 prefixEnd_696044 := by exact prefixLift 696044
  have htrace : WordTrace (prefixWord ++ tailWord_696044) baseStart_696044 baseEnd_696044 := by
    simpa [prefixWord, tailWord_696044, baseEnd_696044] using wordTrace_append hprefix tailTrace_696044
  have hstable : (prefixWord ++ tailWord_696044).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696044).length < 2 ^ (prefixWord ++ tailWord_696044).sum := by decide
  have hdescent : baseEnd_696044 < baseStart_696044 := by decide
  rcases family_descends (prefixWord ++ tailWord_696044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696068 : List Nat := [2, 3, 2, 2, 1, 3, 1, 6]
def baseStart_696068 : Nat := 118140960795 + 696068 * 2 ^ 59
def prefixEnd_696068 : Nat := 4983230072969 + 3 ^ 40 * 696068 * 2
def baseEnd_696068 : Nat := 105901467322633441318177

theorem tailTrace_696068 : CollatzResearch.WordTrace tailWord_696068 prefixEnd_696068 105901467322633441318177 := by
  unfold tailWord_696068
  simp only [CollatzResearch.WordTrace]
  refine ⟨12693842821135994897536429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16925123761514659863381905 12693842821135994897536429)
  ·
    refine ⟨4760191057925998086576161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12693842821135994897536429 4760191057925998086576161)
    ·
      refine ⟨3570143293444498564932121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4760191057925998086576161 3570143293444498564932121)
      ·
        refine ⟨2677607470083373923699091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3570143293444498564932121 2677607470083373923699091)
        ·
          refine ⟨4016411205125060885548637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2677607470083373923699091 4016411205125060885548637)
          ·
            refine ⟨1506154201921897832080739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4016411205125060885548637 1506154201921897832080739)
            ·
              refine ⟨2259231302882846748121109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1506154201921897832080739 2259231302882846748121109)
              ·
                refine ⟨105901467322633441318177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2259231302882846748121109 105901467322633441318177)
                ·
                  rfl

theorem cell20_696068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 6].length) (baseStart_696068 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_696068 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_696068 prefixEnd_696068 := by exact prefixLift 696068
  have htrace : WordTrace (prefixWord ++ tailWord_696068) baseStart_696068 baseEnd_696068 := by
    simpa [prefixWord, tailWord_696068, baseEnd_696068] using wordTrace_append hprefix tailTrace_696068
  have hstable : (prefixWord ++ tailWord_696068).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696068).length < 2 ^ (prefixWord ++ tailWord_696068).sum := by decide
  have hdescent : baseEnd_696068 < baseStart_696068 := by decide
  rcases family_descends (prefixWord ++ tailWord_696068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696078 : List Nat := [4, 1, 1, 2, 1, 1, 5, 3, 2]
def baseStart_696078 : Nat := 118140960795 + 696078 * 2 ^ 59
def prefixEnd_696078 : Nat := 4983230072969 + 3 ^ 40 * 696078 * 2
def baseEnd_696078 : Nat := 317708966240384733621157

theorem tailTrace_696078 : CollatzResearch.WordTrace tailWord_696078 prefixEnd_696078 317708966240384733621157 := by
  unfold tailWord_696078
  simp only [CollatzResearch.WordTrace]
  refine ⟨3173506296529470187867111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16925366914823841001957925 3173506296529470187867111)
  ·
    refine ⟨4760259444794205281800667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3173506296529470187867111 4760259444794205281800667)
    ·
      refine ⟨7140389167191307922701001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4760259444794205281800667 7140389167191307922701001)
      ·
        refine ⟨5355291875393480942025751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7140389167191307922701001 5355291875393480942025751)
        ·
          refine ⟨8032937813090221413038627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5355291875393480942025751 8032937813090221413038627)
          ·
            refine ⟨12049406719635332119557941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8032937813090221413038627 12049406719635332119557941)
            ·
              refine ⟨1129631879965812386208557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12049406719635332119557941 1129631879965812386208557)
              ·
                refine ⟨423611954987179644828209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1129631879965812386208557 423611954987179644828209)
                ·
                  refine ⟨317708966240384733621157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 423611954987179644828209 317708966240384733621157)
                  ·
                    rfl

theorem cell20_696078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 5, 3, 2].length) (baseStart_696078 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_696078 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_696078 prefixEnd_696078 := by exact prefixLift 696078
  have htrace : WordTrace (prefixWord ++ tailWord_696078) baseStart_696078 baseEnd_696078 := by
    simpa [prefixWord, tailWord_696078, baseEnd_696078] using wordTrace_append hprefix tailTrace_696078
  have hstable : (prefixWord ++ tailWord_696078).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696078).length < 2 ^ (prefixWord ++ tailWord_696078).sum := by decide
  have hdescent : baseEnd_696078 < baseStart_696078 := by decide
  rcases family_descends (prefixWord ++ tailWord_696078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696099 : List Nat := [1, 1, 1, 4, 2, 1, 2, 6, 2]
def baseStart_696099 : Nat := 118140960795 + 696099 * 2 ^ 59
def prefixEnd_696099 : Nat := 4983230072969 + 3 ^ 40 * 696099 * 2
def baseEnd_696099 : Nat := 317718551212601993921071

theorem tailTrace_696099 : CollatzResearch.WordTrace tailWord_696099 prefixEnd_696099 317718551212601993921071 := by
  unfold tailWord_696099
  simp only [CollatzResearch.WordTrace]
  refine ⟨25388816305159682089451351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16925877536773121392967567 25388816305159682089451351)
  ·
    refine ⟨38083224457739523134177027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25388816305159682089451351 38083224457739523134177027)
    ·
      refine ⟨57124836686609284701265541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38083224457739523134177027 57124836686609284701265541)
      ·
        refine ⟨10710906878739240881487289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57124836686609284701265541 10710906878739240881487289)
        ·
          refine ⟨8033180159054430661115467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10710906878739240881487289 8033180159054430661115467)
          ·
            refine ⟨12049770238581645991673201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8033180159054430661115467 12049770238581645991673201)
            ·
              refine ⟨9037327678936234493754901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12049770238581645991673201 9037327678936234493754901)
              ·
                refine ⟨423624734950135991894761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9037327678936234493754901 423624734950135991894761)
                ·
                  refine ⟨317718551212601993921071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 423624734950135991894761 317718551212601993921071)
                  ·
                    rfl

theorem cell20_696099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 6, 2].length) (baseStart_696099 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_696099 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_696099 prefixEnd_696099 := by exact prefixLift 696099
  have htrace : WordTrace (prefixWord ++ tailWord_696099) baseStart_696099 baseEnd_696099 := by
    simpa [prefixWord, tailWord_696099, baseEnd_696099] using wordTrace_append hprefix tailTrace_696099
  have hstable : (prefixWord ++ tailWord_696099).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696099).length < 2 ^ (prefixWord ++ tailWord_696099).sum := by decide
  have hdescent : baseEnd_696099 < baseStart_696099 := by decide
  rcases family_descends (prefixWord ++ tailWord_696099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696137 : List Nat := [1, 2, 1, 1, 2, 4, 2, 5, 2]
def baseStart_696137 : Nat := 118140960795 + 696137 * 2 ^ 59
def prefixEnd_696137 : Nat := 4983230072969 + 3 ^ 40 * 696137 * 2
def baseEnd_696137 : Nat := 317735895448042750654249

theorem tailTrace_696137 : CollatzResearch.WordTrace tailWord_696137 prefixEnd_696137 317735895448042750654249 := by
  unfold tailWord_696137
  simp only [CollatzResearch.WordTrace]
  refine ⟨25390202279022014579334665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16926801519348009719556443 25390202279022014579334665)
  ·
    refine ⟨19042651709266510934500999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25390202279022014579334665 19042651709266510934500999)
    ·
      refine ⟨28563977563899766401751499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19042651709266510934500999 28563977563899766401751499)
      ·
        refine ⟨42845966345849649602627249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28563977563899766401751499 42845966345849649602627249)
        ·
          refine ⟨32134474759387237201970437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42845966345849649602627249 32134474759387237201970437)
          ·
            refine ⟨6025214017385106975369457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32134474759387237201970437 6025214017385106975369457)
            ·
              refine ⟨4518910513038830231527093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6025214017385106975369457 4518910513038830231527093)
              ·
                refine ⟨423647860597390334205665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4518910513038830231527093 423647860597390334205665)
                ·
                  refine ⟨317735895448042750654249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 423647860597390334205665 317735895448042750654249)
                  ·
                    rfl

theorem cell20_696137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 5, 2].length) (baseStart_696137 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_696137 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_696137 prefixEnd_696137 := by exact prefixLift 696137
  have htrace : WordTrace (prefixWord ++ tailWord_696137) baseStart_696137 baseEnd_696137 := by
    simpa [prefixWord, tailWord_696137, baseEnd_696137] using wordTrace_append hprefix tailTrace_696137
  have hstable : (prefixWord ++ tailWord_696137).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696137).length < 2 ^ (prefixWord ++ tailWord_696137).sum := by decide
  have hdescent : baseEnd_696137 < baseStart_696137 := by decide
  rcases family_descends (prefixWord ++ tailWord_696137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696202 : List Nat := [3, 1, 2, 4, 3, 1, 1, 2, 3]
def baseStart_696202 : Nat := 118140960795 + 696202 * 2 ^ 59
def prefixEnd_696202 : Nat := 4983230072969 + 3 ^ 40 * 696202 * 2
def baseEnd_696202 : Nat := 317765563219191413487317

theorem tailTrace_696202 : CollatzResearch.WordTrace tailWord_696202 prefixEnd_696202 317765563219191413487317 := by
  unfold tailWord_696202
  simp only [CollatzResearch.WordTrace]
  refine ⟨6348143255946632670112715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16928382015857687120300573 6348143255946632670112715)
  ·
    refine ⟨9522214883919949005169073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6348143255946632670112715 9522214883919949005169073)
    ·
      refine ⟨7141661162939961753876805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9522214883919949005169073 7141661162939961753876805)
      ·
        refine ⟨1339061468051242828851901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7141661162939961753876805 1339061468051242828851901)
        ·
          refine ⟨502148050519216060819463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1339061468051242828851901 502148050519216060819463)
          ·
            refine ⟨753222075778824091229195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 502148050519216060819463 753222075778824091229195)
            ·
              refine ⟨1129833113668236136843793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 753222075778824091229195 1129833113668236136843793)
              ·
                refine ⟨847374835251177102632845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1129833113668236136843793 847374835251177102632845)
                ·
                  refine ⟨317765563219191413487317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 847374835251177102632845 317765563219191413487317)
                  ·
                    rfl

theorem cell20_696202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 1, 2, 3].length) (baseStart_696202 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_696202 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_696202 prefixEnd_696202 := by exact prefixLift 696202
  have htrace : WordTrace (prefixWord ++ tailWord_696202) baseStart_696202 baseEnd_696202 := by
    simpa [prefixWord, tailWord_696202, baseEnd_696202] using wordTrace_append hprefix tailTrace_696202
  have hstable : (prefixWord ++ tailWord_696202).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696202).length < 2 ^ (prefixWord ++ tailWord_696202).sum := by decide
  have hdescent : baseEnd_696202 < baseStart_696202 := by decide
  rcases family_descends (prefixWord ++ tailWord_696202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696213 : List Nat := [1, 3, 2, 1, 1, 3, 1, 6, 2]
def baseStart_696213 : Nat := 118140960795 + 696213 * 2 ^ 59
def prefixEnd_696213 : Nat := 4983230072969 + 3 ^ 40 * 696213 * 2
def baseEnd_696213 : Nat := 317770583918924264120605

theorem tailTrace_696213 : CollatzResearch.WordTrace tailWord_696213 prefixEnd_696213 317770583918924264120605 := by
  unfold tailWord_696213
  simp only [CollatzResearch.WordTrace]
  refine ⟨25392974226746679559101293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16928649484497786372734195 25392974226746679559101293)
  ·
    refine ⟨9522365335030004834662985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25392974226746679559101293 9522365335030004834662985)
    ·
      refine ⟨7141774001272503625997239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9522365335030004834662985 7141774001272503625997239)
      ·
        refine ⟨10712661001908755438995859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7141774001272503625997239 10712661001908755438995859)
        ·
          refine ⟨16068991502863133158493789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10712661001908755438995859 16068991502863133158493789)
          ·
            refine ⟨6025871813573674934435171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16068991502863133158493789 6025871813573674934435171)
            ·
              refine ⟨9038807720360512401652757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6025871813573674934435171 9038807720360512401652757)
              ·
                refine ⟨423694111891899018827473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9038807720360512401652757 423694111891899018827473)
                ·
                  refine ⟨317770583918924264120605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 423694111891899018827473 317770583918924264120605)
                  ·
                    rfl

theorem cell20_696213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 6, 2].length) (baseStart_696213 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_696213 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_696213 prefixEnd_696213 := by exact prefixLift 696213
  have htrace : WordTrace (prefixWord ++ tailWord_696213) baseStart_696213 baseEnd_696213 := by
    simpa [prefixWord, tailWord_696213, baseEnd_696213] using wordTrace_append hprefix tailTrace_696213
  have hstable : (prefixWord ++ tailWord_696213).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696213).length < 2 ^ (prefixWord ++ tailWord_696213).sum := by decide
  have hdescent : baseEnd_696213 < baseStart_696213 := by decide
  rcases family_descends (prefixWord ++ tailWord_696213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696223 : List Nat := [1, 1, 2, 5, 3, 1, 3, 1, 3]
def baseStart_696223 : Nat := 118140960795 + 696223 * 2 ^ 59
def prefixEnd_696223 : Nat := 4983230072969 + 3 ^ 40 * 696223 * 2
def baseEnd_696223 : Nat := 317775148191408673787231

theorem tailTrace_696223 : CollatzResearch.WordTrace tailWord_696223 prefixEnd_696223 317775148191408673787231 := by
  unfold tailWord_696223
  simp only [CollatzResearch.WordTrace]
  refine ⟨25393338956710451266965323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16928892637806967511310215 25393338956710451266965323)
  ·
    refine ⟨38090008435065676900447985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25393338956710451266965323 38090008435065676900447985)
    ·
      refine ⟨28567506326299257675335989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38090008435065676900447985 28567506326299257675335989)
      ·
        refine ⟨2678203718090555407062749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28567506326299257675335989 2678203718090555407062749)
        ·
          refine ⟨1004326394283958277648531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2678203718090555407062749 1004326394283958277648531)
          ·
            refine ⟨1506489591425937416472797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1004326394283958277648531 1506489591425937416472797)
            ·
              refine ⟨564933596784726531177299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1506489591425937416472797 564933596784726531177299)
              ·
                refine ⟨847400395177089796765949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 564933596784726531177299 847400395177089796765949)
                ·
                  refine ⟨317775148191408673787231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 847400395177089796765949 317775148191408673787231)
                  ·
                    rfl

theorem cell20_696223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 3, 1, 3].length) (baseStart_696223 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_696223 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_696223 prefixEnd_696223 := by exact prefixLift 696223
  have htrace : WordTrace (prefixWord ++ tailWord_696223) baseStart_696223 baseEnd_696223 := by
    simpa [prefixWord, tailWord_696223, baseEnd_696223] using wordTrace_append hprefix tailTrace_696223
  have hstable : (prefixWord ++ tailWord_696223).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696223).length < 2 ^ (prefixWord ++ tailWord_696223).sum := by decide
  have hdescent : baseEnd_696223 < baseStart_696223 := by decide
  rcases family_descends (prefixWord ++ tailWord_696223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696248 : List Nat := [2, 1, 2, 1, 2, 3, 1, 1, 7]
def baseStart_696248 : Nat := 118140960795 + 696248 * 2 ^ 59
def prefixEnd_696248 : Nat := 4983230072969 + 3 ^ 40 * 696248 * 2
def baseEnd_696248 : Nat := 317786558872619697953795

theorem tailTrace_696248 : CollatzResearch.WordTrace tailWord_696248 prefixEnd_696248 317786558872619697953795 := by
  unfold tailWord_696248
  simp only [CollatzResearch.WordTrace]
  refine ⟨12697125390809940268312699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16929500521079920357750265 12697125390809940268312699)
  ·
    refine ⟨19045688086214910402469049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12697125390809940268312699 19045688086214910402469049)
    ·
      refine ⟨14284266064661182801851787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19045688086214910402469049 14284266064661182801851787)
      ·
        refine ⟨21426399096991774202777681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14284266064661182801851787 21426399096991774202777681)
        ·
          refine ⟨16069799322743830652083261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21426399096991774202777681 16069799322743830652083261)
          ·
            refine ⟨6026174746028936494531223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16069799322743830652083261 6026174746028936494531223)
            ·
              refine ⟨9039262119043404741796835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6026174746028936494531223 9039262119043404741796835)
              ·
                refine ⟨13558893178565107112695253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9039262119043404741796835 13558893178565107112695253)
                ·
                  refine ⟨317786558872619697953795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13558893178565107112695253 317786558872619697953795)
                  ·
                    rfl

theorem cell20_696248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 1, 7].length) (baseStart_696248 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_696248 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_696248 prefixEnd_696248 := by exact prefixLift 696248
  have htrace : WordTrace (prefixWord ++ tailWord_696248) baseStart_696248 baseEnd_696248 := by
    simpa [prefixWord, tailWord_696248, baseEnd_696248] using wordTrace_append hprefix tailTrace_696248
  have hstable : (prefixWord ++ tailWord_696248).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696248).length < 2 ^ (prefixWord ++ tailWord_696248).sum := by decide
  have hdescent : baseEnd_696248 < baseStart_696248 := by decide
  rcases family_descends (prefixWord ++ tailWord_696248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696272 : List Nat := [2, 1, 1, 1, 1, 2, 7, 1, 4]
def baseStart_696272 : Nat := 118140960795 + 696272 * 2 ^ 59
def prefixEnd_696272 : Nat := 4983230072969 + 3 ^ 40 * 696272 * 2
def baseEnd_696272 : Nat := 317797513126582281153697

theorem tailTrace_696272 : CollatzResearch.WordTrace tailWord_696272 prefixEnd_696272 317797513126582281153697 := by
  unfold tailWord_696272
  simp only [CollatzResearch.WordTrace]
  refine ⟨12697563066766466317749535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16930084089021955090332713 12697563066766466317749535)
  ·
    refine ⟨19046344600149699476624303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12697563066766466317749535 19046344600149699476624303)
    ·
      refine ⟨28569516900224549214936455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19046344600149699476624303 28569516900224549214936455)
      ·
        refine ⟨42854275350336823822404683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28569516900224549214936455 42854275350336823822404683)
        ·
          refine ⟨64281413025505235733607025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42854275350336823822404683 64281413025505235733607025)
          ·
            refine ⟨48211059769128926800205269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64281413025505235733607025 48211059769128926800205269)
            ·
              refine ⟨1129946713338959221879811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 48211059769128926800205269 1129946713338959221879811)
              ·
                refine ⟨1694920070008438832819717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1129946713338959221879811 1694920070008438832819717)
                ·
                  refine ⟨317797513126582281153697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1694920070008438832819717 317797513126582281153697)
                  ·
                    rfl

theorem cell20_696272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 7, 1, 4].length) (baseStart_696272 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_696272 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_696272 prefixEnd_696272 := by exact prefixLift 696272
  have htrace : WordTrace (prefixWord ++ tailWord_696272) baseStart_696272 baseEnd_696272 := by
    simpa [prefixWord, tailWord_696272, baseEnd_696272] using wordTrace_append hprefix tailTrace_696272
  have hstable : (prefixWord ++ tailWord_696272).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696272).length < 2 ^ (prefixWord ++ tailWord_696272).sum := by decide
  have hdescent : baseEnd_696272 < baseStart_696272 := by decide
  rcases family_descends (prefixWord ++ tailWord_696272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696279 : List Nat := [1, 1, 3, 2, 1, 1, 6, 5]
def baseStart_696279 : Nat := 118140960795 + 696279 * 2 ^ 59
def prefixEnd_696279 : Nat := 4983230072969 + 3 ^ 40 * 696279 * 2
def baseEnd_696279 : Nat := 105933569372440455973445

theorem tailTrace_696279 : CollatzResearch.WordTrace tailWord_696279 prefixEnd_696279 105933569372440455973445 := by
  unfold tailWord_696279
  simp only [CollatzResearch.WordTrace]
  refine ⟨25395381444507572831003891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16930254296338381887335927 25395381444507572831003891)
  ·
    refine ⟨38093072166761359246505837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25395381444507572831003891 38093072166761359246505837)
    ·
      refine ⟨14284902062535509717439689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38093072166761359246505837 14284902062535509717439689)
      ·
        refine ⟨10713676546901632288079767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14284902062535509717439689 10713676546901632288079767)
        ·
          refine ⟨16070514820352448432119651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10713676546901632288079767 16070514820352448432119651)
          ·
            refine ⟨24105772230528672648179477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16070514820352448432119651 24105772230528672648179477)
            ·
              refine ⟨1129958073306031530383413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 24105772230528672648179477 1129958073306031530383413)
              ·
                refine ⟨105933569372440455973445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1129958073306031530383413 105933569372440455973445)
                ·
                  rfl

theorem cell20_696279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 6, 5].length) (baseStart_696279 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_696279 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_696279 prefixEnd_696279 := by exact prefixLift 696279
  have htrace : WordTrace (prefixWord ++ tailWord_696279) baseStart_696279 baseEnd_696279 := by
    simpa [prefixWord, tailWord_696279, baseEnd_696279] using wordTrace_append hprefix tailTrace_696279
  have hstable : (prefixWord ++ tailWord_696279).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696279).length < 2 ^ (prefixWord ++ tailWord_696279).sum := by decide
  have hdescent : baseEnd_696279 < baseStart_696279 := by decide
  rcases family_descends (prefixWord ++ tailWord_696279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696282 : List Nat := [3, 1, 1, 2, 5, 1, 1, 3, 3]
def baseStart_696282 : Nat := 118140960795 + 696282 * 2 ^ 59
def prefixEnd_696282 : Nat := 4983230072969 + 3 ^ 40 * 696282 * 2
def baseEnd_696282 : Nat := 317802077399066690820323

theorem tailTrace_696282 : CollatzResearch.WordTrace tailWord_696282 prefixEnd_696282 317802077399066690820323 := by
  unfold tailWord_696282
  simp only [CollatzResearch.WordTrace]
  refine ⟨6348872715874176085840775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16930327242331136228908733 6348872715874176085840775)
  ·
    refine ⟨9523309073811264128761163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6348872715874176085840775 9523309073811264128761163)
    ·
      refine ⟨14284963610716896193141745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9523309073811264128761163 14284963610716896193141745)
      ·
        refine ⟨10713722708037672144856309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14284963610716896193141745 10713722708037672144856309)
        ·
          refine ⟨1004411503878531763580279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10713722708037672144856309 1004411503878531763580279)
          ·
            refine ⟨1506617255817797645370419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1004411503878531763580279 1506617255817797645370419)
            ·
              refine ⟨2259925883726696468055629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1506617255817797645370419 2259925883726696468055629)
              ·
                refine ⟨847472206397511175520861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2259925883726696468055629 847472206397511175520861)
                ·
                  refine ⟨317802077399066690820323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 847472206397511175520861 317802077399066690820323)
                  ·
                    rfl

theorem cell20_696282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 3, 3].length) (baseStart_696282 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_696282 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_696282 prefixEnd_696282 := by exact prefixLift 696282
  have htrace : WordTrace (prefixWord ++ tailWord_696282) baseStart_696282 baseEnd_696282 := by
    simpa [prefixWord, tailWord_696282, baseEnd_696282] using wordTrace_append hprefix tailTrace_696282
  have hstable : (prefixWord ++ tailWord_696282).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696282).length < 2 ^ (prefixWord ++ tailWord_696282).sum := by decide
  have hdescent : baseEnd_696282 < baseStart_696282 := by decide
  rcases family_descends (prefixWord ++ tailWord_696282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696326 : List Nat := [6, 2, 1, 2, 1, 2, 1, 5]
def baseStart_696326 : Nat := 118140960795 + 696326 * 2 ^ 59
def prefixEnd_696326 : Nat := 4983230072969 + 3 ^ 40 * 696326 * 2
def baseEnd_696326 : Nat := 105940720065999364451159

theorem tailTrace_696326 : CollatzResearch.WordTrace tailWord_696326 prefixEnd_696326 105940720065999364451159 := by
  unfold tailWord_696326
  simp only [CollatzResearch.WordTrace]
  refine ⟨793659239854290620561401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 16931397116891533238643221 793659239854290620561401)
  ·
    refine ⟨595244429890717965421051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 793659239854290620561401 595244429890717965421051)
    ·
      refine ⟨892866644836076948131577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 595244429890717965421051 892866644836076948131577)
      ·
        refine ⟨669649983627057711098683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 892866644836076948131577 669649983627057711098683)
        ·
          refine ⟨1004474975440586566648025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 669649983627057711098683 1004474975440586566648025)
          ·
            refine ⟨753356231580439924986019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1004474975440586566648025 753356231580439924986019)
            ·
              refine ⟨1130034347370659887479029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 753356231580439924986019 1130034347370659887479029)
              ·
                refine ⟨105940720065999364451159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1130034347370659887479029 105940720065999364451159)
                ·
                  rfl

theorem cell20_696326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_696326 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_696326 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_696326 prefixEnd_696326 := by exact prefixLift 696326
  have htrace : WordTrace (prefixWord ++ tailWord_696326) baseStart_696326 baseEnd_696326 := by
    simpa [prefixWord, tailWord_696326, baseEnd_696326] using wordTrace_append hprefix tailTrace_696326
  have hstable : (prefixWord ++ tailWord_696326).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696326).length < 2 ^ (prefixWord ++ tailWord_696326).sum := by decide
  have hdescent : baseEnd_696326 < baseStart_696326 := by decide
  rcases family_descends (prefixWord ++ tailWord_696326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696348 : List Nat := [2, 2, 3, 1, 3, 1, 1, 1, 6]
def baseStart_696348 : Nat := 118140960795 + 696348 * 2 ^ 59
def prefixEnd_696348 : Nat := 4983230072969 + 3 ^ 40 * 696348 * 2
def baseEnd_696348 : Nat := 317832201597463794620053

theorem tailTrace_696348 : CollatzResearch.WordTrace tailWord_696348 prefixEnd_696348 317832201597463794620053 := by
  unfold tailWord_696348
  simp only [CollatzResearch.WordTrace]
  refine ⟨12698949040628798807632849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16931932054171731743510465 12698949040628798807632849)
  ·
    refine ⟨9524211780471599105724637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12698949040628798807632849 9524211780471599105724637)
    ·
      refine ⟨3571579417676849664646739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9524211780471599105724637 3571579417676849664646739)
      ·
        refine ⟨5357369126515274496970109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3571579417676849664646739 5357369126515274496970109)
        ·
          refine ⟨2009013422443227936363791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5357369126515274496970109 2009013422443227936363791)
          ·
            refine ⟨3013520133664841904545687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2009013422443227936363791 3013520133664841904545687)
            ·
              refine ⟨4520280200497262856818531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3013520133664841904545687 4520280200497262856818531)
              ·
                refine ⟨6780420300745894285227797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4520280200497262856818531 6780420300745894285227797)
                ·
                  refine ⟨317832201597463794620053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6780420300745894285227797 317832201597463794620053)
                  ·
                    rfl

theorem cell20_696348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 1, 6].length) (baseStart_696348 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_696348 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_696348 prefixEnd_696348 := by exact prefixLift 696348
  have htrace : WordTrace (prefixWord ++ tailWord_696348) baseStart_696348 baseEnd_696348 := by
    simpa [prefixWord, tailWord_696348, baseEnd_696348] using wordTrace_append hprefix tailTrace_696348
  have hstable : (prefixWord ++ tailWord_696348).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696348).length < 2 ^ (prefixWord ++ tailWord_696348).sum := by decide
  have hdescent : baseEnd_696348 < baseStart_696348 := by decide
  rcases family_descends (prefixWord ++ tailWord_696348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696382 : List Nat := [4, 2, 1, 3, 2, 1, 2, 1, 4]
def baseStart_696382 : Nat := 118140960795 + 696382 * 2 ^ 59
def prefixEnd_696382 : Nat := 4983230072969 + 3 ^ 40 * 696382 * 2
def baseEnd_696382 : Nat := 317847720123910787486581

theorem tailTrace_696382 : CollatzResearch.WordTrace tailWord_696382 prefixEnd_696382 317847720123910787486581 := by
  unfold tailWord_696382
  simp only [CollatzResearch.WordTrace]
  refine ⟨3174892270391802677750425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16932758775422947614668933 3174892270391802677750425)
  ·
    refine ⟨2381169202793852008312819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3174892270391802677750425 2381169202793852008312819)
    ·
      refine ⟨3571753804190778012469229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2381169202793852008312819 3571753804190778012469229)
      ·
        refine ⟨1339407676571541754675961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3571753804190778012469229 1339407676571541754675961)
        ·
          refine ⟨1004555757428656316006971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1339407676571541754675961 1004555757428656316006971)
          ·
            refine ⟨1506833636142984474010457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1004555757428656316006971 1506833636142984474010457)
            ·
              refine ⟨1130125227107238355507843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1506833636142984474010457 1130125227107238355507843)
              ·
                refine ⟨1695187840660857533261765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1130125227107238355507843 1695187840660857533261765)
                ·
                  refine ⟨317847720123910787486581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1695187840660857533261765 317847720123910787486581)
                  ·
                    rfl

theorem cell20_696382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 2, 1, 4].length) (baseStart_696382 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_696382 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_696382 prefixEnd_696382 := by exact prefixLift 696382
  have htrace : WordTrace (prefixWord ++ tailWord_696382) baseStart_696382 baseEnd_696382 := by
    simpa [prefixWord, tailWord_696382, baseEnd_696382] using wordTrace_append hprefix tailTrace_696382
  have hstable : (prefixWord ++ tailWord_696382).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696382).length < 2 ^ (prefixWord ++ tailWord_696382).sum := by decide
  have hdescent : baseEnd_696382 < baseStart_696382 := by decide
  rcases family_descends (prefixWord ++ tailWord_696382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696406 : List Nat := [5, 2, 2, 1, 1, 1, 4, 4]
def baseStart_696406 : Nat := 118140960795 + 696406 * 2 ^ 59
def prefixEnd_696406 : Nat := 4983230072969 + 3 ^ 40 * 696406 * 2
def baseEnd_696406 : Nat := 105952891459291123562161

theorem tailTrace_696406 : CollatzResearch.WordTrace tailWord_696406 prefixEnd_696406 105952891459291123562161 := by
  unfold tailWord_696406
  simp only [CollatzResearch.WordTrace]
  refine ⟨1587500844690467095054817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16933342343364982347251381 1587500844690467095054817)
  ·
    refine ⟨1190625633517850321291113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1587500844690467095054817 1190625633517850321291113)
    ·
      refine ⟨892969225138387740968335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1190625633517850321291113 892969225138387740968335)
      ·
        refine ⟨1339453837707581611452503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 892969225138387740968335 1339453837707581611452503)
        ·
          refine ⟨2009180756561372417178755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1339453837707581611452503 2009180756561372417178755)
          ·
            refine ⟨3013771134842058625768133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2009180756561372417178755 3013771134842058625768133)
            ·
              refine ⟨565082087782885992331525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3013771134842058625768133 565082087782885992331525)
              ·
                refine ⟨105952891459291123562161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 565082087782885992331525 105952891459291123562161)
                ·
                  rfl

theorem cell20_696406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 4, 4].length) (baseStart_696406 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_696406 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_696406 prefixEnd_696406 := by exact prefixLift 696406
  have htrace : WordTrace (prefixWord ++ tailWord_696406) baseStart_696406 baseEnd_696406 := by
    simpa [prefixWord, tailWord_696406, baseEnd_696406] using wordTrace_append hprefix tailTrace_696406
  have hstable : (prefixWord ++ tailWord_696406).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696406).length < 2 ^ (prefixWord ++ tailWord_696406).sum := by decide
  have hdescent : baseEnd_696406 < baseStart_696406 := by decide
  rcases family_descends (prefixWord ++ tailWord_696406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696431 : List Nat := [1, 1, 2, 1, 3, 6, 6]
def baseStart_696431 : Nat := 118140960795 + 696431 * 2 ^ 59
def prefixEnd_696431 : Nat := 4983230072969 + 3 ^ 40 * 696431 * 2
def baseEnd_696431 : Nat := 35318898339898266094783

theorem tailTrace_696431 : CollatzResearch.WordTrace tailWord_696431 prefixEnd_696431 35318898339898266094783 := by
  unfold tailWord_696431
  simp only [CollatzResearch.WordTrace]
  refine ⟨25400925339956902790537147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16933950226637935193691431 25400925339956902790537147)
  ·
    refine ⟨38101388009935354185805721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25400925339956902790537147 38101388009935354185805721)
    ·
      refine ⟨28576041007451515639354291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38101388009935354185805721 28576041007451515639354291)
      ·
        refine ⟨42864061511177273459031437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28576041007451515639354291 42864061511177273459031437)
        ·
          refine ⟨16074023066691477547136789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42864061511177273459031437 16074023066691477547136789)
          ·
            refine ⟨753469831251163010022037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 16074023066691477547136789 753469831251163010022037)
            ·
              refine ⟨35318898339898266094783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 753469831251163010022037 35318898339898266094783)
              ·
                rfl

theorem cell20_696431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 6].length) (baseStart_696431 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_696431 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_696431 prefixEnd_696431 := by exact prefixLift 696431
  have htrace : WordTrace (prefixWord ++ tailWord_696431) baseStart_696431 baseEnd_696431 := by
    simpa [prefixWord, tailWord_696431, baseEnd_696431] using wordTrace_append hprefix tailTrace_696431
  have hstable : (prefixWord ++ tailWord_696431).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696431).length < 2 ^ (prefixWord ++ tailWord_696431).sum := by decide
  have hdescent : baseEnd_696431 < baseStart_696431 := by decide
  rcases family_descends (prefixWord ++ tailWord_696431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696441 : List Nat := [1, 2, 1, 3, 4, 3, 1, 1, 4]
def baseStart_696441 : Nat := 118140960795 + 696441 * 2 ^ 59
def prefixEnd_696441 : Nat := 4983230072969 + 3 ^ 40 * 696441 * 2
def baseEnd_696441 : Nat := 317874649331568804519673

theorem tailTrace_696441 : CollatzResearch.WordTrace tailWord_696441 prefixEnd_696441 317874649331568804519673 := by
  unfold tailWord_696441
  simp only [CollatzResearch.WordTrace]
  refine ⟨25401290069920674498401177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16934193379947116332267451 25401290069920674498401177)
  ·
    refine ⟨19050967552440505873800883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25401290069920674498401177 19050967552440505873800883)
    ·
      refine ⟨28576451328660758810701325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19050967552440505873800883 28576451328660758810701325)
      ·
        refine ⟨10716169248247784554012997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28576451328660758810701325 10716169248247784554012997)
        ·
          refine ⟨2009281734046459603877437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10716169248247784554012997 2009281734046459603877437)
          ·
            refine ⟨753480650267422351454039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2009281734046459603877437 753480650267422351454039)
            ·
              refine ⟨1130220975401133527181059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 753480650267422351454039 1130220975401133527181059)
              ·
                refine ⟨1695331463101700290771589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1130220975401133527181059 1695331463101700290771589)
                ·
                  refine ⟨317874649331568804519673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1695331463101700290771589 317874649331568804519673)
                  ·
                    rfl

theorem cell20_696441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 1, 1, 4].length) (baseStart_696441 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_696441 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_696441 prefixEnd_696441 := by exact prefixLift 696441
  have htrace : WordTrace (prefixWord ++ tailWord_696441) baseStart_696441 baseEnd_696441 := by
    simpa [prefixWord, tailWord_696441, baseEnd_696441] using wordTrace_append hprefix tailTrace_696441
  have hstable : (prefixWord ++ tailWord_696441).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696441).length < 2 ^ (prefixWord ++ tailWord_696441).sum := by decide
  have hdescent : baseEnd_696441 < baseStart_696441 := by decide
  rcases family_descends (prefixWord ++ tailWord_696441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696590 : List Nat := [4, 1, 1, 2, 1, 2, 1, 1, 7]
def baseStart_696590 : Nat := 118140960795 + 696590 * 2 ^ 59
def prefixEnd_696590 : Nat := 4983230072969 + 3 ^ 40 * 696590 * 2
def baseEnd_696590 : Nat := 317942656991586508552397

theorem tailTrace_696590 : CollatzResearch.WordTrace tailWord_696590 prefixEnd_696590 317942656991586508552397 := by
  unfold tailWord_696590
  simp only [CollatzResearch.WordTrace]
  refine ⟨3175840568297609118196903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16937816364253915297050149 3175840568297609118196903)
  ·
    refine ⟨4763760852446413677295355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3175840568297609118196903 4763760852446413677295355)
    ·
      refine ⟨7145641278669620515943033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4763760852446413677295355 7145641278669620515943033)
      ·
        refine ⟨5359230959002215386957275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7145641278669620515943033 5359230959002215386957275)
        ·
          refine ⟨8038846438503323080435913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5359230959002215386957275 8038846438503323080435913)
          ·
            refine ⟨6029134828877492310326935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8038846438503323080435913 6029134828877492310326935)
            ·
              refine ⟨9043702243316238465490403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6029134828877492310326935 9043702243316238465490403)
              ·
                refine ⟨13565553364974357698235605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9043702243316238465490403 13565553364974357698235605)
                ·
                  refine ⟨317942656991586508552397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13565553364974357698235605 317942656991586508552397)
                  ·
                    rfl

theorem cell20_696590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 1, 7].length) (baseStart_696590 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_696590 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_696590 prefixEnd_696590 := by exact prefixLift 696590
  have htrace : WordTrace (prefixWord ++ tailWord_696590) baseStart_696590 baseEnd_696590 := by
    simpa [prefixWord, tailWord_696590, baseEnd_696590] using wordTrace_append hprefix tailTrace_696590
  have hstable : (prefixWord ++ tailWord_696590).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696590).length < 2 ^ (prefixWord ++ tailWord_696590).sum := by decide
  have hdescent : baseEnd_696590 < baseStart_696590 := by decide
  rcases family_descends (prefixWord ++ tailWord_696590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696593 : List Nat := [1, 2, 2, 1, 1, 5, 3, 3, 2]
def baseStart_696593 : Nat := 118140960795 + 696593 * 2 ^ 59
def prefixEnd_696593 : Nat := 4983230072969 + 3 ^ 40 * 696593 * 2
def baseEnd_696593 : Nat := 317944026273331831452385

theorem tailTrace_696593 : CollatzResearch.WordTrace tailWord_696593 prefixEnd_696593 317944026273331831452385 := by
  unfold tailWord_696593
  simp only [CollatzResearch.WordTrace]
  refine ⟨25406833965370004457934433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16937889310246669638622955 25406833965370004457934433)
  ·
    refine ⟨19055125474027503343450825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25406833965370004457934433 19055125474027503343450825)
    ·
      refine ⟨14291344105520627507588119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19055125474027503343450825 14291344105520627507588119)
      ·
        refine ⟨21437016158280941261382179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14291344105520627507588119 21437016158280941261382179)
        ·
          refine ⟨32155524237421411892073269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21437016158280941261382179 32155524237421411892073269)
          ·
            refine ⟨3014580397258257364881869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32155524237421411892073269 3014580397258257364881869)
            ·
              refine ⟨1130467648971846511830701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3014580397258257364881869 1130467648971846511830701)
              ·
                refine ⟨423925368364442441936513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1130467648971846511830701 423925368364442441936513)
                ·
                  refine ⟨317944026273331831452385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 423925368364442441936513 317944026273331831452385)
                  ·
                    rfl

theorem cell20_696593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 3, 3, 2].length) (baseStart_696593 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_696593 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_696593 prefixEnd_696593 := by exact prefixLift 696593
  have htrace : WordTrace (prefixWord ++ tailWord_696593) baseStart_696593 baseEnd_696593 := by
    simpa [prefixWord, tailWord_696593, baseEnd_696593] using wordTrace_append hprefix tailTrace_696593
  have hstable : (prefixWord ++ tailWord_696593).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696593).length < 2 ^ (prefixWord ++ tailWord_696593).sum := by decide
  have hdescent : baseEnd_696593 < baseStart_696593 := by decide
  rcases family_descends (prefixWord ++ tailWord_696593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696597 : List Nat := [1, 3, 2, 1, 2, 1, 2, 2, 6]
def baseStart_696597 : Nat := 118140960795 + 696597 * 2 ^ 59
def prefixEnd_696597 : Nat := 4983230072969 + 3 ^ 40 * 696597 * 2
def baseEnd_696597 : Nat := 317945851982325595319035

theorem tailTrace_696597 : CollatzResearch.WordTrace tailWord_696597 prefixEnd_696597 317945851982325595319035 := by
  unfold tailWord_696597
  simp only [CollatzResearch.WordTrace]
  refine ⟨25406979857355513141080045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16937986571570342094053363 25406979857355513141080045)
  ·
    refine ⟨9527617446508317427905017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25406979857355513141080045 9527617446508317427905017)
    ·
      refine ⟨7145713084881238070928763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9527617446508317427905017 7145713084881238070928763)
      ·
        refine ⟨10718569627321857106393145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7145713084881238070928763 10718569627321857106393145)
        ·
          refine ⟨8038927220491392829794859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10718569627321857106393145 8038927220491392829794859)
          ·
            refine ⟨12058390830737089244692289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8038927220491392829794859 12058390830737089244692289)
            ·
              refine ⟨9043793123052816933519217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12058390830737089244692289 9043793123052816933519217)
              ·
                refine ⟨6782844842289612700139413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9043793123052816933519217 6782844842289612700139413)
                ·
                  refine ⟨317945851982325595319035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6782844842289612700139413 317945851982325595319035)
                  ·
                    rfl

theorem cell20_696597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 2, 6].length) (baseStart_696597 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_696597 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_696597 prefixEnd_696597 := by exact prefixLift 696597
  have htrace : WordTrace (prefixWord ++ tailWord_696597) baseStart_696597 baseEnd_696597 := by
    simpa [prefixWord, tailWord_696597, baseEnd_696597] using wordTrace_append hprefix tailTrace_696597
  have hstable : (prefixWord ++ tailWord_696597).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696597).length < 2 ^ (prefixWord ++ tailWord_696597).sum := by decide
  have hdescent : baseEnd_696597 < baseStart_696597 := by decide
  rcases family_descends (prefixWord ++ tailWord_696597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696606 : List Nat := [4, 3, 2, 1, 1, 2, 3, 2, 2]
def baseStart_696606 : Nat := 118140960795 + 696606 * 2 ^ 59
def prefixEnd_696606 : Nat := 4983230072969 + 3 ^ 40 * 696606 * 2
def baseEnd_696606 : Nat := 317949959827561564018999

theorem tailTrace_696606 : CollatzResearch.WordTrace tailWord_696606 prefixEnd_696606 317949959827561564018999 := by
  unfold tailWord_696606
  simp only [CollatzResearch.WordTrace]
  refine ⟨3175913514290363459769709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16938205409548605118771781 3175913514290363459769709)
  ·
    refine ⟨1190967567858886297413641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3175913514290363459769709 1190967567858886297413641)
    ·
      refine ⟨893225675894164723060231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1190967567858886297413641 893225675894164723060231)
      ·
        refine ⟨1339838513841247084590347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 893225675894164723060231 1339838513841247084590347)
        ·
          refine ⟨2009757770761870626885521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1339838513841247084590347 2009757770761870626885521)
          ·
            refine ⟨1507318328071402970164141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2009757770761870626885521 1507318328071402970164141)
            ·
              refine ⟨565244373026776113811553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1507318328071402970164141 565244373026776113811553)
              ·
                refine ⟨423933279770082085358665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 565244373026776113811553 423933279770082085358665)
                ·
                  refine ⟨317949959827561564018999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 423933279770082085358665 317949959827561564018999)
                  ·
                    rfl

theorem cell20_696606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 3, 2, 2].length) (baseStart_696606 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_696606 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_696606 prefixEnd_696606 := by exact prefixLift 696606
  have htrace : WordTrace (prefixWord ++ tailWord_696606) baseStart_696606 baseEnd_696606 := by
    simpa [prefixWord, tailWord_696606, baseEnd_696606] using wordTrace_append hprefix tailTrace_696606
  have hstable : (prefixWord ++ tailWord_696606).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696606).length < 2 ^ (prefixWord ++ tailWord_696606).sum := by decide
  have hdescent : baseEnd_696606 < baseStart_696606 := by decide
  rcases family_descends (prefixWord ++ tailWord_696606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696690 : List Nat := [3, 2, 1, 2, 1, 4, 1, 2, 4]
def baseStart_696690 : Nat := 118140960795 + 696690 * 2 ^ 59
def prefixEnd_696690 : Nat := 4983230072969 + 3 ^ 40 * 696690 * 2
def baseEnd_696690 : Nat := 317988299716430605218655

theorem tailTrace_696690 : CollatzResearch.WordTrace tailWord_696690 prefixEnd_696690 317988299716430605218655 := by
  unfold tailWord_696690
  simp only [CollatzResearch.WordTrace]
  refine ⟨6352592961504647506053881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16940247897345726682810349 6352592961504647506053881)
  ·
    refine ⟨4764444721128485629540411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6352592961504647506053881 4764444721128485629540411)
    ·
      refine ⟨7146667081692728444310617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4764444721128485629540411 7146667081692728444310617)
      ·
        refine ⟨5360000311269546333232963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7146667081692728444310617 5360000311269546333232963)
        ·
          refine ⟨8040000466904319499849445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5360000311269546333232963 8040000466904319499849445)
          ·
            refine ⟨1507500087544559906221771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8040000466904319499849445 1507500087544559906221771)
            ·
              refine ⟨2261250131316839859332657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1507500087544559906221771 2261250131316839859332657)
              ·
                refine ⟨1695937598487629894499493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2261250131316839859332657 1695937598487629894499493)
                ·
                  refine ⟨317988299716430605218655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1695937598487629894499493 317988299716430605218655)
                  ·
                    rfl

theorem cell20_696690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 2, 4].length) (baseStart_696690 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_696690 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_696690 prefixEnd_696690 := by exact prefixLift 696690
  have htrace : WordTrace (prefixWord ++ tailWord_696690) baseStart_696690 baseEnd_696690 := by
    simpa [prefixWord, tailWord_696690, baseEnd_696690] using wordTrace_append hprefix tailTrace_696690
  have hstable : (prefixWord ++ tailWord_696690).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696690).length < 2 ^ (prefixWord ++ tailWord_696690).sum := by decide
  have hdescent : baseEnd_696690 < baseStart_696690 := by decide
  rcases family_descends (prefixWord ++ tailWord_696690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696711 : List Nat := [1, 1, 4, 2, 2, 1, 1, 2, 6]
def baseStart_696711 : Nat := 118140960795 + 696711 * 2 ^ 59
def prefixEnd_696711 : Nat := 4983230072969 + 3 ^ 40 * 696711 * 2
def baseEnd_696711 : Nat := 317997884688647865518569

theorem tailTrace_696711 : CollatzResearch.WordTrace tailWord_696711 prefixEnd_696711 317997884688647865518569 := by
  unfold tailWord_696711
  simp only [CollatzResearch.WordTrace]
  refine ⟨25411137778942510610729987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16940758519295007073819991 25411137778942510610729987)
  ·
    refine ⟨38116706668413765916094981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25411137778942510610729987 38116706668413765916094981)
    ·
      refine ⟨7146882500327581109267809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38116706668413765916094981 7146882500327581109267809)
      ·
        refine ⟨5360161875245685831950857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7146882500327581109267809 5360161875245685831950857)
        ·
          refine ⟨4020121406434264373963143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5360161875245685831950857 4020121406434264373963143)
          ·
            refine ⟨6030182109651396560944715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4020121406434264373963143 6030182109651396560944715)
            ·
              refine ⟨9045273164477094841417073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6030182109651396560944715 9045273164477094841417073)
              ·
                refine ⟨6783954873357821131062805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9045273164477094841417073 6783954873357821131062805)
                ·
                  refine ⟨317997884688647865518569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6783954873357821131062805 317997884688647865518569)
                  ·
                    rfl

theorem cell20_696711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 2, 6].length) (baseStart_696711 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_696711 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_696711 prefixEnd_696711 := by exact prefixLift 696711
  have htrace : WordTrace (prefixWord ++ tailWord_696711) baseStart_696711 baseEnd_696711 := by
    simpa [prefixWord, tailWord_696711, baseEnd_696711] using wordTrace_append hprefix tailTrace_696711
  have hstable : (prefixWord ++ tailWord_696711).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696711).length < 2 ^ (prefixWord ++ tailWord_696711).sum := by decide
  have hdescent : baseEnd_696711 < baseStart_696711 := by decide
  rcases family_descends (prefixWord ++ tailWord_696711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696714 : List Nat := [3, 1, 2, 5, 1, 1, 7]
def baseStart_696714 : Nat := 118140960795 + 696714 * 2 ^ 59
def prefixEnd_696714 : Nat := 4983230072969 + 3 ^ 40 * 696714 * 2
def baseEnd_696714 : Nat := 35333250441154798713173

theorem tailTrace_696714 : CollatzResearch.WordTrace tailWord_696714 prefixEnd_696714 35333250441154798713173 := by
  unfold tailWord_696714
  simp only [CollatzResearch.WordTrace]
  refine ⟨6352811799482910530772299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16940831465287761415392797 6352811799482910530772299)
  ·
    refine ⟨9529217699224365796158449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6352811799482910530772299 9529217699224365796158449)
    ·
      refine ⟨7146913274418274347118837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9529217699224365796158449 7146913274418274347118837)
      ·
        refine ⟨670023119476713220042391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7146913274418274347118837 670023119476713220042391)
        ·
          refine ⟨1005034679215069830063587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 670023119476713220042391 1005034679215069830063587)
          ·
            refine ⟨1507552018822604745095381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1005034679215069830063587 1507552018822604745095381)
            ·
              refine ⟨35333250441154798713173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1507552018822604745095381 35333250441154798713173)
              ·
                rfl

theorem cell20_696714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 7].length) (baseStart_696714 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_696714 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_696714 prefixEnd_696714 := by exact prefixLift 696714
  have htrace : WordTrace (prefixWord ++ tailWord_696714) baseStart_696714 baseEnd_696714 := by
    simpa [prefixWord, tailWord_696714, baseEnd_696714] using wordTrace_append hprefix tailTrace_696714
  have hstable : (prefixWord ++ tailWord_696714).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696714).length < 2 ^ (prefixWord ++ tailWord_696714).sum := by decide
  have hdescent : baseEnd_696714 < baseStart_696714 := by decide
  rcases family_descends (prefixWord ++ tailWord_696714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696728 : List Nat := [2, 1, 2, 5, 1, 1, 1, 3, 4]
def baseStart_696728 : Nat := 118140960795 + 696728 * 2 ^ 59
def prefixEnd_696728 : Nat := 4983230072969 + 3 ^ 40 * 696728 * 2
def baseEnd_696728 : Nat := 318005643951871361951833

theorem tailTrace_696728 : CollatzResearch.WordTrace tailWord_696728 prefixEnd_696728 318005643951871361951833 := by
  unfold tailWord_696728
  simp only [CollatzResearch.WordTrace]
  refine ⟨12705878909940461257049419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16941171879920615009399225 12705878909940461257049419)
  ·
    refine ⟨19058818364910691885574129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12705878909940461257049419 19058818364910691885574129)
    ·
      refine ⟨14294113773683018914180597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19058818364910691885574129 14294113773683018914180597)
      ·
        refine ⟨1340073166282783023204431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14294113773683018914180597 1340073166282783023204431)
        ·
          refine ⟨2010109749424174534806647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1340073166282783023204431 2010109749424174534806647)
          ·
            refine ⟨3015164624136261802209971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2010109749424174534806647 3015164624136261802209971)
            ·
              refine ⟨4522746936204392703314957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3015164624136261802209971 4522746936204392703314957)
              ·
                refine ⟨1696030101076647263743109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4522746936204392703314957 1696030101076647263743109)
                ·
                  refine ⟨318005643951871361951833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1696030101076647263743109 318005643951871361951833)
                  ·
                    rfl

theorem cell20_696728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 3, 4].length) (baseStart_696728 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_696728 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_696728 prefixEnd_696728 := by exact prefixLift 696728
  have htrace : WordTrace (prefixWord ++ tailWord_696728) baseStart_696728 baseEnd_696728 := by
    simpa [prefixWord, tailWord_696728, baseEnd_696728] using wordTrace_append hprefix tailTrace_696728
  have hstable : (prefixWord ++ tailWord_696728).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696728).length < 2 ^ (prefixWord ++ tailWord_696728).sum := by decide
  have hdescent : baseEnd_696728 < baseStart_696728 := by decide
  rcases family_descends (prefixWord ++ tailWord_696728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696738 : List Nat := [3, 3, 1, 2, 1, 1, 5, 1, 3]
def baseStart_696738 : Nat := 118140960795 + 696738 * 2 ^ 59
def prefixEnd_696738 : Nat := 4983230072969 + 3 ^ 40 * 696738 * 2
def baseEnd_696738 : Nat := 318010208224355771618459

theorem tailTrace_696738 : CollatzResearch.WordTrace tailWord_696738 prefixEnd_696738 318010208224355771618459 := by
  unfold tailWord_696738
  simp only [CollatzResearch.WordTrace]
  refine ⟨6353030637461173555490717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16941415033229796147975245 6353030637461173555490717)
  ·
    refine ⟨2382386489047940083309019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6353030637461173555490717 2382386489047940083309019)
    ·
      refine ⟨3573579733571910124963529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2382386489047940083309019 3573579733571910124963529)
      ·
        refine ⟨2680184800178932593722647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3573579733571910124963529 2680184800178932593722647)
        ·
          refine ⟨4020277200268398890583971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2680184800178932593722647 4020277200268398890583971)
          ·
            refine ⟨6030415800402598335875957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4020277200268398890583971 6030415800402598335875957)
            ·
              refine ⟨565351481287743593988371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6030415800402598335875957 565351481287743593988371)
              ·
                refine ⟨848027221931615390982557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 565351481287743593988371 848027221931615390982557)
                ·
                  refine ⟨318010208224355771618459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 848027221931615390982557 318010208224355771618459)
                  ·
                    rfl

theorem cell20_696738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 5, 1, 3].length) (baseStart_696738 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_696738 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_696738 prefixEnd_696738 := by exact prefixLift 696738
  have htrace : WordTrace (prefixWord ++ tailWord_696738) baseStart_696738 baseEnd_696738 := by
    simpa [prefixWord, tailWord_696738, baseEnd_696738] using wordTrace_append hprefix tailTrace_696738
  have hstable : (prefixWord ++ tailWord_696738).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696738).length < 2 ^ (prefixWord ++ tailWord_696738).sum := by decide
  have hdescent : baseEnd_696738 < baseStart_696738 := by decide
  rcases family_descends (prefixWord ++ tailWord_696738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696790 : List Nat := [5, 2, 1, 1, 1, 1, 4, 5]
def baseStart_696790 : Nat := 118140960795 + 696790 * 2 ^ 59
def prefixEnd_696790 : Nat := 4983230072969 + 3 ^ 40 * 696790 * 2
def baseEnd_696790 : Nat := 106011314147091567294971

theorem tailTrace_696790 : CollatzResearch.WordTrace tailWord_696790 prefixEnd_696790 106011314147091567294971 := by
  unfold tailWord_696790
  simp only [CollatzResearch.WordTrace]
  refine ⟨1588376196603519193928489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16942679430437538068570549 1588376196603519193928489)
  ·
    refine ⟨1191282147452639395446367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1588376196603519193928489 1191282147452639395446367)
    ·
      refine ⟨1786923221178959093169551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1191282147452639395446367 1786923221178959093169551)
      ·
        refine ⟨2680384831768438639754327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1786923221178959093169551 2680384831768438639754327)
        ·
          refine ⟨4020577247652657959631491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2680384831768438639754327 4020577247652657959631491)
          ·
            refine ⟨6030865871478986939447237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4020577247652657959631491 6030865871478986939447237)
            ·
              refine ⟨1130787350902310051146357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6030865871478986939447237 1130787350902310051146357)
              ·
                refine ⟨106011314147091567294971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1130787350902310051146357 106011314147091567294971)
                ·
                  rfl

theorem cell20_696790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 4, 5].length) (baseStart_696790 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_696790 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_696790 prefixEnd_696790 := by exact prefixLift 696790
  have htrace : WordTrace (prefixWord ++ tailWord_696790) baseStart_696790 baseEnd_696790 := by
    simpa [prefixWord, tailWord_696790, baseEnd_696790] using wordTrace_append hprefix tailTrace_696790
  have hstable : (prefixWord ++ tailWord_696790).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696790).length < 2 ^ (prefixWord ++ tailWord_696790).sum := by decide
  have hdescent : baseEnd_696790 < baseStart_696790 := by decide
  rcases family_descends (prefixWord ++ tailWord_696790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696797 : List Nat := [1, 4, 3, 1, 1, 1, 3, 3, 3]
def baseStart_696797 : Nat := 118140960795 + 696797 * 2 ^ 59
def prefixEnd_696797 : Nat := 4983230072969 + 3 ^ 40 * 696797 * 2
def baseEnd_696797 : Nat := 318037137432013788651551

theorem tailTrace_696797 : CollatzResearch.WordTrace tailWord_696797 prefixEnd_696797 318037137432013788651551 := by
  unfold tailWord_696797
  simp only [CollatzResearch.WordTrace]
  refine ⟨25414274456630947298360645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16942849637753964865573763 25414274456630947298360645)
  ·
    refine ⟨4765176460618302618442621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25414274456630947298360645 4765176460618302618442621)
    ·
      refine ⟨1786941172731863481915983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4765176460618302618442621 1786941172731863481915983)
      ·
        refine ⟨2680411759097795222873975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1786941172731863481915983 2680411759097795222873975)
        ·
          refine ⟨4020617638646692834310963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2680411759097795222873975 4020617638646692834310963)
          ·
            refine ⟨6030926457970039251466445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4020617638646692834310963 6030926457970039251466445)
            ·
              refine ⟨2261597421738764719299917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6030926457970039251466445 2261597421738764719299917)
              ·
                refine ⟨848099033152036769737469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2261597421738764719299917 848099033152036769737469)
                ·
                  refine ⟨318037137432013788651551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 848099033152036769737469 318037137432013788651551)
                  ·
                    rfl

theorem cell20_696797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 3, 3].length) (baseStart_696797 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_696797 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_696797 prefixEnd_696797 := by exact prefixLift 696797
  have htrace : WordTrace (prefixWord ++ tailWord_696797) baseStart_696797 baseEnd_696797 := by
    simpa [prefixWord, tailWord_696797, baseEnd_696797] using wordTrace_append hprefix tailTrace_696797
  have hstable : (prefixWord ++ tailWord_696797).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696797).length < 2 ^ (prefixWord ++ tailWord_696797).sum := by decide
  have hdescent : baseEnd_696797 < baseStart_696797 := by decide
  rcases family_descends (prefixWord ++ tailWord_696797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696834 : List Nat := [3, 4, 1, 2, 2, 2, 2, 2, 2]
def baseStart_696834 : Nat := 118140960795 + 696834 * 2 ^ 59
def prefixEnd_696834 : Nat := 4983230072969 + 3 ^ 40 * 696834 * 2
def baseEnd_696834 : Nat := 318054025240206104418067

theorem tailTrace_696834 : CollatzResearch.WordTrace tailWord_696834 prefixEnd_696834 318054025240206104418067 := by
  unfold tailWord_696834
  simp only [CollatzResearch.WordTrace]
  refine ⟨6353905989374225654364389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16943749304997935078305037 6353905989374225654364389)
  ·
    refine ⟨1191357373007667310193323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6353905989374225654364389 1191357373007667310193323)
    ·
      refine ⟨1787036059511500965289985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1191357373007667310193323 1787036059511500965289985)
      ·
        refine ⟨1340277044633625723967489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1787036059511500965289985 1340277044633625723967489)
        ·
          refine ⟨1005207783475219292975617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1340277044633625723967489 1005207783475219292975617)
          ·
            refine ⟨753905837606414469731713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1005207783475219292975617 753905837606414469731713)
            ·
              refine ⟨565429378204810852298785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 753905837606414469731713 565429378204810852298785)
              ·
                refine ⟨424072033653608139224089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 565429378204810852298785 424072033653608139224089)
                ·
                  refine ⟨318054025240206104418067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 424072033653608139224089 318054025240206104418067)
                  ·
                    rfl

theorem cell20_696834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 2, 2, 2].length) (baseStart_696834 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_696834 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_696834 prefixEnd_696834 := by exact prefixLift 696834
  have htrace : WordTrace (prefixWord ++ tailWord_696834) baseStart_696834 baseEnd_696834 := by
    simpa [prefixWord, tailWord_696834, baseEnd_696834] using wordTrace_append hprefix tailTrace_696834
  have hstable : (prefixWord ++ tailWord_696834).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696834).length < 2 ^ (prefixWord ++ tailWord_696834).sum := by decide
  have hdescent : baseEnd_696834 < baseStart_696834 := by decide
  rcases family_descends (prefixWord ++ tailWord_696834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696845 : List Nat := [1, 7, 1, 1, 1, 1, 3, 5]
def baseStart_696845 : Nat := 118140960795 + 696845 * 2 ^ 59
def prefixEnd_696845 : Nat := 4983230072969 + 3 ^ 40 * 696845 * 2
def baseEnd_696845 : Nat := 106019681979979651683785

theorem tailTrace_696845 : CollatzResearch.WordTrace tailWord_696845 prefixEnd_696845 106019681979979651683785 := by
  unfold tailWord_696845
  simp only [CollatzResearch.WordTrace]
  refine ⟨25416025160457051496107989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16944016773638034330738659 25416025160457051496107989)
  ·
    refine ⟨595688089698212144440031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 25416025160457051496107989 595688089698212144440031)
    ·
      refine ⟨893532134547318216660047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 595688089698212144440031 893532134547318216660047)
      ·
        refine ⟨1340298201820977324990071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 893532134547318216660047 1340298201820977324990071)
        ·
          refine ⟨2010447302731465987485107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1340298201820977324990071 2010447302731465987485107)
          ·
            refine ⟨3015670954097198981227661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2010447302731465987485107 3015670954097198981227661)
            ·
              refine ⟨1130876607786449617960373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3015670954097198981227661 1130876607786449617960373)
              ·
                refine ⟨106019681979979651683785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1130876607786449617960373 106019681979979651683785)
                ·
                  rfl

theorem cell20_696845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 3, 5].length) (baseStart_696845 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_696845 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_696845 prefixEnd_696845 := by exact prefixLift 696845
  have htrace : WordTrace (prefixWord ++ tailWord_696845) baseStart_696845 baseEnd_696845 := by
    simpa [prefixWord, tailWord_696845, baseEnd_696845] using wordTrace_append hprefix tailTrace_696845
  have hstable : (prefixWord ++ tailWord_696845).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696845).length < 2 ^ (prefixWord ++ tailWord_696845).sum := by decide
  have hdescent : baseEnd_696845 < baseStart_696845 := by decide
  rcases family_descends (prefixWord ++ tailWord_696845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696852 : List Nat := [2, 4, 3, 1, 1, 1, 2, 3, 3]
def baseStart_696852 : Nat := 118140960795 + 696852 * 2 ^ 59
def prefixEnd_696852 : Nat := 4983230072969 + 3 ^ 40 * 696852 * 2
def baseEnd_696852 : Nat := 318062240930678041817993

theorem tailTrace_696852 : CollatzResearch.WordTrace tailWord_696852 prefixEnd_696852 318062240930678041817993 := by
  unfold tailWord_696852
  simp only [CollatzResearch.WordTrace]
  refine ⟨12708140235715845845806405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16944186980954461127741873 12708140235715845845806405)
  ·
    refine ⟨2382776294196721096088701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12708140235715845845806405 2382776294196721096088701)
    ·
      refine ⟨893541110323770411033263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2382776294196721096088701 893541110323770411033263)
      ·
        refine ⟨1340311665485655616549895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 893541110323770411033263 1340311665485655616549895)
        ·
          refine ⟨2010467498228483424824843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1340311665485655616549895 2010467498228483424824843)
          ·
            refine ⟨3015701247342725137237265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2010467498228483424824843 3015701247342725137237265)
            ·
              refine ⟨2261775935507043852927949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3015701247342725137237265 2261775935507043852927949)
              ·
                refine ⟨848165975815141444847981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2261775935507043852927949 848165975815141444847981)
                ·
                  refine ⟨318062240930678041817993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 848165975815141444847981 318062240930678041817993)
                  ·
                    rfl

theorem cell20_696852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 3, 3].length) (baseStart_696852 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_696852 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_696852 prefixEnd_696852 := by exact prefixLift 696852
  have htrace : WordTrace (prefixWord ++ tailWord_696852) baseStart_696852 baseEnd_696852 := by
    simpa [prefixWord, tailWord_696852, baseEnd_696852] using wordTrace_append hprefix tailTrace_696852
  have hstable : (prefixWord ++ tailWord_696852).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696852).length < 2 ^ (prefixWord ++ tailWord_696852).sum := by decide
  have hdescent : baseEnd_696852 < baseStart_696852 := by decide
  rcases family_descends (prefixWord ++ tailWord_696852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696880 : List Nat := [2, 1, 1, 1, 2, 3, 3, 5, 2]
def baseStart_696880 : Nat := 118140960795 + 696880 * 2 ^ 59
def prefixEnd_696880 : Nat := 4983230072969 + 3 ^ 40 * 696880 * 2
def baseEnd_696880 : Nat := 318075020893634388884545

theorem tailTrace_696880 : CollatzResearch.WordTrace tailWord_696880 prefixEnd_696880 318075020893634388884545 := by
  unfold tailWord_696880
  simp only [CollatzResearch.WordTrace]
  refine ⟨12708650857665126236816047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16944867810220168315754729 12708650857665126236816047)
  ·
    refine ⟨19062976286497689355224071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12708650857665126236816047 19062976286497689355224071)
    ·
      refine ⟨28594464429746534032836107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19062976286497689355224071 28594464429746534032836107)
      ·
        refine ⟨42891696644619801049254161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28594464429746534032836107 42891696644619801049254161)
        ·
          refine ⟨32168772483464850786940621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42891696644619801049254161 32168772483464850786940621)
          ·
            refine ⟨12063289681299319045102733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32168772483464850786940621 12063289681299319045102733)
            ·
              refine ⟨4523733630487244641913525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12063289681299319045102733 4523733630487244641913525)
              ·
                refine ⟨424100027858179185179393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4523733630487244641913525 424100027858179185179393)
                ·
                  refine ⟨318075020893634388884545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 424100027858179185179393 318075020893634388884545)
                  ·
                    rfl

theorem cell20_696880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 5, 2].length) (baseStart_696880 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_696880 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_696880 prefixEnd_696880 := by exact prefixLift 696880
  have htrace : WordTrace (prefixWord ++ tailWord_696880) baseStart_696880 baseEnd_696880 := by
    simpa [prefixWord, tailWord_696880, baseEnd_696880] using wordTrace_append hprefix tailTrace_696880
  have hstable : (prefixWord ++ tailWord_696880).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696880).length < 2 ^ (prefixWord ++ tailWord_696880).sum := by decide
  have hdescent : baseEnd_696880 < baseStart_696880 := by decide
  rcases family_descends (prefixWord ++ tailWord_696880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696897 : List Nat := [1, 2, 5, 1, 1, 2, 2, 4, 2]
def baseStart_696897 : Nat := 118140960795 + 696897 * 2 ^ 59
def prefixEnd_696897 : Nat := 4983230072969 + 3 ^ 40 * 696897 * 2
def baseEnd_696897 : Nat := 318082780156857885317809

theorem tailTrace_696897 : CollatzResearch.WordTrace tailWord_696897 prefixEnd_696897 318082780156857885317809 := by
  unfold tailWord_696897
  simp only [CollatzResearch.WordTrace]
  refine ⟨25417921756268664377000945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16945281170845776251333963 25417921756268664377000945)
  ·
    refine ⟨19063441317201498282750709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25417921756268664377000945 19063441317201498282750709)
    ·
      refine ⟨1787197623487640464007879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19063441317201498282750709 1787197623487640464007879)
      ·
        refine ⟨2680796435231460696011819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1787197623487640464007879 2680796435231460696011819)
        ·
          refine ⟨4021194652847191044017729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2680796435231460696011819 4021194652847191044017729)
          ·
            refine ⟨3015895989635393283013297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4021194652847191044017729 3015895989635393283013297)
            ·
              refine ⟨2261921992226544962259973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3015895989635393283013297 2261921992226544962259973)
              ·
                refine ⟨424110373542477180423745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2261921992226544962259973 424110373542477180423745)
                ·
                  refine ⟨318082780156857885317809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 424110373542477180423745 318082780156857885317809)
                  ·
                    rfl

theorem cell20_696897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 4, 2].length) (baseStart_696897 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_696897 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_696897 prefixEnd_696897 := by exact prefixLift 696897
  have htrace : WordTrace (prefixWord ++ tailWord_696897) baseStart_696897 baseEnd_696897 := by
    simpa [prefixWord, tailWord_696897, baseEnd_696897] using wordTrace_append hprefix tailTrace_696897
  have hstable : (prefixWord ++ tailWord_696897).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696897).length < 2 ^ (prefixWord ++ tailWord_696897).sum := by decide
  have hdescent : baseEnd_696897 < baseStart_696897 := by decide
  rcases family_descends (prefixWord ++ tailWord_696897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696901 : List Nat := [1, 3, 1, 1, 1, 5, 1, 3, 4]
def baseStart_696901 : Nat := 118140960795 + 696901 * 2 ^ 59
def prefixEnd_696901 : Nat := 4983230072969 + 3 ^ 40 * 696901 * 2
def baseEnd_696901 : Nat := 318084605865851649184459

theorem tailTrace_696901 : CollatzResearch.WordTrace tailWord_696901 prefixEnd_696901 318084605865851649184459 := by
  unfold tailWord_696901
  simp only [CollatzResearch.WordTrace]
  refine ⟨25418067648254173060146557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16945378432169448706764371 25418067648254173060146557)
  ·
    refine ⟨9531775368095314897554959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25418067648254173060146557 9531775368095314897554959)
    ·
      refine ⟨14297663052142972346332439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9531775368095314897554959 14297663052142972346332439)
      ·
        refine ⟨21446494578214458519498659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14297663052142972346332439 21446494578214458519498659)
        ·
          refine ⟨32169741867321687779247989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21446494578214458519498659 32169741867321687779247989)
          ·
            refine ⟨3015913300061408229304499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32169741867321687779247989 3015913300061408229304499)
            ·
              refine ⟨4523869950092112343956749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3015913300061408229304499 4523869950092112343956749)
              ·
                refine ⟨1696451231284542128983781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4523869950092112343956749 1696451231284542128983781)
                ·
                  refine ⟨318084605865851649184459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1696451231284542128983781 318084605865851649184459)
                  ·
                    rfl

theorem cell20_696901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 3, 4].length) (baseStart_696901 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_696901 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_696901 prefixEnd_696901 := by exact prefixLift 696901
  have htrace : WordTrace (prefixWord ++ tailWord_696901) baseStart_696901 baseEnd_696901 := by
    simpa [prefixWord, tailWord_696901, baseEnd_696901] using wordTrace_append hprefix tailTrace_696901
  have hstable : (prefixWord ++ tailWord_696901).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696901).length < 2 ^ (prefixWord ++ tailWord_696901).sum := by decide
  have hdescent : baseEnd_696901 < baseStart_696901 := by decide
  rcases family_descends (prefixWord ++ tailWord_696901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696908 : List Nat := [2, 2, 1, 3, 1, 2, 2, 7]
def baseStart_696908 : Nat := 118140960795 + 696908 * 2 ^ 59
def prefixEnd_696908 : Nat := 4983230072969 + 3 ^ 40 * 696908 * 2
def baseEnd_696908 : Nat := 106029266952196911983699

theorem tailTrace_696908 : CollatzResearch.WordTrace tailWord_696908 prefixEnd_696908 106029266952196911983699 := by
  unfold tailWord_696908
  simp only [CollatzResearch.WordTrace]
  refine ⟨12709161479614406627825689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16945548639485875503767585 12709161479614406627825689)
  ·
    refine ⟨9531871109710804970869267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12709161479614406627825689 9531871109710804970869267)
    ·
      refine ⟨14297806664566207456303901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9531871109710804970869267 14297806664566207456303901)
      ·
        refine ⟨5361677499212327796113963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14297806664566207456303901 5361677499212327796113963)
        ·
          refine ⟨8042516248818491694170945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5361677499212327796113963 8042516248818491694170945)
          ·
            refine ⟨6031887186613868770628209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8042516248818491694170945 6031887186613868770628209)
            ·
              refine ⟨4523915389960401577971157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6031887186613868770628209 4523915389960401577971157)
              ·
                refine ⟨106029266952196911983699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4523915389960401577971157 106029266952196911983699)
                ·
                  rfl

theorem cell20_696908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 7].length) (baseStart_696908 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_696908 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_696908 prefixEnd_696908 := by exact prefixLift 696908
  have htrace : WordTrace (prefixWord ++ tailWord_696908) baseStart_696908 baseEnd_696908 := by
    simpa [prefixWord, tailWord_696908, baseEnd_696908] using wordTrace_append hprefix tailTrace_696908
  have hstable : (prefixWord ++ tailWord_696908).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696908).length < 2 ^ (prefixWord ++ tailWord_696908).sum := by decide
  have hdescent : baseEnd_696908 < baseStart_696908 := by decide
  rcases family_descends (prefixWord ++ tailWord_696908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696956 : List Nat := [2, 2, 2, 1, 1, 2, 2, 6, 2]
def baseStart_696956 : Nat := 118140960795 + 696956 * 2 ^ 59
def prefixEnd_696956 : Nat := 4983230072969 + 3 ^ 40 * 696956 * 2
def baseEnd_696956 : Nat := 318109709364515902350901

theorem tailTrace_696956 : CollatzResearch.WordTrace tailWord_696956 prefixEnd_696956 318109709364515902350901 := by
  unfold tailWord_696956
  simp only [CollatzResearch.WordTrace]
  refine ⟨12710036831527458726699361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16946715775369944968932481 12710036831527458726699361)
  ·
    refine ⟨9532527623645594045024521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12710036831527458726699361 9532527623645594045024521)
    ·
      refine ⟨7149395717734195533768391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9532527623645594045024521 7149395717734195533768391)
      ·
        refine ⟨10724093576601293300652587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7149395717734195533768391 10724093576601293300652587)
        ·
          refine ⟨16086140364901939950978881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10724093576601293300652587 16086140364901939950978881)
          ·
            refine ⟨12064605273676454963234161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16086140364901939950978881 12064605273676454963234161)
            ·
              refine ⟨9048453955257341222425621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12064605273676454963234161 9048453955257341222425621)
              ·
                refine ⟨424146279152687869801201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9048453955257341222425621 424146279152687869801201)
                ·
                  refine ⟨318109709364515902350901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 424146279152687869801201 318109709364515902350901)
                  ·
                    rfl

theorem cell20_696956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 6, 2].length) (baseStart_696956 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_696956 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_696956 prefixEnd_696956 := by exact prefixLift 696956
  have htrace : WordTrace (prefixWord ++ tailWord_696956) baseStart_696956 baseEnd_696956 := by
    simpa [prefixWord, tailWord_696956, baseEnd_696956] using wordTrace_append hprefix tailTrace_696956
  have hstable : (prefixWord ++ tailWord_696956).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696956).length < 2 ^ (prefixWord ++ tailWord_696956).sum := by decide
  have hdescent : baseEnd_696956 < baseStart_696956 := by decide
  rcases family_descends (prefixWord ++ tailWord_696956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696962 : List Nat := [3, 4, 3, 1, 1, 1, 1, 3, 3]
def baseStart_696962 : Nat := 118140960795 + 696962 * 2 ^ 59
def prefixEnd_696962 : Nat := 4983230072969 + 3 ^ 40 * 696962 * 2
def baseEnd_696962 : Nat := 318112447928006548150877

theorem tailTrace_696962 : CollatzResearch.WordTrace tailWord_696962 prefixEnd_696962 318112447928006548150877 := by
  unfold tailWord_696962
  simp only [CollatzResearch.WordTrace]
  refine ⟨6355073125258295119529285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16946861667355453652078093 6355073125258295119529285)
  ·
    refine ⟨1191576210985930334911741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6355073125258295119529285 1191576210985930334911741)
    ·
      refine ⟨446841079119723875591903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1191576210985930334911741 446841079119723875591903)
      ·
        refine ⟨670261618679585813387855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 446841079119723875591903 670261618679585813387855)
        ·
          refine ⟨1005392428019378720081783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 670261618679585813387855 1005392428019378720081783)
          ·
            refine ⟨1508088642029068080122675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1005392428019378720081783 1508088642029068080122675)
            ·
              refine ⟨2262132963043602120184013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1508088642029068080122675 2262132963043602120184013)
              ·
                refine ⟨848299861141350795069005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2262132963043602120184013 848299861141350795069005)
                ·
                  refine ⟨318112447928006548150877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 848299861141350795069005 318112447928006548150877)
                  ·
                    rfl

theorem cell20_696962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 3, 3].length) (baseStart_696962 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_696962 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_696962 prefixEnd_696962 := by exact prefixLift 696962
  have htrace : WordTrace (prefixWord ++ tailWord_696962) baseStart_696962 baseEnd_696962 := by
    simpa [prefixWord, tailWord_696962, baseEnd_696962] using wordTrace_append hprefix tailTrace_696962
  have hstable : (prefixWord ++ tailWord_696962).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696962).length < 2 ^ (prefixWord ++ tailWord_696962).sum := by decide
  have hdescent : baseEnd_696962 < baseStart_696962 := by decide
  rcases family_descends (prefixWord ++ tailWord_696962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_696984 : List Nat := [2, 1, 2, 4, 1, 1, 1, 8]
def baseStart_696984 : Nat := 118140960795 + 696984 * 2 ^ 59
def prefixEnd_696984 : Nat := 4983230072969 + 3 ^ 40 * 696984 * 2
def baseEnd_696984 : Nat := 106040829775824083139151

theorem tailTrace_696984 : CollatzResearch.WordTrace tailWord_696984 prefixEnd_696984 106040829775824083139151 := by
  unfold tailWord_696984
  simp only [CollatzResearch.WordTrace]
  refine ⟨12710547453476739117709003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16947396604635652156945337 12710547453476739117709003)
  ·
    refine ⟨19065821180215108676563505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12710547453476739117709003 19065821180215108676563505)
    ·
      refine ⟨14299365885161331507422629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19065821180215108676563505 14299365885161331507422629)
      ·
        refine ⟨2681131103467749657641743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14299365885161331507422629 2681131103467749657641743)
        ·
          refine ⟨4021696655201624486462615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2681131103467749657641743 4021696655201624486462615)
          ·
            refine ⟨6032544982802436729693923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4021696655201624486462615 6032544982802436729693923)
            ·
              refine ⟨9048817474203655094540885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6032544982802436729693923 9048817474203655094540885)
              ·
                refine ⟨106040829775824083139151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9048817474203655094540885 106040829775824083139151)
                ·
                  rfl

theorem cell20_696984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 8].length) (baseStart_696984 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_696984 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_696984 prefixEnd_696984 := by exact prefixLift 696984
  have htrace : WordTrace (prefixWord ++ tailWord_696984) baseStart_696984 baseEnd_696984 := by
    simpa [prefixWord, tailWord_696984, baseEnd_696984] using wordTrace_append hprefix tailTrace_696984
  have hstable : (prefixWord ++ tailWord_696984).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_696984).length < 2 ^ (prefixWord ++ tailWord_696984).sum := by decide
  have hdescent : baseEnd_696984 < baseStart_696984 := by decide
  rcases family_descends (prefixWord ++ tailWord_696984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697011 : List Nat := [1, 1, 1, 2, 3, 4, 4, 2, 2]
def baseStart_697011 : Nat := 118140960795 + 697011 * 2 ^ 59
def prefixEnd_697011 : Nat := 4983230072969 + 3 ^ 40 * 697011 * 2
def baseEnd_697011 : Nat := 318134812863180155517343

theorem tailTrace_697011 : CollatzResearch.WordTrace tailWord_697011 prefixEnd_697011 318134812863180155517343 := by
  unfold tailWord_697011
  simp only [CollatzResearch.WordTrace]
  refine ⟨25422079677855661846650887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16948053118570441231100591 25422079677855661846650887)
  ·
    refine ⟨38133119516783492769976331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25422079677855661846650887 38133119516783492769976331)
    ·
      refine ⟨57199679275175239154964497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38133119516783492769976331 57199679275175239154964497)
      ·
        refine ⟨42899759456381429366223373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57199679275175239154964497 42899759456381429366223373)
        ·
          refine ⟨16087409796143036012333765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42899759456381429366223373 16087409796143036012333765)
          ·
            refine ⟨3016389336776819252312581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16087409796143036012333765 3016389336776819252312581)
            ·
              refine ⟨565573000645653609808609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3016389336776819252312581 565573000645653609808609)
              ·
                refine ⟨424179750484240207356457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 565573000645653609808609 424179750484240207356457)
                ·
                  refine ⟨318134812863180155517343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 424179750484240207356457 318134812863180155517343)
                  ·
                    rfl

theorem cell20_697011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 4, 2, 2].length) (baseStart_697011 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_697011 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_697011 prefixEnd_697011 := by exact prefixLift 697011
  have htrace : WordTrace (prefixWord ++ tailWord_697011) baseStart_697011 baseEnd_697011 := by
    simpa [prefixWord, tailWord_697011, baseEnd_697011] using wordTrace_append hprefix tailTrace_697011
  have hstable : (prefixWord ++ tailWord_697011).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697011).length < 2 ^ (prefixWord ++ tailWord_697011).sum := by decide
  have hdescent : baseEnd_697011 < baseStart_697011 := by decide
  rcases family_descends (prefixWord ++ tailWord_697011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697014 : List Nat := [5, 1, 3, 1, 3, 1, 1, 5]
def baseStart_697014 : Nat := 118140960795 + 697014 * 2 ^ 59
def prefixEnd_697014 : Nat := 4983230072969 + 3 ^ 40 * 697014 * 2
def baseEnd_697014 : Nat := 106045394048308492805777

theorem tailTrace_697014 : CollatzResearch.WordTrace tailWord_697014 prefixEnd_697014 106045394048308492805777 := by
  unfold tailWord_697014
  simp only [CollatzResearch.WordTrace]
  refine ⟨1588886818552799584938131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16948126064563195572673397 1588886818552799584938131)
  ·
    refine ⟨2383330227829199377407197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1588886818552799584938131 2383330227829199377407197)
    ·
      refine ⟨893748835435949766527699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2383330227829199377407197 893748835435949766527699)
      ·
        refine ⟨1340623253153924649791549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 893748835435949766527699 1340623253153924649791549)
        ·
          refine ⟨502733719932721743671831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1340623253153924649791549 502733719932721743671831)
          ·
            refine ⟨754100579899082615507747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 502733719932721743671831 754100579899082615507747)
            ·
              refine ⟨1131150869848623923261621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 754100579899082615507747 1131150869848623923261621)
              ·
                refine ⟨106045394048308492805777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1131150869848623923261621 106045394048308492805777)
                ·
                  rfl

theorem cell20_697014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 1, 5].length) (baseStart_697014 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_697014 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_697014 prefixEnd_697014 := by exact prefixLift 697014
  have htrace : WordTrace (prefixWord ++ tailWord_697014) baseStart_697014 baseEnd_697014 := by
    simpa [prefixWord, tailWord_697014, baseEnd_697014] using wordTrace_append hprefix tailTrace_697014
  have hstable : (prefixWord ++ tailWord_697014).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697014).length < 2 ^ (prefixWord ++ tailWord_697014).sum := by decide
  have hdescent : baseEnd_697014 < baseStart_697014 := by decide
  rcases family_descends (prefixWord ++ tailWord_697014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697060 : List Nat := [2, 3, 1, 1, 1, 5, 7]
def baseStart_697060 : Nat := 118140960795 + 697060 * 2 ^ 59
def prefixEnd_697060 : Nat := 4983230072969 + 3 ^ 40 * 697060 * 2
def baseEnd_697060 : Nat := 35350797533150418098201

theorem tailTrace_697060 : CollatzResearch.WordTrace tailWord_697060 prefixEnd_697060 35350797533150418098201 := by
  unfold tailWord_697060
  simp only [CollatzResearch.WordTrace]
  refine ⟨12711933427339071607592317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16949244569785428810123089 12711933427339071607592317)
  ·
    refine ⟨4766975035252151852847119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12711933427339071607592317 4766975035252151852847119)
    ·
      refine ⟨7150462552878227779270679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4766975035252151852847119 7150462552878227779270679)
      ·
        refine ⟨10725693829317341668906019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7150462552878227779270679 10725693829317341668906019)
        ·
          refine ⟨16088540743976012503359029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10725693829317341668906019 16088540743976012503359029)
          ·
            refine ⟨1508300694747751172189909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16088540743976012503359029 1508300694747751172189909)
            ·
              refine ⟨35350797533150418098201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1508300694747751172189909 35350797533150418098201)
              ·
                rfl

theorem cell20_697060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 7].length) (baseStart_697060 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_697060 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_697060 prefixEnd_697060 := by exact prefixLift 697060
  have htrace : WordTrace (prefixWord ++ tailWord_697060) baseStart_697060 baseEnd_697060 := by
    simpa [prefixWord, tailWord_697060, baseEnd_697060] using wordTrace_append hprefix tailTrace_697060
  have hstable : (prefixWord ++ tailWord_697060).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697060).length < 2 ^ (prefixWord ++ tailWord_697060).sum := by decide
  have hdescent : baseEnd_697060 < baseStart_697060 := by decide
  rcases family_descends (prefixWord ++ tailWord_697060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697070 : List Nat := [4, 1, 2, 1, 1, 4, 2, 1, 4]
def baseStart_697070 : Nat := 118140960795 + 697070 * 2 ^ 59
def prefixEnd_697070 : Nat := 4983230072969 + 3 ^ 40 * 697070 * 2
def baseEnd_697070 : Nat := 318161742070838172550435

theorem tailTrace_697070 : CollatzResearch.WordTrace tailWord_697070 prefixEnd_697070 318161742070838172550435 := by
  unfold tailWord_697070
  simp only [CollatzResearch.WordTrace]
  refine ⟨3178028948080239365381083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16949487723094609948699109 3178028948080239365381083)
  ·
    refine ⟨4767043422120359048071625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3178028948080239365381083 4767043422120359048071625)
    ·
      refine ⟨3575282566590269286053719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4767043422120359048071625 3575282566590269286053719)
      ·
        refine ⟨5362923849885403929080579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3575282566590269286053719 5362923849885403929080579)
        ·
          refine ⟨8044385774828105893620869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5362923849885403929080579 8044385774828105893620869)
          ·
            refine ⟨1508322332780269855053913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8044385774828105893620869 1508322332780269855053913)
            ·
              refine ⟨1131241749585202391290435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1508322332780269855053913 1131241749585202391290435)
              ·
                refine ⟨1696862624377803586935653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1131241749585202391290435 1696862624377803586935653)
                ·
                  refine ⟨318161742070838172550435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1696862624377803586935653 318161742070838172550435)
                  ·
                    rfl

theorem cell20_697070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 2, 1, 4].length) (baseStart_697070 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_697070 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_697070 prefixEnd_697070 := by exact prefixLift 697070
  have htrace : WordTrace (prefixWord ++ tailWord_697070) baseStart_697070 baseEnd_697070 := by
    simpa [prefixWord, tailWord_697070, baseEnd_697070] using wordTrace_append hprefix tailTrace_697070
  have hstable : (prefixWord ++ tailWord_697070).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697070).length < 2 ^ (prefixWord ++ tailWord_697070).sum := by decide
  have hdescent : baseEnd_697070 < baseStart_697070 := by decide
  rcases family_descends (prefixWord ++ tailWord_697070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697076 : List Nat := [2, 6, 1, 1, 2, 1, 3, 1, 3]
def baseStart_697076 : Nat := 118140960795 + 697076 * 2 ^ 59
def prefixEnd_697076 : Nat := 4983230072969 + 3 ^ 40 * 697076 * 2
def baseEnd_697076 : Nat := 318164480634328818350411

theorem tailTrace_697076 : CollatzResearch.WordTrace tailWord_697076 prefixEnd_697076 318164480634328818350411 := by
  unfold tailWord_697076
  simp only [CollatzResearch.WordTrace]
  refine ⟨12712225211310088973883541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16949633615080118631844721 12712225211310088973883541)
  ·
    refine ⟨595885556780160420650791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 12712225211310088973883541 595885556780160420650791)
    ·
      refine ⟨893828335170240630976187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 595885556780160420650791 893828335170240630976187)
      ·
        refine ⟨1340742502755360946464281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 893828335170240630976187 1340742502755360946464281)
        ·
          refine ⟨1005556877066520709848211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1340742502755360946464281 1005556877066520709848211)
          ·
            refine ⟨1508335315599781064772317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1005556877066520709848211 1508335315599781064772317)
            ·
              refine ⟨565625743349917899289619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1508335315599781064772317 565625743349917899289619)
              ·
                refine ⟨848438615024876848934429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 565625743349917899289619 848438615024876848934429)
                ·
                  refine ⟨318164480634328818350411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 848438615024876848934429 318164480634328818350411)
                  ·
                    rfl

theorem cell20_697076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_697076 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_697076 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_697076 prefixEnd_697076 := by exact prefixLift 697076
  have htrace : WordTrace (prefixWord ++ tailWord_697076) baseStart_697076 baseEnd_697076 := by
    simpa [prefixWord, tailWord_697076, baseEnd_697076] using wordTrace_append hprefix tailTrace_697076
  have hstable : (prefixWord ++ tailWord_697076).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697076).length < 2 ^ (prefixWord ++ tailWord_697076).sum := by decide
  have hdescent : baseEnd_697076 < baseStart_697076 := by decide
  rcases family_descends (prefixWord ++ tailWord_697076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697098 : List Nat := [3, 1, 2, 2, 1, 2, 3, 6]
def baseStart_697098 : Nat := 118140960795 + 697098 * 2 ^ 59
def prefixEnd_697098 : Nat := 4983230072969 + 3 ^ 40 * 697098 * 2
def baseEnd_697098 : Nat := 106058174011264839872329

theorem tailTrace_697098 : CollatzResearch.WordTrace tailWord_697098 prefixEnd_697098 106058174011264839872329 := by
  unfold tailWord_697098
  simp only [CollatzResearch.WordTrace]
  refine ⟨6356313207135118926266987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16950168552360317136711965 6356313207135118926266987)
  ·
    refine ⟨9534469810702678389400481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6356313207135118926266987 9534469810702678389400481)
    ·
      refine ⟨7150852358027008792050361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9534469810702678389400481 7150852358027008792050361)
      ·
        refine ⟨5363139268520256594037771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7150852358027008792050361 5363139268520256594037771)
        ·
          refine ⟨8044708902780384891056657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5363139268520256594037771 8044708902780384891056657)
          ·
            refine ⟨6033531677085288668292493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8044708902780384891056657 6033531677085288668292493)
            ·
              refine ⟨2262574378906983250609685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6033531677085288668292493 2262574378906983250609685)
              ·
                refine ⟨106058174011264839872329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2262574378906983250609685 106058174011264839872329)
                ·
                  rfl

theorem cell20_697098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 6].length) (baseStart_697098 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_697098 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_697098 prefixEnd_697098 := by exact prefixLift 697098
  have htrace : WordTrace (prefixWord ++ tailWord_697098) baseStart_697098 baseEnd_697098 := by
    simpa [prefixWord, tailWord_697098, baseEnd_697098] using wordTrace_append hprefix tailTrace_697098
  have hstable : (prefixWord ++ tailWord_697098).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697098).length < 2 ^ (prefixWord ++ tailWord_697098).sum := by decide
  have hdescent : baseEnd_697098 < baseStart_697098 := by decide
  rcases family_descends (prefixWord ++ tailWord_697098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697105 : List Nat := [1, 2, 2, 1, 1, 3, 3, 2, 5]
def baseStart_697105 : Nat := 118140960795 + 697105 * 2 ^ 59
def prefixEnd_697105 : Nat := 4983230072969 + 3 ^ 40 * 697105 * 2
def baseEnd_697105 : Nat := 318177717024533606383625

theorem tailTrace_697105 : CollatzResearch.WordTrace tailWord_697105 prefixEnd_697105 318177717024533606383625 := by
  unfold tailWord_697105
  simp only [CollatzResearch.WordTrace]
  refine ⟨25425508139515115900572769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16950338759676743933715179 25425508139515115900572769)
  ·
    refine ⟨19069131104636336925429577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25425508139515115900572769 19069131104636336925429577)
    ·
      refine ⟨14301848328477252694072183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19069131104636336925429577 14301848328477252694072183)
      ·
        refine ⟨21452772492715879041108275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14301848328477252694072183 21452772492715879041108275)
        ·
          refine ⟨32179158739073818561662413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21452772492715879041108275 32179158739073818561662413)
          ·
            refine ⟨12067184527152681960623405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32179158739073818561662413 12067184527152681960623405)
            ·
              refine ⟨4525194197682255735233777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12067184527152681960623405 4525194197682255735233777)
              ·
                refine ⟨3393895648261691801425333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4525194197682255735233777 3393895648261691801425333)
                ·
                  refine ⟨318177717024533606383625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3393895648261691801425333 318177717024533606383625)
                  ·
                    rfl

theorem cell20_697105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 2, 5].length) (baseStart_697105 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_697105 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_697105 prefixEnd_697105 := by exact prefixLift 697105
  have htrace : WordTrace (prefixWord ++ tailWord_697105) baseStart_697105 baseEnd_697105 := by
    simpa [prefixWord, tailWord_697105, baseEnd_697105] using wordTrace_append hprefix tailTrace_697105
  have hstable : (prefixWord ++ tailWord_697105).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697105).length < 2 ^ (prefixWord ++ tailWord_697105).sum := by decide
  have hdescent : baseEnd_697105 < baseStart_697105 := by decide
  rcases family_descends (prefixWord ++ tailWord_697105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697122 : List Nat := [3, 3, 1, 1, 2, 2, 2, 1, 5]
def baseStart_697122 : Nat := 118140960795 + 697122 * 2 ^ 59
def prefixEnd_697122 : Nat := 4983230072969 + 3 ^ 40 * 697122 * 2
def baseEnd_697122 : Nat := 318185476287757102816889

theorem tailTrace_697122 : CollatzResearch.WordTrace tailWord_697122 prefixEnd_697122 318185476287757102816889 := by
  unfold tailWord_697122
  simp only [CollatzResearch.WordTrace]
  refine ⟨6356532045113381950985405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16950752120302351869294413 6356532045113381950985405)
  ·
    refine ⟨2383699516917518231619527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6356532045113381950985405 2383699516917518231619527)
    ·
      refine ⟨3575549275376277347429291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2383699516917518231619527 3575549275376277347429291)
      ·
        refine ⟨5363323913064416021143937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3575549275376277347429291 5363323913064416021143937)
        ·
          refine ⟨4022492934798312015857953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5363323913064416021143937 4022492934798312015857953)
          ·
            refine ⟨3016869701098734011893465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4022492934798312015857953 3016869701098734011893465)
            ·
              refine ⟨2262652275824050508920099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3016869701098734011893465 2262652275824050508920099)
              ·
                refine ⟨3393978413736075763380149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2262652275824050508920099 3393978413736075763380149)
                ·
                  refine ⟨318185476287757102816889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3393978413736075763380149 318185476287757102816889)
                  ·
                    rfl

theorem cell20_697122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_697122 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_697122 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_697122 prefixEnd_697122 := by exact prefixLift 697122
  have htrace : WordTrace (prefixWord ++ tailWord_697122) baseStart_697122 baseEnd_697122 := by
    simpa [prefixWord, tailWord_697122, baseEnd_697122] using wordTrace_append hprefix tailTrace_697122
  have hstable : (prefixWord ++ tailWord_697122).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697122).length < 2 ^ (prefixWord ++ tailWord_697122).sum := by decide
  have hdescent : baseEnd_697122 < baseStart_697122 := by decide
  rcases family_descends (prefixWord ++ tailWord_697122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697125 : List Nat := [1, 3, 1, 2, 3, 1, 5, 2, 2]
def baseStart_697125 : Nat := 118140960795 + 697125 * 2 ^ 59
def prefixEnd_697125 : Nat := 4983230072969 + 3 ^ 40 * 697125 * 2
def baseEnd_697125 : Nat := 318186845569502425716877

theorem tailTrace_697125 : CollatzResearch.WordTrace tailWord_697125 prefixEnd_697125 318186845569502425716877 := by
  unfold tailWord_697125
  simp only [CollatzResearch.WordTrace]
  refine ⟨25426237599442659316300829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16950825066295106210867219 25426237599442659316300829)
  ·
    refine ⟨9534839099790997243612811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25426237599442659316300829 9534839099790997243612811)
    ·
      refine ⟨14302258649686495865419217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9534839099790997243612811 14302258649686495865419217)
      ·
        refine ⟨10726693987264871899064413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14302258649686495865419217 10726693987264871899064413)
        ·
          refine ⟨4022510245224326962149155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10726693987264871899064413 4022510245224326962149155)
          ·
            refine ⟨6033765367836490443223733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4022510245224326962149155 6033765367836490443223733)
            ·
              refine ⟨565665503234670979052225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6033765367836490443223733 565665503234670979052225)
              ·
                refine ⟨424249127426003234289169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 565665503234670979052225 424249127426003234289169)
                ·
                  refine ⟨318186845569502425716877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 424249127426003234289169 318186845569502425716877)
                  ·
                    rfl

theorem cell20_697125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 5, 2, 2].length) (baseStart_697125 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_697125 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_697125 prefixEnd_697125 := by exact prefixLift 697125
  have htrace : WordTrace (prefixWord ++ tailWord_697125) baseStart_697125 baseEnd_697125 := by
    simpa [prefixWord, tailWord_697125, baseEnd_697125] using wordTrace_append hprefix tailTrace_697125
  have hstable : (prefixWord ++ tailWord_697125).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697125).length < 2 ^ (prefixWord ++ tailWord_697125).sum := by decide
  have hdescent : baseEnd_697125 < baseStart_697125 := by decide
  rcases family_descends (prefixWord ++ tailWord_697125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697139 : List Nat := [1, 1, 1, 2, 6, 1, 4, 1, 3]
def baseStart_697139 : Nat := 118140960795 + 697139 * 2 ^ 59
def prefixEnd_697139 : Nat := 4983230072969 + 3 ^ 40 * 697139 * 2
def baseEnd_697139 : Nat := 318193235550980599250153

theorem tailTrace_697139 : CollatzResearch.WordTrace tailWord_697139 prefixEnd_697139 318193235550980599250153 := by
  unfold tailWord_697139
  simp only [CollatzResearch.WordTrace]
  refine ⟨25426748221391939707310471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16951165480927959804873647 25426748221391939707310471)
  ·
    refine ⟨38140122332087909560965707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25426748221391939707310471 38140122332087909560965707)
    ·
      refine ⟨57210183498131864341448561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38140122332087909560965707 57210183498131864341448561)
      ·
        refine ⟨42907637623598898256086421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57210183498131864341448561 42907637623598898256086421)
        ·
          refine ⟨2011295513606198355754051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 42907637623598898256086421 2011295513606198355754051)
          ·
            refine ⟨3016943270409297533631077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2011295513606198355754051 3016943270409297533631077)
            ·
              refine ⟨565676863201743287555827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3016943270409297533631077 565676863201743287555827)
              ·
                refine ⟨848515294802614931333741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 565676863201743287555827 848515294802614931333741)
                ·
                  refine ⟨318193235550980599250153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 848515294802614931333741 318193235550980599250153)
                  ·
                    rfl

theorem cell20_697139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 4, 1, 3].length) (baseStart_697139 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_697139 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_697139 prefixEnd_697139 := by exact prefixLift 697139
  have htrace : WordTrace (prefixWord ++ tailWord_697139) baseStart_697139 baseEnd_697139 := by
    simpa [prefixWord, tailWord_697139, baseEnd_697139] using wordTrace_append hprefix tailTrace_697139
  have hstable : (prefixWord ++ tailWord_697139).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697139).length < 2 ^ (prefixWord ++ tailWord_697139).sum := by decide
  have hdescent : baseEnd_697139 < baseStart_697139 := by decide
  rcases family_descends (prefixWord ++ tailWord_697139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697174 : List Nat := [5, 2, 13]
def baseStart_697174 : Nat := 118140960795 + 697174 * 2 ^ 59
def prefixEnd_697174 : Nat := 4983230072969 + 3 ^ 40 * 697174 * 2
def baseEnd_697174 : Nat := 436500974629185230567

theorem tailTrace_697174 : CollatzResearch.WordTrace tailWord_697174 prefixEnd_697174 436500974629185230567 := by
  unfold tailWord_697174
  simp only [CollatzResearch.WordTrace]
  refine ⟨1589251548516571292802161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16952016517510093789889717 1589251548516571292802161)
  ·
    refine ⟨1191938661387428469601621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1589251548516571292802161 1191938661387428469601621)
    ·
      refine ⟨436500974629185230567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 13 1191938661387428469601621 436500974629185230567)
      ·
        rfl

theorem cell20_697174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 13].length) (baseStart_697174 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_697174 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_697174 prefixEnd_697174 := by exact prefixLift 697174
  have htrace : WordTrace (prefixWord ++ tailWord_697174) baseStart_697174 baseEnd_697174 := by
    simpa [prefixWord, tailWord_697174, baseEnd_697174] using wordTrace_append hprefix tailTrace_697174
  have hstable : (prefixWord ++ tailWord_697174).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697174).length < 2 ^ (prefixWord ++ tailWord_697174).sum := by decide
  have hdescent : baseEnd_697174 < baseStart_697174 := by decide
  rcases family_descends (prefixWord ++ tailWord_697174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697180 : List Nat := [2, 2, 4, 2, 1, 1, 4, 2, 2]
def baseStart_697180 : Nat := 118140960795 + 697180 * 2 ^ 59
def prefixEnd_697180 : Nat := 4983230072969 + 3 ^ 40 * 697180 * 2
def baseEnd_697180 : Nat := 318211949068166678883319

theorem tailTrace_697180 : CollatzResearch.WordTrace tailWord_697180 prefixEnd_697180 318211949068166678883319 := by
  unfold tailWord_697180
  simp only [CollatzResearch.WordTrace]
  refine ⟨12714121807121701854776497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16952162409495602473035329 12714121807121701854776497)
  ·
    refine ⟨9535591355341276391082373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12714121807121701854776497 9535591355341276391082373)
    ·
      refine ⟨1787923379126489323327945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9535591355341276391082373 1787923379126489323327945)
      ·
        refine ⟨1340942534344866992495959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1787923379126489323327945 1340942534344866992495959)
        ·
          refine ⟨2011413801517300488743939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1340942534344866992495959 2011413801517300488743939)
          ·
            refine ⟨3017120702275950733115909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2011413801517300488743939 3017120702275950733115909)
            ·
              refine ⟨565710131676740762459233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3017120702275950733115909 565710131676740762459233)
              ·
                refine ⟨424282598757555571844425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 565710131676740762459233 424282598757555571844425)
                ·
                  refine ⟨318211949068166678883319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 424282598757555571844425 318211949068166678883319)
                  ·
                    rfl

theorem cell20_697180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 4, 2, 2].length) (baseStart_697180 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_697180 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_697180 prefixEnd_697180 := by exact prefixLift 697180
  have htrace : WordTrace (prefixWord ++ tailWord_697180) baseStart_697180 baseEnd_697180 := by
    simpa [prefixWord, tailWord_697180, baseEnd_697180] using wordTrace_append hprefix tailTrace_697180
  have hstable : (prefixWord ++ tailWord_697180).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697180).length < 2 ^ (prefixWord ++ tailWord_697180).sum := by decide
  have hdescent : baseEnd_697180 < baseStart_697180 := by decide
  rcases family_descends (prefixWord ++ tailWord_697180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697184 : List Nat := [2, 1, 1, 3, 3, 1, 3, 4, 2]
def baseStart_697184 : Nat := 118140960795 + 697184 * 2 ^ 59
def prefixEnd_697184 : Nat := 4983230072969 + 3 ^ 40 * 697184 * 2
def baseEnd_697184 : Nat := 318213774777160442749969

theorem tailTrace_697184 : CollatzResearch.WordTrace tailWord_697184 prefixEnd_697184 318213774777160442749969 := by
  unfold tailWord_697184
  simp only [CollatzResearch.WordTrace]
  refine ⟨12714194753114456196349303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16952259670819274928465737 12714194753114456196349303)
  ·
    refine ⟨19071292129671684294523955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12714194753114456196349303 19071292129671684294523955)
    ·
      refine ⟨28606938194507526441785933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19071292129671684294523955 28606938194507526441785933)
      ·
        refine ⟨10727601822940322415669725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28606938194507526441785933 10727601822940322415669725)
        ·
          refine ⟨4022850683602620905876147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10727601822940322415669725 4022850683602620905876147)
          ·
            refine ⟨6034276025403931358814221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4022850683602620905876147 6034276025403931358814221)
            ·
              refine ⟨2262853509526474259555333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6034276025403931358814221 2262853509526474259555333)
              ·
                refine ⟨424285033036213923666625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2262853509526474259555333 424285033036213923666625)
                ·
                  refine ⟨318213774777160442749969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 424285033036213923666625 318213774777160442749969)
                  ·
                    rfl

theorem cell20_697184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 4, 2].length) (baseStart_697184 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_697184 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_697184 prefixEnd_697184 := by exact prefixLift 697184
  have htrace : WordTrace (prefixWord ++ tailWord_697184) baseStart_697184 baseEnd_697184 := by
    simpa [prefixWord, tailWord_697184, baseEnd_697184] using wordTrace_append hprefix tailTrace_697184
  have hstable : (prefixWord ++ tailWord_697184).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697184).length < 2 ^ (prefixWord ++ tailWord_697184).sum := by decide
  have hdescent : baseEnd_697184 < baseStart_697184 := by decide
  rcases family_descends (prefixWord ++ tailWord_697184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697191 : List Nat := [1, 1, 5, 1, 2, 4, 1, 5]
def baseStart_697191 : Nat := 118140960795 + 697191 * 2 ^ 59
def prefixEnd_697191 : Nat := 4983230072969 + 3 ^ 40 * 697191 * 2
def baseEnd_697191 : Nat := 106072323255966509838869

theorem tailTrace_697191 : CollatzResearch.WordTrace tailWord_697191 prefixEnd_697191 106072323255966509838869 := by
  unfold tailWord_697191
  simp only [CollatzResearch.WordTrace]
  refine ⟨25428644817203552588203427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16952429878135701725468951 25428644817203552588203427)
  ·
    refine ⟨38142967225805328882305141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25428644817203552588203427 38142967225805328882305141)
    ·
      refine ⟨3575903177419249582716107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 38142967225805328882305141 3575903177419249582716107)
      ·
        refine ⟨5363854766128874374074161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3575903177419249582716107 5363854766128874374074161)
        ·
          refine ⟨4022891074596655780555621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5363854766128874374074161 4022891074596655780555621)
          ·
            refine ⟨754292076486872958854179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4022891074596655780555621 754292076486872958854179)
            ·
              refine ⟨1131438114730309438281269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 754292076486872958854179 1131438114730309438281269)
              ·
                refine ⟨106072323255966509838869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1131438114730309438281269 106072323255966509838869)
                ·
                  rfl

theorem cell20_697191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 1, 5].length) (baseStart_697191 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_697191 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_697191 prefixEnd_697191 := by exact prefixLift 697191
  have htrace : WordTrace (prefixWord ++ tailWord_697191) baseStart_697191 baseEnd_697191 := by
    simpa [prefixWord, tailWord_697191, baseEnd_697191] using wordTrace_append hprefix tailTrace_697191
  have hstable : (prefixWord ++ tailWord_697191).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697191).length < 2 ^ (prefixWord ++ tailWord_697191).sum := by decide
  have hdescent : baseEnd_697191 < baseStart_697191 := by decide
  rcases family_descends (prefixWord ++ tailWord_697191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697205 : List Nat := [1, 3, 4, 1, 1, 2, 1, 1, 6]
def baseStart_697205 : Nat := 118140960795 + 697205 * 2 ^ 59
def prefixEnd_697205 : Nat := 4983230072969 + 3 ^ 40 * 697205 * 2
def baseEnd_697205 : Nat := 318223359749377703049883

theorem tailTrace_697205 : CollatzResearch.WordTrace tailWord_697205 prefixEnd_697205 318223359749377703049883 := by
  unfold tailWord_697205
  simp only [CollatzResearch.WordTrace]
  refine ⟨25429155439152832979213069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16952770292768555319475379 25429155439152832979213069)
  ·
    refine ⟨9535933289682312367204901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25429155439152832979213069 9535933289682312367204901)
    ·
      refine ⟨1787987491815433568850919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9535933289682312367204901 1787987491815433568850919)
      ·
        refine ⟨2681981237723150353276379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1787987491815433568850919 2681981237723150353276379)
        ·
          refine ⟨4022971856584725529914569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2681981237723150353276379 4022971856584725529914569)
          ·
            refine ⟨3017228892438544147435927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4022971856584725529914569 3017228892438544147435927)
            ·
              refine ⟨4525843338657816221153891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3017228892438544147435927 4525843338657816221153891)
              ·
                refine ⟨6788765007986724331730837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4525843338657816221153891 6788765007986724331730837)
                ·
                  refine ⟨318223359749377703049883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6788765007986724331730837 318223359749377703049883)
                  ·
                    rfl

theorem cell20_697205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 1, 6].length) (baseStart_697205 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_697205 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_697205 prefixEnd_697205 := by exact prefixLift 697205
  have htrace : WordTrace (prefixWord ++ tailWord_697205) baseStart_697205 baseEnd_697205 := by
    simpa [prefixWord, tailWord_697205, baseEnd_697205] using wordTrace_append hprefix tailTrace_697205
  have hstable : (prefixWord ++ tailWord_697205).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697205).length < 2 ^ (prefixWord ++ tailWord_697205).sum := by decide
  have hdescent : baseEnd_697205 < baseStart_697205 := by decide
  rcases family_descends (prefixWord ++ tailWord_697205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697219 : List Nat := [1, 1, 1, 3, 4, 1, 2, 2, 5]
def baseStart_697219 : Nat := 118140960795 + 697219 * 2 ^ 59
def prefixEnd_697219 : Nat := 4983230072969 + 3 ^ 40 * 697219 * 2
def baseEnd_697219 : Nat := 318229749730855876583159

theorem tailTrace_697219 : CollatzResearch.WordTrace tailWord_697219 prefixEnd_697219 318229749730855876583159 := by
  unfold tailWord_697219
  simp only [CollatzResearch.WordTrace]
  refine ⟨25429666061102113370222711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16953110707401408913481807 25429666061102113370222711)
  ·
    refine ⟨38144499091653170055334067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25429666061102113370222711 38144499091653170055334067)
    ·
      refine ⟨57216748637479755083001101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38144499091653170055334067 57216748637479755083001101)
      ·
        refine ⟨21456280739054908156125413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57216748637479755083001101 21456280739054908156125413)
        ·
          refine ⟨4023052638572795279273515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21456280739054908156125413 4023052638572795279273515)
          ·
            refine ⟨6034578957859192918910273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4023052638572795279273515 6034578957859192918910273)
            ·
              refine ⟨4525934218394394689182705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6034578957859192918910273 4525934218394394689182705)
              ·
                refine ⟨3394450663795796016887029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4525934218394394689182705 3394450663795796016887029)
                ·
                  refine ⟨318229749730855876583159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3394450663795796016887029 318229749730855876583159)
                  ·
                    rfl

theorem cell20_697219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 2, 5].length) (baseStart_697219 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_697219 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_697219 prefixEnd_697219 := by exact prefixLift 697219
  have htrace : WordTrace (prefixWord ++ tailWord_697219) baseStart_697219 baseEnd_697219 := by
    simpa [prefixWord, tailWord_697219, baseEnd_697219] using wordTrace_append hprefix tailTrace_697219
  have hstable : (prefixWord ++ tailWord_697219).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697219).length < 2 ^ (prefixWord ++ tailWord_697219).sum := by decide
  have hdescent : baseEnd_697219 < baseStart_697219 := by decide
  rcases family_descends (prefixWord ++ tailWord_697219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697236 : List Nat := [2, 4, 2, 1, 1, 1, 3, 1, 5]
def baseStart_697236 : Nat := 118140960795 + 697236 * 2 ^ 59
def prefixEnd_697236 : Nat := 4983230072969 + 3 ^ 40 * 697236 * 2
def baseEnd_697236 : Nat := 318237508994079373016423

theorem tailTrace_697236 : CollatzResearch.WordTrace tailWord_697236 prefixEnd_697236 318237508994079373016423 := by
  unfold tailWord_697236
  simp only [CollatzResearch.WordTrace]
  refine ⟨12715143051020262636795781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16953524068027016849061041 12715143051020262636795781)
  ·
    refine ⟨2384089322066299244399209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12715143051020262636795781 2384089322066299244399209)
    ·
      refine ⟨1788066991549724433299407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2384089322066299244399209 1788066991549724433299407)
      ·
        refine ⟨2682100487324586649949111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1788066991549724433299407 2682100487324586649949111)
        ·
          refine ⟨4023150730986879974923667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2682100487324586649949111 4023150730986879974923667)
          ·
            refine ⟨6034726096480319962385501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4023150730986879974923667 6034726096480319962385501)
            ·
              refine ⟨2263022286180119985894563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6034726096480319962385501 2263022286180119985894563)
              ·
                refine ⟨3394533429270179978841845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2263022286180119985894563 3394533429270179978841845)
                ·
                  refine ⟨318237508994079373016423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3394533429270179978841845 318237508994079373016423)
                  ·
                    rfl

theorem cell20_697236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_697236 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_697236 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_697236 prefixEnd_697236 := by exact prefixLift 697236
  have htrace : WordTrace (prefixWord ++ tailWord_697236) baseStart_697236 baseEnd_697236 := by
    simpa [prefixWord, tailWord_697236, baseEnd_697236] using wordTrace_append hprefix tailTrace_697236
  have hstable : (prefixWord ++ tailWord_697236).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697236).length < 2 ^ (prefixWord ++ tailWord_697236).sum := by decide
  have hdescent : baseEnd_697236 < baseStart_697236 := by decide
  rcases family_descends (prefixWord ++ tailWord_697236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697284 : List Nat := [2, 3, 3, 3, 1, 2, 6]
def baseStart_697284 : Nat := 118140960795 + 697284 * 2 ^ 59
def prefixEnd_697284 : Nat := 4983230072969 + 3 ^ 40 * 697284 * 2
def baseEnd_697284 : Nat := 35362157500222726601803

theorem tailTrace_697284 : CollatzResearch.WordTrace tailWord_697284 prefixEnd_697284 35362157500222726601803 := by
  unfold tailWord_697284
  simp only [CollatzResearch.WordTrace]
  refine ⟨12716018402933314735669453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16954691203911086314225937 12716018402933314735669453)
  ·
    refine ⟨4768506901099993025876045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12716018402933314735669453 4768506901099993025876045)
    ·
      refine ⟨1788190087912497384703517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4768506901099993025876045 1788190087912497384703517)
      ·
        refine ⟨670571282967186519263819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1788190087912497384703517 670571282967186519263819)
        ·
          refine ⟨1005856924450779778895729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 670571282967186519263819 1005856924450779778895729)
          ·
            refine ⟨754392693338084834171797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1005856924450779778895729 754392693338084834171797)
            ·
              refine ⟨35362157500222726601803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 754392693338084834171797 35362157500222726601803)
              ·
                rfl

theorem cell20_697284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 6].length) (baseStart_697284 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_697284 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_697284 prefixEnd_697284 := by exact prefixLift 697284
  have htrace : WordTrace (prefixWord ++ tailWord_697284) baseStart_697284 baseEnd_697284 := by
    simpa [prefixWord, tailWord_697284, baseEnd_697284] using wordTrace_append hprefix tailTrace_697284
  have hstable : (prefixWord ++ tailWord_697284).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697284).length < 2 ^ (prefixWord ++ tailWord_697284).sum := by decide
  have hdescent : baseEnd_697284 < baseStart_697284 := by decide
  rcases family_descends (prefixWord ++ tailWord_697284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697295 : List Nat := [1, 1, 2, 1, 1, 6, 2, 1, 5]
def baseStart_697295 : Nat := 118140960795 + 697295 * 2 ^ 59
def prefixEnd_697295 : Nat := 4983230072969 + 3 ^ 40 * 697295 * 2
def baseEnd_697295 : Nat := 318264438201737390049515

theorem tailTrace_697295 : CollatzResearch.WordTrace tailWord_697295 prefixEnd_697295 318264438201737390049515 := by
  unfold tailWord_697295
  simp only [CollatzResearch.WordTrace]
  refine ⟨25432438008826778349989339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16954958672551185566659559 25432438008826778349989339)
  ·
    refine ⟨38148657013240167524984009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25432438008826778349989339 38148657013240167524984009)
    ·
      refine ⟨28611492759930125643738007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38148657013240167524984009 28611492759930125643738007)
      ·
        refine ⟨42917239139895188465607011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28611492759930125643738007 42917239139895188465607011)
        ·
          refine ⟨64375858709842782698410517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42917239139895188465607011 64375858709842782698410517)
          ·
            refine ⟨3017618377023880438987993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 64375858709842782698410517 3017618377023880438987993)
            ·
              refine ⟨2263213782767910329240995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3017618377023880438987993 2263213782767910329240995)
              ·
                refine ⟨3394820674151865493861493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2263213782767910329240995 3394820674151865493861493)
                ·
                  refine ⟨318264438201737390049515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3394820674151865493861493 318264438201737390049515)
                  ·
                    rfl

theorem cell20_697295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 1, 5].length) (baseStart_697295 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_697295 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_697295 prefixEnd_697295 := by exact prefixLift 697295
  have htrace : WordTrace (prefixWord ++ tailWord_697295) baseStart_697295 baseEnd_697295 := by
    simpa [prefixWord, tailWord_697295, baseEnd_697295] using wordTrace_append hprefix tailTrace_697295
  have hstable : (prefixWord ++ tailWord_697295).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697295).length < 2 ^ (prefixWord ++ tailWord_697295).sum := by decide
  have hdescent : baseEnd_697295 < baseStart_697295 := by decide
  rcases family_descends (prefixWord ++ tailWord_697295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697298 : List Nat := [3, 2, 2, 3, 1, 1, 3, 1, 4]
def baseStart_697298 : Nat := 118140960795 + 697298 * 2 ^ 59
def prefixEnd_697298 : Nat := 4983230072969 + 3 ^ 40 * 697298 * 2
def baseEnd_697298 : Nat := 318265807483482712949503

theorem tailTrace_697298 : CollatzResearch.WordTrace tailWord_697298 prefixEnd_697298 318265807483482712949503 := by
  unfold tailWord_697298
  simp only [CollatzResearch.WordTrace]
  refine ⟨6358136856953977465587137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16955031618543939908232365 6358136856953977465587137)
  ·
    refine ⟨4768602642715483099190353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6358136856953977465587137 4768602642715483099190353)
    ·
      refine ⟨3576451982036612324392765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4768602642715483099190353 3576451982036612324392765)
      ·
        refine ⟨1341169493263729621647287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3576451982036612324392765 1341169493263729621647287)
        ·
          refine ⟨2011754239895594432470931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1341169493263729621647287 2011754239895594432470931)
          ·
            refine ⟨3017631359843391648706397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2011754239895594432470931 3017631359843391648706397)
            ·
              refine ⟨1131611759941271868264899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3017631359843391648706397 1131611759941271868264899)
              ·
                refine ⟨1697417639911907802397349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1131611759941271868264899 1697417639911907802397349)
                ·
                  refine ⟨318265807483482712949503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1697417639911907802397349 318265807483482712949503)
                  ·
                    rfl

theorem cell20_697298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 3, 1, 4].length) (baseStart_697298 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_697298 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_697298 prefixEnd_697298 := by exact prefixLift 697298
  have htrace : WordTrace (prefixWord ++ tailWord_697298) baseStart_697298 baseEnd_697298 := by
    simpa [prefixWord, tailWord_697298, baseEnd_697298] using wordTrace_append hprefix tailTrace_697298
  have hstable : (prefixWord ++ tailWord_697298).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697298).length < 2 ^ (prefixWord ++ tailWord_697298).sum := by decide
  have hdescent : baseEnd_697298 < baseStart_697298 := by decide
  rcases family_descends (prefixWord ++ tailWord_697298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697405 : List Nat := [1, 4, 1, 3, 1, 4, 1, 2, 3]
def baseStart_697405 : Nat := 118140960795 + 697405 * 2 ^ 59
def prefixEnd_697405 : Nat := 4983230072969 + 3 ^ 40 * 697405 * 2
def baseEnd_697405 : Nat := 318314645199065896382399

theorem tailTrace_697405 : CollatzResearch.WordTrace tailWord_697405 prefixEnd_697405 318314645199065896382399 := by
  unfold tailWord_697405
  simp only [CollatzResearch.WordTrace]
  refine ⟨25436450038428267136493669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16957633358952178090995779 25436450038428267136493669)
  ·
    refine ⟨4769334382205300088092563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25436450038428267136493669 4769334382205300088092563)
    ·
      refine ⟨7154001573307950132138845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4769334382205300088092563 7154001573307950132138845)
      ·
        refine ⟨2682750589990481299552067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7154001573307950132138845 2682750589990481299552067)
        ·
          refine ⟨4024125884985721949328101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2682750589990481299552067 4024125884985721949328101)
          ·
            refine ⟨754523603434822865499019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4024125884985721949328101 754523603434822865499019)
            ·
              refine ⟨1131785405152234298248529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 754523603434822865499019 1131785405152234298248529)
              ·
                refine ⟨848839053864175723686397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1131785405152234298248529 848839053864175723686397)
                ·
                  refine ⟨318314645199065896382399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 848839053864175723686397 318314645199065896382399)
                  ·
                    rfl

theorem cell20_697405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 1, 2, 3].length) (baseStart_697405 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_697405 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_697405 prefixEnd_697405 := by exact prefixLift 697405
  have htrace : WordTrace (prefixWord ++ tailWord_697405) baseStart_697405 baseEnd_697405 := by
    simpa [prefixWord, tailWord_697405, baseEnd_697405] using wordTrace_append hprefix tailTrace_697405
  have hstable : (prefixWord ++ tailWord_697405).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697405).length < 2 ^ (prefixWord ++ tailWord_697405).sum := by decide
  have hdescent : baseEnd_697405 < baseStart_697405 := by decide
  rcases family_descends (prefixWord ++ tailWord_697405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697447 : List Nat := [1, 1, 5, 1, 1, 3, 1, 2, 5]
def baseStart_697447 : Nat := 118140960795 + 697447 * 2 ^ 59
def prefixEnd_697447 : Nat := 4983230072969 + 3 ^ 40 * 697447 * 2
def baseEnd_697447 : Nat := 318333815143500416982227

theorem tailTrace_697447 : CollatzResearch.WordTrace tailWord_697447 prefixEnd_697447 318333815143500416982227 := by
  unfold tailWord_697447
  simp only [CollatzResearch.WordTrace]
  refine ⟨25437981904276108309522595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16958654602850738873015063 25437981904276108309522595)
  ·
    refine ⟨38156972856414162464283893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25437981904276108309522595 38156972856414162464283893)
    ·
      refine ⟨3577216205288827731026615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 38156972856414162464283893 3577216205288827731026615)
      ·
        refine ⟨5365824307933241596539923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3577216205288827731026615 5365824307933241596539923)
        ·
          refine ⟨8048736461899862394809885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5365824307933241596539923 8048736461899862394809885)
          ·
            refine ⟨3018276173212448398053707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8048736461899862394809885 3018276173212448398053707)
            ·
              refine ⟨4527414259818672597080561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3018276173212448398053707 4527414259818672597080561)
              ·
                refine ⟨3395560694864004447810421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4527414259818672597080561 3395560694864004447810421)
                ·
                  refine ⟨318333815143500416982227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3395560694864004447810421 318333815143500416982227)
                  ·
                    rfl

theorem cell20_697447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 2, 5].length) (baseStart_697447 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_697447 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_697447 prefixEnd_697447 := by exact prefixLift 697447
  have htrace : WordTrace (prefixWord ++ tailWord_697447) baseStart_697447 baseEnd_697447 := by
    simpa [prefixWord, tailWord_697447, baseEnd_697447] using wordTrace_append hprefix tailTrace_697447
  have hstable : (prefixWord ++ tailWord_697447).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697447).length < 2 ^ (prefixWord ++ tailWord_697447).sum := by decide
  have hdescent : baseEnd_697447 < baseStart_697447 := by decide
  rcases family_descends (prefixWord ++ tailWord_697447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697481 : List Nat := [1, 2, 1, 1, 4, 5, 2, 1, 3]
def baseStart_697481 : Nat := 118140960795 + 697481 * 2 ^ 59
def prefixEnd_697481 : Nat := 4983230072969 + 3 ^ 40 * 697481 * 2
def baseEnd_697481 : Nat := 318349333669947409848755

theorem tailTrace_697481 : CollatzResearch.WordTrace tailWord_697481 prefixEnd_697481 318349333669947409848755 := by
  unfold tailWord_697481
  simp only [CollatzResearch.WordTrace]
  refine ⟨25439221986152932116260297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16959481324101954744173531 25439221986152932116260297)
  ·
    refine ⟨19079416489614699087195223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25439221986152932116260297 19079416489614699087195223)
    ·
      refine ⟨28619124734422048630792835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19079416489614699087195223 28619124734422048630792835)
      ·
        refine ⟨42928687101633072946189253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28619124734422048630792835 42928687101633072946189253)
        ·
          refine ⟨8049128831556201177410485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42928687101633072946189253 8049128831556201177410485)
          ·
            refine ⟨754605827958393860382233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8049128831556201177410485 754605827958393860382233)
            ·
              refine ⟨565954370968795395286675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 754605827958393860382233 565954370968795395286675)
              ·
                refine ⟨848931556453193092930013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 565954370968795395286675 848931556453193092930013)
                ·
                  refine ⟨318349333669947409848755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 848931556453193092930013 318349333669947409848755)
                  ·
                    rfl

theorem cell20_697481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 2, 1, 3].length) (baseStart_697481 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_697481 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_697481 prefixEnd_697481 := by exact prefixLift 697481
  have htrace : WordTrace (prefixWord ++ tailWord_697481) baseStart_697481 baseEnd_697481 := by
    simpa [prefixWord, tailWord_697481, baseEnd_697481] using wordTrace_append hprefix tailTrace_697481
  have hstable : (prefixWord ++ tailWord_697481).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697481).length < 2 ^ (prefixWord ++ tailWord_697481).sum := by decide
  have hdescent : baseEnd_697481 < baseStart_697481 := by decide
  rcases family_descends (prefixWord ++ tailWord_697481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697523 : List Nat := [1, 1, 1, 2, 3, 2, 3, 4, 3]
def baseStart_697523 : Nat := 118140960795 + 697523 * 2 ^ 59
def prefixEnd_697523 : Nat := 4983230072969 + 3 ^ 40 * 697523 * 2
def baseEnd_697523 : Nat := 318368503614381930448583

theorem tailTrace_697523 : CollatzResearch.WordTrace tailWord_697523 prefixEnd_697523 318368503614381930448583 := by
  unfold tailWord_697523
  simp only [CollatzResearch.WordTrace]
  refine ⟨25440753852000773289289223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16960502568000515526192815 25440753852000773289289223)
  ·
    refine ⟨38161130778001159933933835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25440753852000773289289223 38161130778001159933933835)
    ·
      refine ⟨57241696167001739900900753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38161130778001159933933835 57241696167001739900900753)
      ·
        refine ⟨42931272125251304925675565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57241696167001739900900753 42931272125251304925675565)
        ·
          refine ⟨16099227046969239347128337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42931272125251304925675565 16099227046969239347128337)
          ·
            refine ⟨12074420285226929510346253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16099227046969239347128337 12074420285226929510346253)
            ·
              refine ⟨4527907606960098566379845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12074420285226929510346253 4527907606960098566379845)
              ·
                refine ⟨848982676305018481196221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4527907606960098566379845 848982676305018481196221)
                ·
                  refine ⟨318368503614381930448583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 848982676305018481196221 318368503614381930448583)
                  ·
                    rfl

theorem cell20_697523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 4, 3].length) (baseStart_697523 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_697523 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_697523 prefixEnd_697523 := by exact prefixLift 697523
  have htrace : WordTrace (prefixWord ++ tailWord_697523) baseStart_697523 baseEnd_697523 := by
    simpa [prefixWord, tailWord_697523, baseEnd_697523] using wordTrace_append hprefix tailTrace_697523
  have hstable : (prefixWord ++ tailWord_697523).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697523).length < 2 ^ (prefixWord ++ tailWord_697523).sum := by decide
  have hdescent : baseEnd_697523 < baseStart_697523 := by decide
  rcases family_descends (prefixWord ++ tailWord_697523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697530 : List Nat := [3, 1, 1, 1, 2, 2, 1, 5, 4]
def baseStart_697530 : Nat := 118140960795 + 697530 * 2 ^ 59
def prefixEnd_697530 : Nat := 4983230072969 + 3 ^ 40 * 697530 * 2
def baseEnd_697530 : Nat := 318371698605121017215221

theorem tailTrace_697530 : CollatzResearch.WordTrace tailWord_697530 prefixEnd_697530 318371698605121017215221 := by
  unfold tailWord_697530
  simp only [CollatzResearch.WordTrace]
  refine ⟨6360252290743853371198511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16960672775316942323196029 6360252290743853371198511)
  ·
    refine ⟨9540378436115780056797767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6360252290743853371198511 9540378436115780056797767)
    ·
      refine ⟨14310567654173670085196651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9540378436115780056797767 14310567654173670085196651)
      ·
        refine ⟨21465851481260505127794977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14310567654173670085196651 21465851481260505127794977)
        ·
          refine ⟨16099388610945378845846233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21465851481260505127794977 16099388610945378845846233)
          ·
            refine ⟨12074541458209034134384675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16099388610945378845846233 12074541458209034134384675)
            ·
              refine ⟨18111812187313551201577013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12074541458209034134384675 18111812187313551201577013)
              ·
                refine ⟨1697982392560645425147845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18111812187313551201577013 1697982392560645425147845)
                ·
                  refine ⟨318371698605121017215221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1697982392560645425147845 318371698605121017215221)
                  ·
                    rfl

theorem cell20_697530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 5, 4].length) (baseStart_697530 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_697530 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_697530 prefixEnd_697530 := by exact prefixLift 697530
  have htrace : WordTrace (prefixWord ++ tailWord_697530) baseStart_697530 baseEnd_697530 := by
    simpa [prefixWord, tailWord_697530, baseEnd_697530] using wordTrace_append hprefix tailTrace_697530
  have hstable : (prefixWord ++ tailWord_697530).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697530).length < 2 ^ (prefixWord ++ tailWord_697530).sum := by decide
  have hdescent : baseEnd_697530 < baseStart_697530 := by decide
  rcases family_descends (prefixWord ++ tailWord_697530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697578 : List Nat := [3, 1, 3, 1, 1, 3, 3, 2, 3]
def baseStart_697578 : Nat := 118140960795 + 697578 * 2 ^ 59
def prefixEnd_697578 : Nat := 4983230072969 + 3 ^ 40 * 697578 * 2
def baseEnd_697578 : Nat := 318393607113046183615025

theorem tailTrace_697578 : CollatzResearch.WordTrace tailWord_697578 prefixEnd_697578 318393607113046183615025 := by
  unfold tailWord_697578
  simp only [CollatzResearch.WordTrace]
  refine ⟨6360689966700379420635347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16961839911201011788360925 6360689966700379420635347)
  ·
    refine ⟨9541034950050569130953021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6360689966700379420635347 9541034950050569130953021)
    ·
      refine ⟨3577888106268963424107383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9541034950050569130953021 3577888106268963424107383)
      ·
        refine ⟨5366832159403445136161075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3577888106268963424107383 5366832159403445136161075)
        ·
          refine ⟨8050248239105167704241613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5366832159403445136161075 8050248239105167704241613)
          ·
            refine ⟨3018843089664437889090605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8050248239105167704241613 3018843089664437889090605)
            ·
              refine ⟨1132066158624164208408977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3018843089664437889090605 1132066158624164208408977)
              ·
                refine ⟨849049618968123156306733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1132066158624164208408977 849049618968123156306733)
                ·
                  refine ⟨318393607113046183615025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 849049618968123156306733 318393607113046183615025)
                  ·
                    rfl

theorem cell20_697578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 3, 2, 3].length) (baseStart_697578 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_697578 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_697578 prefixEnd_697578 := by exact prefixLift 697578
  have htrace : WordTrace (prefixWord ++ tailWord_697578) baseStart_697578 baseEnd_697578 := by
    simpa [prefixWord, tailWord_697578, baseEnd_697578] using wordTrace_append hprefix tailTrace_697578
  have hstable : (prefixWord ++ tailWord_697578).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697578).length < 2 ^ (prefixWord ++ tailWord_697578).sum := by decide
  have hdescent : baseEnd_697578 < baseStart_697578 := by decide
  rcases family_descends (prefixWord ++ tailWord_697578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697637 : List Nat := [1, 3, 1, 2, 4, 1, 2, 1, 5]
def baseStart_697637 : Nat := 118140960795 + 697637 * 2 ^ 59
def prefixEnd_697637 : Nat := 4983230072969 + 3 ^ 40 * 697637 * 2
def baseEnd_697637 : Nat := 318420536320704200648117

theorem tailTrace_697637 : CollatzResearch.WordTrace tailWord_697637 prefixEnd_697637 318420536320704200648117 := by
  unfold tailWord_697637
  simp only [CollatzResearch.WordTrace]
  refine ⟨25444911773587770758939165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16963274515725180505959443 25444911773587770758939165)
  ·
    refine ⟨9541841915095414034602187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25444911773587770758939165 9541841915095414034602187)
    ·
      refine ⟨14312762872643121051903281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9541841915095414034602187 14312762872643121051903281)
      ·
        refine ⟨10734572154482340788927461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14312762872643121051903281 10734572154482340788927461)
        ·
          refine ⟨2012732278965438897923899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10734572154482340788927461 2012732278965438897923899)
          ·
            refine ⟨3019098418448158346885849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2012732278965438897923899 3019098418448158346885849)
            ·
              refine ⟨2264323813836118760164387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3019098418448158346885849 2264323813836118760164387)
              ·
                refine ⟨3396485720754178140246581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2264323813836118760164387 3396485720754178140246581)
                ·
                  refine ⟨318420536320704200648117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3396485720754178140246581 318420536320704200648117)
                  ·
                    rfl

theorem cell20_697637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 1, 5].length) (baseStart_697637 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_697637 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_697637 prefixEnd_697637 := by exact prefixLift 697637
  have htrace : WordTrace (prefixWord ++ tailWord_697637) baseStart_697637 baseEnd_697637 := by
    simpa [prefixWord, tailWord_697637, baseEnd_697637] using wordTrace_append hprefix tailTrace_697637
  have hstable : (prefixWord ++ tailWord_697637).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697637).length < 2 ^ (prefixWord ++ tailWord_697637).sum := by decide
  have hdescent : baseEnd_697637 < baseStart_697637 := by decide
  rcases family_descends (prefixWord ++ tailWord_697637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697640 : List Nat := [2, 1, 5, 1, 2, 3, 1, 1, 4]
def baseStart_697640 : Nat := 118140960795 + 697640 * 2 ^ 59
def prefixEnd_697640 : Nat := 4983230072969 + 3 ^ 40 * 697640 * 2
def baseEnd_697640 : Nat := 318421905602449523548105

theorem tailTrace_697640 : CollatzResearch.WordTrace tailWord_697640 prefixEnd_697640 318421905602449523548105 := by
  unfold tailWord_697640
  simp only [CollatzResearch.WordTrace]
  refine ⟨12722510596288451135649187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16963347461717934847532249 12722510596288451135649187)
  ·
    refine ⟨19083765894432676703473781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12722510596288451135649187 19083765894432676703473781)
    ·
      refine ⟨1789103052603063440950667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19083765894432676703473781 1789103052603063440950667)
      ·
        refine ⟨2683654578904595161426001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1789103052603063440950667 2683654578904595161426001)
        ·
          refine ⟨2012740934178446371069501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2683654578904595161426001 2012740934178446371069501)
          ·
            refine ⟨754777850316917389151063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2012740934178446371069501 754777850316917389151063)
            ·
              refine ⟨1132166775475376083726595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 754777850316917389151063 1132166775475376083726595)
              ·
                refine ⟨1698250163213064125589893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1132166775475376083726595 1698250163213064125589893)
                ·
                  refine ⟨318421905602449523548105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1698250163213064125589893 318421905602449523548105)
                  ·
                    rfl

theorem cell20_697640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 1, 1, 4].length) (baseStart_697640 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_697640 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_697640 prefixEnd_697640 := by exact prefixLift 697640
  have htrace : WordTrace (prefixWord ++ tailWord_697640) baseStart_697640 baseEnd_697640 := by
    simpa [prefixWord, tailWord_697640, baseEnd_697640] using wordTrace_append hprefix tailTrace_697640
  have hstable : (prefixWord ++ tailWord_697640).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697640).length < 2 ^ (prefixWord ++ tailWord_697640).sum := by decide
  have hdescent : baseEnd_697640 < baseStart_697640 := by decide
  rcases family_descends (prefixWord ++ tailWord_697640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697651 : List Nat := [1, 1, 1, 2, 5, 2, 1, 7]
def baseStart_697651 : Nat := 118140960795 + 697651 * 2 ^ 59
def prefixEnd_697651 : Nat := 4983230072969 + 3 ^ 40 * 697651 * 2
def baseEnd_697651 : Nat := 106142308767394124727131

theorem tailTrace_697651 : CollatzResearch.WordTrace tailWord_697651 prefixEnd_697651 106142308767394124727131 := by
  unfold tailWord_697651
  simp only [CollatzResearch.WordTrace]
  refine ⟨25445422395537051149948807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16963614930358034099965871 25445422395537051149948807)
  ·
    refine ⟨38168133593305576724923211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25445422395537051149948807 38168133593305576724923211)
    ·
      refine ⟨57252200389958365087384817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38168133593305576724923211 57252200389958365087384817)
      ·
        refine ⟨42939150292468773815538613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57252200389958365087384817 42939150292468773815538613)
        ·
          refine ⟨4025545339918947545206745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42939150292468773815538613 4025545339918947545206745)
          ·
            refine ⟨3019159004939210658905059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4025545339918947545206745 3019159004939210658905059)
            ·
              refine ⟨4528738507408815988357589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3019159004939210658905059 4528738507408815988357589)
              ·
                refine ⟨106142308767394124727131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4528738507408815988357589 106142308767394124727131)
                ·
                  rfl

theorem cell20_697651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 7].length) (baseStart_697651 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_697651 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_697651 prefixEnd_697651 := by exact prefixLift 697651
  have htrace : WordTrace (prefixWord ++ tailWord_697651) baseStart_697651 baseEnd_697651 := by
    simpa [prefixWord, tailWord_697651, baseEnd_697651] using wordTrace_append hprefix tailTrace_697651
  have hstable : (prefixWord ++ tailWord_697651).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697651).length < 2 ^ (prefixWord ++ tailWord_697651).sum := by decide
  have hdescent : baseEnd_697651 < baseStart_697651 := by decide
  rcases family_descends (prefixWord ++ tailWord_697651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697713 : List Nat := [1, 2, 2, 2, 1, 2, 4, 3, 3]
def baseStart_697713 : Nat := 118140960795 + 697713 * 2 ^ 59
def prefixEnd_697713 : Nat := 4983230072969 + 3 ^ 40 * 697713 * 2
def baseEnd_697713 : Nat := 318455224791585714114473

theorem tailTrace_697713 : CollatzResearch.WordTrace tailWord_697713 prefixEnd_697713 318455224791585714114473 := by
  unfold tailWord_697713
  simp only [CollatzResearch.WordTrace]
  refine ⟨25447683721312435738705793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16965122480874957159137195 25447683721312435738705793)
  ·
    refine ⟨19085762790984326804029345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25447683721312435738705793 19085762790984326804029345)
    ·
      refine ⟨14314322093238245103022009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19085762790984326804029345 14314322093238245103022009)
      ·
        refine ⟨10735741569928683827266507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14314322093238245103022009 10735741569928683827266507)
        ·
          refine ⟨16103612354893025740899761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10735741569928683827266507 16103612354893025740899761)
          ·
            refine ⟨12077709266169769305674821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16103612354893025740899761 12077709266169769305674821)
            ·
              refine ⟨2264570487406831744814029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12077709266169769305674821 2264570487406831744814029)
              ·
                refine ⟨849213932777561904305261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2264570487406831744814029 849213932777561904305261)
                ·
                  refine ⟨318455224791585714114473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 849213932777561904305261 318455224791585714114473)
                  ·
                    rfl

theorem cell20_697713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 3, 3].length) (baseStart_697713 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_697713 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_697713 prefixEnd_697713 := by exact prefixLift 697713
  have htrace : WordTrace (prefixWord ++ tailWord_697713) baseStart_697713 baseEnd_697713 := by
    simpa [prefixWord, tailWord_697713, baseEnd_697713] using wordTrace_append hprefix tailTrace_697713
  have hstable : (prefixWord ++ tailWord_697713).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697713).length < 2 ^ (prefixWord ++ tailWord_697713).sum := by decide
  have hdescent : baseEnd_697713 < baseStart_697713 := by decide
  rcases family_descends (prefixWord ++ tailWord_697713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697788 : List Nat := [2, 2, 2, 4, 3, 1, 1, 3, 2]
def baseStart_697788 : Nat := 118140960795 + 697788 * 2 ^ 59
def prefixEnd_697788 : Nat := 4983230072969 + 3 ^ 40 * 697788 * 2
def baseEnd_697788 : Nat := 318489456835218786614167

theorem tailTrace_697788 : CollatzResearch.WordTrace tailWord_697788 prefixEnd_697788 318489456835218786614167 := by
  unfold tailWord_697788
  simp only [CollatzResearch.WordTrace]
  refine ⟨12725209598020361773843009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16966946130693815698457345 12725209598020361773843009)
  ·
    refine ⟨9543907198515271330382257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12725209598020361773843009 9543907198515271330382257)
    ·
      refine ⟨7157930398886453497786693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9543907198515271330382257 7157930398886453497786693)
      ·
        refine ⟨1342111949791210030835005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7157930398886453497786693 1342111949791210030835005)
        ·
          refine ⟨503291981171703761563127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1342111949791210030835005 503291981171703761563127)
          ·
            refine ⟨754937971757555642344691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 503291981171703761563127 754937971757555642344691)
            ·
              refine ⟨1132406957636333463517037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 754937971757555642344691 1132406957636333463517037)
              ·
                refine ⟨424652609113625048818889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1132406957636333463517037 424652609113625048818889)
                ·
                  refine ⟨318489456835218786614167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 424652609113625048818889 318489456835218786614167)
                  ·
                    rfl

theorem cell20_697788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 1, 3, 2].length) (baseStart_697788 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_697788 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_697788 prefixEnd_697788 := by exact prefixLift 697788
  have htrace : WordTrace (prefixWord ++ tailWord_697788) baseStart_697788 baseEnd_697788 := by
    simpa [prefixWord, tailWord_697788, baseEnd_697788] using wordTrace_append hprefix tailTrace_697788
  have hstable : (prefixWord ++ tailWord_697788).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697788).length < 2 ^ (prefixWord ++ tailWord_697788).sum := by decide
  have hdescent : baseEnd_697788 < baseStart_697788 := by decide
  rcases family_descends (prefixWord ++ tailWord_697788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697841 : List Nat := [1, 2, 2, 2, 3, 2, 2, 6]
def baseStart_697841 : Nat := 118140960795 + 697841 * 2 ^ 59
def prefixEnd_697841 : Nat := 4983230072969 + 3 ^ 40 * 697841 * 2
def baseEnd_697841 : Nat := 106171215826462052615761

theorem tailTrace_697841 : CollatzResearch.WordTrace tailWord_697841 prefixEnd_697841 106171215826462052615761 := by
  unfold tailWord_697841
  simp only [CollatzResearch.WordTrace]
  refine ⟨25452352264848713599365377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16968234843232475732910251 25452352264848713599365377)
  ·
    refine ⟨19089264198636535199524033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25452352264848713599365377 19089264198636535199524033)
    ·
      refine ⟨14316948148977401399643025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19089264198636535199524033 14316948148977401399643025)
      ·
        refine ⟨10737711111733051049732269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14316948148977401399643025 10737711111733051049732269)
        ·
          refine ⟨4026641666899894143649601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10737711111733051049732269 4026641666899894143649601)
          ·
            refine ⟨3019981250174920607737201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4026641666899894143649601 3019981250174920607737201)
            ·
              refine ⟨2264985937631190455802901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3019981250174920607737201 2264985937631190455802901)
              ·
                refine ⟨106171215826462052615761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2264985937631190455802901 106171215826462052615761)
                ·
                  rfl

theorem cell20_697841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 6].length) (baseStart_697841 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_697841 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_697841 prefixEnd_697841 := by exact prefixLift 697841
  have htrace : WordTrace (prefixWord ++ tailWord_697841) baseStart_697841 baseEnd_697841 := by
    simpa [prefixWord, tailWord_697841, baseEnd_697841] using wordTrace_append hprefix tailTrace_697841
  have hstable : (prefixWord ++ tailWord_697841).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697841).length < 2 ^ (prefixWord ++ tailWord_697841).sum := by decide
  have hdescent : baseEnd_697841 < baseStart_697841 := by decide
  rcases family_descends (prefixWord ++ tailWord_697841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697855 : List Nat := [1, 1, 2, 2, 1, 2, 2, 1, 8]
def baseStart_697855 : Nat := 118140960795 + 697855 * 2 ^ 59
def prefixEnd_697855 : Nat := 4983230072969 + 3 ^ 40 * 697855 * 2
def baseEnd_697855 : Nat := 318520037460864331380559

theorem tailTrace_697855 : CollatzResearch.WordTrace tailWord_697855 prefixEnd_697855 318520037460864331380559 := by
  unfold tailWord_697855
  simp only [CollatzResearch.WordTrace]
  refine ⟨25452862886797993990375019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16968575257865329326916679 25452862886797993990375019)
  ·
    refine ⟨38179294330196990985562529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25452862886797993990375019 38179294330196990985562529)
    ·
      refine ⟨28634470747647743239171897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38179294330196990985562529 28634470747647743239171897)
      ·
        refine ⟨21475853060735807429378923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28634470747647743239171897 21475853060735807429378923)
        ·
          refine ⟨32213779591103711144068385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21475853060735807429378923 32213779591103711144068385)
          ·
            refine ⟨24160334693327783358051289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32213779591103711144068385 24160334693327783358051289)
            ·
              refine ⟨18120251019995837518538467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24160334693327783358051289 18120251019995837518538467)
              ·
                refine ⟨27180376529993756277807701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18120251019995837518538467 27180376529993756277807701)
                ·
                  refine ⟨318520037460864331380559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27180376529993756277807701 318520037460864331380559)
                  ·
                    rfl

theorem cell20_697855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 8].length) (baseStart_697855 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_697855 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_697855 prefixEnd_697855 := by exact prefixLift 697855
  have htrace : WordTrace (prefixWord ++ tailWord_697855) baseStart_697855 baseEnd_697855 := by
    simpa [prefixWord, tailWord_697855, baseEnd_697855] using wordTrace_append hprefix tailTrace_697855
  have hstable : (prefixWord ++ tailWord_697855).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697855).length < 2 ^ (prefixWord ++ tailWord_697855).sum := by decide
  have hdescent : baseEnd_697855 < baseStart_697855 := by decide
  rcases family_descends (prefixWord ++ tailWord_697855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697858 : List Nat := [3, 4, 1, 2, 1, 9]
def baseStart_697858 : Nat := 118140960795 + 697858 * 2 ^ 59
def prefixEnd_697858 : Nat := 4983230072969 + 3 ^ 40 * 697858 * 2
def baseEnd_697858 : Nat := 11797089138615172380761

theorem tailTrace_697858 : CollatzResearch.WordTrace tailWord_697858 prefixEnd_697858 11797089138615172380761 := by
  unfold tailWord_697858
  simp only [CollatzResearch.WordTrace]
  refine ⟨6363243076446781375683557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16968648203858083668489485 6363243076446781375683557)
  ·
    refine ⟨1193108076833771507940667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6363243076446781375683557 1193108076833771507940667)
    ·
      refine ⟨1789662115250657261911001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1193108076833771507940667 1789662115250657261911001)
      ·
        refine ⟨1342246586437992946433251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1789662115250657261911001 1342246586437992946433251)
        ·
          refine ⟨2013369879656989419649877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1342246586437992946433251 2013369879656989419649877)
          ·
            refine ⟨11797089138615172380761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2013369879656989419649877 11797089138615172380761)
            ·
              rfl

theorem cell20_697858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 9].length) (baseStart_697858 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_697858 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_697858 prefixEnd_697858 := by exact prefixLift 697858
  have htrace : WordTrace (prefixWord ++ tailWord_697858) baseStart_697858 baseEnd_697858 := by
    simpa [prefixWord, tailWord_697858, baseEnd_697858] using wordTrace_append hprefix tailTrace_697858
  have hstable : (prefixWord ++ tailWord_697858).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697858).length < 2 ^ (prefixWord ++ tailWord_697858).sum := by decide
  have hdescent : baseEnd_697858 < baseStart_697858 := by decide
  rcases family_descends (prefixWord ++ tailWord_697858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697865 : List Nat := [1, 2, 1, 1, 3, 1, 6, 2, 3]
def baseStart_697865 : Nat := 118140960795 + 697865 * 2 ^ 59
def prefixEnd_697865 : Nat := 4983230072969 + 3 ^ 40 * 697865 * 2
def baseEnd_697865 : Nat := 318524601733348741047185

theorem tailTrace_697865 : CollatzResearch.WordTrace tailWord_697865 prefixEnd_697865 318524601733348741047185 := by
  unfold tailWord_697865
  simp only [CollatzResearch.WordTrace]
  refine ⟨25453227616761765698239049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16968818411174510465492699 25453227616761765698239049)
  ·
    refine ⟨19089920712571324273679287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25453227616761765698239049 19089920712571324273679287)
    ·
      refine ⟨28634881068856986410518931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19089920712571324273679287 28634881068856986410518931)
      ·
        refine ⟨42952321603285479615778397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28634881068856986410518931 42952321603285479615778397)
        ·
          refine ⟨16107120601232054855916899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42952321603285479615778397 16107120601232054855916899)
          ·
            refine ⟨24160680901848082283875349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16107120601232054855916899 24160680901848082283875349)
            ·
              refine ⟨1132531917274128857056657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 24160680901848082283875349 1132531917274128857056657)
              ·
                refine ⟨849398937955596642792493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1132531917274128857056657 849398937955596642792493)
                ·
                  refine ⟨318524601733348741047185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 849398937955596642792493 318524601733348741047185)
                  ·
                    rfl

theorem cell20_697865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 6, 2, 3].length) (baseStart_697865 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_697865 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_697865 prefixEnd_697865 := by exact prefixLift 697865
  have htrace : WordTrace (prefixWord ++ tailWord_697865) baseStart_697865 baseEnd_697865 := by
    simpa [prefixWord, tailWord_697865, baseEnd_697865] using wordTrace_append hprefix tailTrace_697865
  have hstable : (prefixWord ++ tailWord_697865).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697865).length < 2 ^ (prefixWord ++ tailWord_697865).sum := by decide
  have hdescent : baseEnd_697865 < baseStart_697865 := by decide
  rcases family_descends (prefixWord ++ tailWord_697865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697868 : List Nat := [2, 2, 1, 2, 5, 1, 1, 4, 2]
def baseStart_697868 : Nat := 118140960795 + 697868 * 2 ^ 59
def prefixEnd_697868 : Nat := 4983230072969 + 3 ^ 40 * 697868 * 2
def baseEnd_697868 : Nat := 318525971015094063947173

theorem tailTrace_697868 : CollatzResearch.WordTrace tailWord_697868 prefixEnd_697868 318525971015094063947173 := by
  unfold tailWord_697868
  simp only [CollatzResearch.WordTrace]
  refine ⟨12726668517875448605299129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16968891357167264807065505 12726668517875448605299129)
  ·
    refine ⟨9545001388406586453974347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12726668517875448605299129 9545001388406586453974347)
    ·
      refine ⟨14317502082609879680961521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9545001388406586453974347 14317502082609879680961521)
      ·
        refine ⟨10738126561957409760721141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14317502082609879680961521 10738126561957409760721141)
        ·
          refine ⟨1006699365183507165067607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10738126561957409760721141 1006699365183507165067607)
          ·
            refine ⟨1510049047775260747601411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1006699365183507165067607 1510049047775260747601411)
            ·
              refine ⟨2265073571662891121402117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1510049047775260747601411 2265073571662891121402117)
              ·
                refine ⟨424701294686792085262897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2265073571662891121402117 424701294686792085262897)
                ·
                  refine ⟨318525971015094063947173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 424701294686792085262897 318525971015094063947173)
                  ·
                    rfl

theorem cell20_697868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 4, 2].length) (baseStart_697868 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_697868 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_697868 prefixEnd_697868 := by exact prefixLift 697868
  have htrace : WordTrace (prefixWord ++ tailWord_697868) baseStart_697868 baseEnd_697868 := by
    simpa [prefixWord, tailWord_697868, baseEnd_697868] using wordTrace_append hprefix tailTrace_697868
  have hstable : (prefixWord ++ tailWord_697868).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697868).length < 2 ^ (prefixWord ++ tailWord_697868).sum := by decide
  have hdescent : baseEnd_697868 < baseStart_697868 := by decide
  rcases family_descends (prefixWord ++ tailWord_697868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697927 : List Nat := [1, 1, 4, 1, 5, 1, 2, 1, 4]
def baseStart_697927 : Nat := 118140960795 + 697927 * 2 ^ 59
def prefixEnd_697927 : Nat := 4983230072969 + 3 ^ 40 * 697927 * 2
def baseEnd_697927 : Nat := 318552900222752080980265

theorem tailTrace_697927 : CollatzResearch.WordTrace tailWord_697927 prefixEnd_697927 318552900222752080980265 := by
  unfold tailWord_697927
  simp only [CollatzResearch.WordTrace]
  refine ⟨25455488942537150286996035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16970325961691433524664023 25455488942537150286996035)
  ·
    refine ⟨38183233413805725430494053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25455488942537150286996035 38183233413805725430494053)
    ·
      refine ⟨7159356265088573518217635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38183233413805725430494053 7159356265088573518217635)
      ·
        refine ⟨10739034397632860277326453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7159356265088573518217635 10739034397632860277326453)
        ·
          refine ⟨1006784474778080650999355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10739034397632860277326453 1006784474778080650999355)
          ·
            refine ⟨1510176712167120976499033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1006784474778080650999355 1510176712167120976499033)
            ·
              refine ⟨1132632534125340732374275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1510176712167120976499033 1132632534125340732374275)
              ·
                refine ⟨1698948801188011098561413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1132632534125340732374275 1698948801188011098561413)
                ·
                  refine ⟨318552900222752080980265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1698948801188011098561413 318552900222752080980265)
                  ·
                    rfl

theorem cell20_697927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 2, 1, 4].length) (baseStart_697927 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_697927 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_697927 prefixEnd_697927 := by exact prefixLift 697927
  have htrace : WordTrace (prefixWord ++ tailWord_697927) baseStart_697927 baseEnd_697927 := by
    simpa [prefixWord, tailWord_697927, baseEnd_697927] using wordTrace_append hprefix tailTrace_697927
  have hstable : (prefixWord ++ tailWord_697927).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697927).length < 2 ^ (prefixWord ++ tailWord_697927).sum := by decide
  have hdescent : baseEnd_697927 < baseStart_697927 := by decide
  rcases family_descends (prefixWord ++ tailWord_697927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697955 : List Nat := [1, 1, 1, 5, 1, 4, 1, 6]
def baseStart_697955 : Nat := 118140960795 + 697955 * 2 ^ 59
def prefixEnd_697955 : Nat := 4983230072969 + 3 ^ 40 * 697955 * 2
def baseEnd_697955 : Nat := 106188560061902809348939

theorem tailTrace_697955 : CollatzResearch.WordTrace tailWord_697955 prefixEnd_697955 106188560061902809348939 := by
  unfold tailWord_697955
  simp only [CollatzResearch.WordTrace]
  refine ⟨25456510186435711069015319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16971006790957140712676879 25456510186435711069015319)
  ·
    refine ⟨38184765279653566603522979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25456510186435711069015319 38184765279653566603522979)
    ·
      refine ⟨57277147919480349905284469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38184765279653566603522979 57277147919480349905284469)
      ·
        refine ⟨5369732617451282803620419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 57277147919480349905284469 5369732617451282803620419)
        ·
          refine ⟨8054598926176924205430629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5369732617451282803620419 8054598926176924205430629)
          ·
            refine ⟨1510237298658173288518243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8054598926176924205430629 1510237298658173288518243)
            ·
              refine ⟨2265355947987259932777365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1510237298658173288518243 2265355947987259932777365)
              ·
                refine ⟨106188560061902809348939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2265355947987259932777365 106188560061902809348939)
                ·
                  rfl

theorem cell20_697955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 6].length) (baseStart_697955 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_697955 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_697955 prefixEnd_697955 := by exact prefixLift 697955
  have htrace : WordTrace (prefixWord ++ tailWord_697955) baseStart_697955 baseEnd_697955 := by
    simpa [prefixWord, tailWord_697955, baseEnd_697955] using wordTrace_append hprefix tailTrace_697955
  have hstable : (prefixWord ++ tailWord_697955).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697955).length < 2 ^ (prefixWord ++ tailWord_697955).sum := by decide
  have hdescent : baseEnd_697955 < baseStart_697955 := by decide
  rcases family_descends (prefixWord ++ tailWord_697955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697969 : List Nat := [1, 2, 2, 2, 1, 1, 1, 4, 6]
def baseStart_697969 : Nat := 118140960795 + 697969 * 2 ^ 59
def prefixEnd_697969 : Nat := 4983230072969 + 3 ^ 40 * 697969 * 2
def baseEnd_697969 : Nat := 318572070167186601580093

theorem tailTrace_697969 : CollatzResearch.WordTrace tailWord_697969 prefixEnd_697969 318572070167186601580093 := by
  unfold tailWord_697969
  simp only [CollatzResearch.WordTrace]
  refine ⟨25457020808384991460024961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16971347205589994306683307 25457020808384991460024961)
  ·
    refine ⟨19092765606288743595018721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25457020808384991460024961 19092765606288743595018721)
    ·
      refine ⟨14319574204716557696264041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19092765606288743595018721 14319574204716557696264041)
      ·
        refine ⟨10739680653537418272198031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14319574204716557696264041 10739680653537418272198031)
        ·
          refine ⟨16109520980306127408297047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10739680653537418272198031 16109520980306127408297047)
          ·
            refine ⟨24164281470459191112445571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16109520980306127408297047 24164281470459191112445571)
            ·
              refine ⟨36246422205688786668668357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24164281470459191112445571 36246422205688786668668357)
              ·
                refine ⟨6796204163566647500375317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36246422205688786668668357 6796204163566647500375317)
                ·
                  refine ⟨318572070167186601580093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6796204163566647500375317 318572070167186601580093)
                  ·
                    rfl

theorem cell20_697969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 4, 6].length) (baseStart_697969 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_697969 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_697969 prefixEnd_697969 := by exact prefixLift 697969
  have htrace : WordTrace (prefixWord ++ tailWord_697969) baseStart_697969 baseEnd_697969 := by
    simpa [prefixWord, tailWord_697969, baseEnd_697969] using wordTrace_append hprefix tailTrace_697969
  have hstable : (prefixWord ++ tailWord_697969).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697969).length < 2 ^ (prefixWord ++ tailWord_697969).sum := by decide
  have hdescent : baseEnd_697969 < baseStart_697969 := by decide
  rcases family_descends (prefixWord ++ tailWord_697969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_697992 : List Nat := [2, 1, 3, 5, 1, 2, 2, 1, 3]
def baseStart_697992 : Nat := 118140960795 + 697992 * 2 ^ 59
def prefixEnd_697992 : Nat := 4983230072969 + 3 ^ 40 * 697992 * 2
def baseEnd_697992 : Nat := 318582567993900743813333

theorem tailTrace_697992 : CollatzResearch.WordTrace tailWord_697992 prefixEnd_697992 318582567993900743813333 := by
  unfold tailWord_697992
  simp only [CollatzResearch.WordTrace]
  refine ⟨12728929843650833194056115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16971906458201110925408153 12728929843650833194056115)
  ·
    refine ⟨19093394765476249791084173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12728929843650833194056115 19093394765476249791084173)
    ·
      refine ⟨7160023037053593671656565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19093394765476249791084173 7160023037053593671656565)
      ·
        refine ⟨671252159723774406717803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7160023037053593671656565 671252159723774406717803)
        ·
          refine ⟨1006878239585661610076705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 671252159723774406717803 1006878239585661610076705)
          ·
            refine ⟨755158679689246207557529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1006878239585661610076705 755158679689246207557529)
            ·
              refine ⟨566369009766934655668147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 755158679689246207557529 566369009766934655668147)
              ·
                refine ⟨849553514650401983502221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 566369009766934655668147 849553514650401983502221)
                ·
                  refine ⟨318582567993900743813333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 849553514650401983502221 318582567993900743813333)
                  ·
                    rfl

theorem cell20_697992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 2, 1, 3].length) (baseStart_697992 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_697992 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_697992 prefixEnd_697992 := by exact prefixLift 697992
  have htrace : WordTrace (prefixWord ++ tailWord_697992) baseStart_697992 baseEnd_697992 := by
    simpa [prefixWord, tailWord_697992, baseEnd_697992] using wordTrace_append hprefix tailTrace_697992
  have hstable : (prefixWord ++ tailWord_697992).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_697992).length < 2 ^ (prefixWord ++ tailWord_697992).sum := by decide
  have hdescent : baseEnd_697992 < baseStart_697992 := by decide
  rcases family_descends (prefixWord ++ tailWord_697992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698062 : List Nat := [4, 1, 1, 1, 3, 1, 3, 2, 4]
def baseStart_698062 : Nat := 118140960795 + 698062 * 2 ^ 59
def prefixEnd_698062 : Nat := 4983230072969 + 3 ^ 40 * 698062 * 2
def baseEnd_698062 : Nat := 318614517901291611479713

theorem tailTrace_698062 : CollatzResearch.WordTrace tailWord_698062 prefixEnd_698062 318614517901291611479713 := by
  unfold tailWord_698062
  simp only [CollatzResearch.WordTrace]
  refine ⟨3182551599631008542895055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16973608531365378895440293 3182551599631008542895055)
  ·
    refine ⟨4773827399446512814342583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3182551599631008542895055 4773827399446512814342583)
    ·
      refine ⟨7160741099169769221513875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4773827399446512814342583 7160741099169769221513875)
      ·
        refine ⟨10741111648754653832270813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7160741099169769221513875 10741111648754653832270813)
        ·
          refine ⟨4027916868282995187101555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10741111648754653832270813 4027916868282995187101555)
          ·
            refine ⟨6041875302424492780652333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4027916868282995187101555 6041875302424492780652333)
            ·
              refine ⟨2265703238409184792744625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6041875302424492780652333 2265703238409184792744625)
              ·
                refine ⟨1699277428806888594558469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2265703238409184792744625 1699277428806888594558469)
                ·
                  refine ⟨318614517901291611479713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1699277428806888594558469 318614517901291611479713)
                  ·
                    rfl

theorem cell20_698062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 2, 4].length) (baseStart_698062 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_698062 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_698062 prefixEnd_698062 := by exact prefixLift 698062
  have htrace : WordTrace (prefixWord ++ tailWord_698062) baseStart_698062 baseEnd_698062 := by
    simpa [prefixWord, tailWord_698062, baseEnd_698062] using wordTrace_append hprefix tailTrace_698062
  have hstable : (prefixWord ++ tailWord_698062).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698062).length < 2 ^ (prefixWord ++ tailWord_698062).sum := by decide
  have hdescent : baseEnd_698062 < baseStart_698062 := by decide
  rcases family_descends (prefixWord ++ tailWord_698062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698079 : List Nat := [1, 1, 2, 3, 2, 2, 4, 3, 2]
def baseStart_698079 : Nat := 118140960795 + 698079 * 2 ^ 59
def prefixEnd_698079 : Nat := 4983230072969 + 3 ^ 40 * 698079 * 2
def baseEnd_698079 : Nat := 318622277164515107912977

theorem tailTrace_698079 : CollatzResearch.WordTrace tailWord_698079 prefixEnd_698079 318622277164515107912977 := by
  unfold tailWord_698079
  simp only [CollatzResearch.WordTrace]
  refine ⟨25461032837986480246529291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16974021891990986831019527 25461032837986480246529291)
  ·
    refine ⟨38191549256979720369793937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25461032837986480246529291 38191549256979720369793937)
    ·
      refine ⟨28643661942734790277345453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38191549256979720369793937 28643661942734790277345453)
      ·
        refine ⟨10741373228525546354004545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28643661942734790277345453 10741373228525546354004545)
        ·
          refine ⟨8056029921394159765503409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10741373228525546354004545 8056029921394159765503409)
          ·
            refine ⟨6042022441045619824127557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8056029921394159765503409 6042022441045619824127557)
            ·
              refine ⟨1132879207696053717023917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6042022441045619824127557 1132879207696053717023917)
              ·
                refine ⟨424829702886020143883969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1132879207696053717023917 424829702886020143883969)
                ·
                  refine ⟨318622277164515107912977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 424829702886020143883969 318622277164515107912977)
                  ·
                    rfl

theorem cell20_698079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 4, 3, 2].length) (baseStart_698079 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_698079 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_698079 prefixEnd_698079 := by exact prefixLift 698079
  have htrace : WordTrace (prefixWord ++ tailWord_698079) baseStart_698079 baseEnd_698079 := by
    simpa [prefixWord, tailWord_698079, baseEnd_698079] using wordTrace_append hprefix tailTrace_698079
  have hstable : (prefixWord ++ tailWord_698079).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698079).length < 2 ^ (prefixWord ++ tailWord_698079).sum := by decide
  have hdescent : baseEnd_698079 < baseStart_698079 := by decide
  rcases family_descends (prefixWord ++ tailWord_698079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698093 : List Nat := [1, 5, 1, 2, 1, 3, 1, 1, 5]
def baseStart_698093 : Nat := 118140960795 + 698093 * 2 ^ 59
def prefixEnd_698093 : Nat := 4983230072969 + 3 ^ 40 * 698093 * 2
def baseEnd_698093 : Nat := 318628667145993281446253

theorem tailTrace_698093 : CollatzResearch.WordTrace tailWord_698093 prefixEnd_698093 318628667145993281446253 := by
  unfold tailWord_698093
  simp only [CollatzResearch.WordTrace]
  refine ⟨25461543459935760637538933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16974362306623840425025955 25461543459935760637538933)
  ·
    refine ⟨2387019699368977559769275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25461543459935760637538933 2387019699368977559769275)
    ·
      refine ⟨3580529549053466339653913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2387019699368977559769275 3580529549053466339653913)
      ·
        refine ⟨2685397161790099754740435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3580529549053466339653913 2685397161790099754740435)
        ·
          refine ⟨4028095742685149632110653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2685397161790099754740435 4028095742685149632110653)
          ·
            refine ⟨1510535903506931112041495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4028095742685149632110653 1510535903506931112041495)
            ·
              refine ⟨2265803855260396668062243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1510535903506931112041495 2265803855260396668062243)
              ·
                refine ⟨3398705782890595002093365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2265803855260396668062243 3398705782890595002093365)
                ·
                  refine ⟨318628667145993281446253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3398705782890595002093365 318628667145993281446253)
                  ·
                    rfl

theorem cell20_698093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_698093 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_698093 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_698093 prefixEnd_698093 := by exact prefixLift 698093
  have htrace : WordTrace (prefixWord ++ tailWord_698093) baseStart_698093 baseEnd_698093 := by
    simpa [prefixWord, tailWord_698093, baseEnd_698093] using wordTrace_append hprefix tailTrace_698093
  have hstable : (prefixWord ++ tailWord_698093).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698093).length < 2 ^ (prefixWord ++ tailWord_698093).sum := by decide
  have hdescent : baseEnd_698093 < baseStart_698093 := by decide
  rcases family_descends (prefixWord ++ tailWord_698093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698145 : List Nat := [1, 2, 3, 2, 1, 5, 6]
def baseStart_698145 : Nat := 118140960795 + 698145 * 2 ^ 59
def prefixEnd_698145 : Nat := 4983230072969 + 3 ^ 40 * 698145 * 2
def baseEnd_698145 : Nat := 35405822373656912412523

theorem tailTrace_698145 : CollatzResearch.WordTrace tailWord_698145 prefixEnd_698145 35405822373656912412523 := by
  unfold tailWord_698145
  simp only [CollatzResearch.WordTrace]
  refine ⟨25463440055747373518431889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16975626703831582345621259 25463440055747373518431889)
  ·
    refine ⟨19097580041810530138823917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25463440055747373518431889 19097580041810530138823917)
    ·
      refine ⟨7161592515678948802058969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19097580041810530138823917 7161592515678948802058969)
      ·
        refine ⟨5371194386759211601544227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7161592515678948802058969 5371194386759211601544227)
        ·
          refine ⟨8056791580138817402316341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5371194386759211601544227 8056791580138817402316341)
          ·
            refine ⟨755324210638014131467157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8056791580138817402316341 755324210638014131467157)
            ·
              refine ⟨35405822373656912412523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 755324210638014131467157 35405822373656912412523)
              ·
                rfl

theorem cell20_698145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 6].length) (baseStart_698145 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_698145 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_698145 prefixEnd_698145 := by exact prefixLift 698145
  have htrace : WordTrace (prefixWord ++ tailWord_698145) baseStart_698145 baseEnd_698145 := by
    simpa [prefixWord, tailWord_698145, baseEnd_698145] using wordTrace_append hprefix tailTrace_698145
  have hstable : (prefixWord ++ tailWord_698145).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698145).length < 2 ^ (prefixWord ++ tailWord_698145).sum := by decide
  have hdescent : baseEnd_698145 < baseStart_698145 := by decide
  rcases family_descends (prefixWord ++ tailWord_698145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698165 : List Nat := [1, 3, 3, 1, 4, 2, 2, 1, 3]
def baseStart_698165 : Nat := 118140960795 + 698165 * 2 ^ 59
def prefixEnd_698165 : Nat := 4983230072969 + 3 ^ 40 * 698165 * 2
def baseEnd_698165 : Nat := 318661529907881031045959

theorem tailTrace_698165 : CollatzResearch.WordTrace tailWord_698165 prefixEnd_698165 318661529907881031045959 := by
  unfold tailWord_698165
  simp only [CollatzResearch.WordTrace]
  refine ⟨25464169515674916934159949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16976113010449944622773299 25464169515674916934159949)
  ·
    refine ⟨9549063568378093850309981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25464169515674916934159949 9549063568378093850309981)
    ·
      refine ⟨3580898838141785193866243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9549063568378093850309981 3580898838141785193866243)
      ·
        refine ⟨5371348257212677790799365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3580898838141785193866243 5371348257212677790799365)
        ·
          refine ⟨1007127798227377085774881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5371348257212677790799365 1007127798227377085774881)
          ·
            refine ⟨755345848670532814331161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1007127798227377085774881 755345848670532814331161)
            ·
              refine ⟨566509386502899610748371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 755345848670532814331161 566509386502899610748371)
              ·
                refine ⟨849764079754349416122557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 566509386502899610748371 849764079754349416122557)
                ·
                  refine ⟨318661529907881031045959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 849764079754349416122557 318661529907881031045959)
                  ·
                    rfl

theorem cell20_698165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 2, 1, 3].length) (baseStart_698165 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_698165 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_698165 prefixEnd_698165 := by exact prefixLift 698165
  have htrace : WordTrace (prefixWord ++ tailWord_698165) baseStart_698165 baseEnd_698165 := by
    simpa [prefixWord, tailWord_698165, baseEnd_698165] using wordTrace_append hprefix tailTrace_698165
  have hstable : (prefixWord ++ tailWord_698165).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698165).length < 2 ^ (prefixWord ++ tailWord_698165).sum := by decide
  have hdescent : baseEnd_698165 < baseStart_698165 := by decide
  rcases family_descends (prefixWord ++ tailWord_698165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698207 : List Nat := [1, 1, 2, 3, 1, 5, 2, 2, 3]
def baseStart_698207 : Nat := 118140960795 + 698207 * 2 ^ 59
def prefixEnd_698207 : Nat := 4983230072969 + 3 ^ 40 * 698207 * 2
def baseEnd_698207 : Nat := 318680699852315551645787

theorem tailTrace_698207 : CollatzResearch.WordTrace tailWord_698207 prefixEnd_698207 318680699852315551645787 := by
  unfold tailWord_698207
  simp only [CollatzResearch.WordTrace]
  refine ⟨25465701381522758107188875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16977134254348505404792583 25465701381522758107188875)
  ·
    refine ⟨38198552072284137160783313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25465701381522758107188875 38198552072284137160783313)
    ·
      refine ⟨28648914054213102870587485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38198552072284137160783313 28648914054213102870587485)
      ·
        refine ⟨10743342770329913576470307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28648914054213102870587485 10743342770329913576470307)
        ·
          refine ⟨16115014155494870364705461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10743342770329913576470307 16115014155494870364705461)
          ·
            refine ⟨1510782577077644096691137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16115014155494870364705461 1510782577077644096691137)
            ·
              refine ⟨1133086932808233072518353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1510782577077644096691137 1133086932808233072518353)
              ·
                refine ⟨849815199606174804388765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1133086932808233072518353 849815199606174804388765)
                ·
                  refine ⟨318680699852315551645787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 849815199606174804388765 318680699852315551645787)
                  ·
                    rfl

theorem cell20_698207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 2, 2, 3].length) (baseStart_698207 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_698207 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_698207 prefixEnd_698207 := by exact prefixLift 698207
  have htrace : WordTrace (prefixWord ++ tailWord_698207) baseStart_698207 baseEnd_698207 := by
    simpa [prefixWord, tailWord_698207, baseEnd_698207] using wordTrace_append hprefix tailTrace_698207
  have hstable : (prefixWord ++ tailWord_698207).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698207).length < 2 ^ (prefixWord ++ tailWord_698207).sum := by decide
  have hdescent : baseEnd_698207 < baseStart_698207 := by decide
  rcases family_descends (prefixWord ++ tailWord_698207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698210 : List Nat := [3, 3, 2, 1, 2, 2, 1, 4, 2]
def baseStart_698210 : Nat := 118140960795 + 698210 * 2 ^ 59
def prefixEnd_698210 : Nat := 4983230072969 + 3 ^ 40 * 698210 * 2
def baseEnd_698210 : Nat := 318682069134060874545775

theorem tailTrace_698210 : CollatzResearch.WordTrace tailWord_698210 prefixEnd_698210 318682069134060874545775 := by
  unfold tailWord_698210
  simp only [CollatzResearch.WordTrace]
  refine ⟨6366452700127972404887021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16977207200341259746365389 6366452700127972404887021)
  ·
    refine ⟨2387419762547989651832633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6366452700127972404887021 2387419762547989651832633)
    ·
      refine ⟨1790564821910992238874475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2387419762547989651832633 1790564821910992238874475)
      ·
        refine ⟨2685847232866488358311713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1790564821910992238874475 2685847232866488358311713)
        ·
          refine ⟨2014385424649866268733785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2685847232866488358311713 2014385424649866268733785)
          ·
            refine ⟨1510789068487399701550339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2014385424649866268733785 1510789068487399701550339)
            ·
              refine ⟨2266183602731099552325509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1510789068487399701550339 2266183602731099552325509)
              ·
                refine ⟨424909425512081166061033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2266183602731099552325509 424909425512081166061033)
                ·
                  refine ⟨318682069134060874545775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 424909425512081166061033 318682069134060874545775)
                  ·
                    rfl

theorem cell20_698210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 4, 2].length) (baseStart_698210 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_698210 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_698210 prefixEnd_698210 := by exact prefixLift 698210
  have htrace : WordTrace (prefixWord ++ tailWord_698210) baseStart_698210 baseEnd_698210 := by
    simpa [prefixWord, tailWord_698210, baseEnd_698210] using wordTrace_append hprefix tailTrace_698210
  have hstable : (prefixWord ++ tailWord_698210).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698210).length < 2 ^ (prefixWord ++ tailWord_698210).sum := by decide
  have hdescent : baseEnd_698210 < baseStart_698210 := by decide
  rcases family_descends (prefixWord ++ tailWord_698210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698221 : List Nat := [1, 5, 1, 1, 1, 1, 5, 5]
def baseStart_698221 : Nat := 118140960795 + 698221 * 2 ^ 59
def prefixEnd_698221 : Nat := 4983230072969 + 3 ^ 40 * 698221 * 2
def baseEnd_698221 : Nat := 106229029944597908393021

theorem tailTrace_698221 : CollatzResearch.WordTrace tailWord_698221 prefixEnd_698221 106229029944597908393021 := by
  unfold tailWord_698221
  simp only [CollatzResearch.WordTrace]
  refine ⟨25466212003472038498198517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16977474668981358998799011 25466212003472038498198517)
  ·
    refine ⟨2387457375325503609206111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25466212003472038498198517 2387457375325503609206111)
    ·
      refine ⟨3581186062988255413809167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2387457375325503609206111 3581186062988255413809167)
      ·
        refine ⟨5371779094482383120713751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3581186062988255413809167 5371779094482383120713751)
        ·
          refine ⟨8057668641723574681070627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5371779094482383120713751 8057668641723574681070627)
          ·
            refine ⟨12086502962585362021605941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8057668641723574681070627 12086502962585362021605941)
            ·
              refine ⟨1133109652742377689525557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12086502962585362021605941 1133109652742377689525557)
              ·
                refine ⟨106229029944597908393021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1133109652742377689525557 106229029944597908393021)
                ·
                  rfl

theorem cell20_698221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 5, 5].length) (baseStart_698221 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_698221 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_698221 prefixEnd_698221 := by exact prefixLift 698221
  have htrace : WordTrace (prefixWord ++ tailWord_698221) baseStart_698221 baseEnd_698221 := by
    simpa [prefixWord, tailWord_698221, baseEnd_698221] using wordTrace_append hprefix tailTrace_698221
  have hstable : (prefixWord ++ tailWord_698221).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698221).length < 2 ^ (prefixWord ++ tailWord_698221).sum := by decide
  have hdescent : baseEnd_698221 < baseStart_698221 := by decide
  rcases family_descends (prefixWord ++ tailWord_698221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698248 : List Nat := [2, 1, 3, 3, 3, 1, 2, 3, 2]
def baseStart_698248 : Nat := 118140960795 + 698248 * 2 ^ 59
def prefixEnd_698248 : Nat := 4983230072969 + 3 ^ 40 * 698248 * 2
def baseEnd_698248 : Nat := 318699413369501631278953

theorem tailTrace_698248 : CollatzResearch.WordTrace tailWord_698248 prefixEnd_698248 318699413369501631278953 := by
  unfold tailWord_698248
  simp only [CollatzResearch.WordTrace]
  refine ⟨12733598387187111054715699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16978131182916148072954265 12733598387187111054715699)
  ·
    refine ⟨19100397580780666582073549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12733598387187111054715699 19100397580780666582073549)
    ·
      refine ⟨7162649092792749968277581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19100397580780666582073549 7162649092792749968277581)
      ·
        refine ⟨2685993409797281238104093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7162649092792749968277581 2685993409797281238104093)
        ·
          refine ⟨1007247528673980464289035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2685993409797281238104093 1007247528673980464289035)
          ·
            refine ⟨1510871293010970696433553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1007247528673980464289035 1510871293010970696433553)
            ·
              refine ⟨1133153469758228022325165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1510871293010970696433553 1133153469758228022325165)
              ·
                refine ⟨424932551159335508371937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1133153469758228022325165 424932551159335508371937)
                ·
                  refine ⟨318699413369501631278953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 424932551159335508371937 318699413369501631278953)
                  ·
                    rfl

theorem cell20_698248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 2, 3, 2].length) (baseStart_698248 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_698248 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_698248 prefixEnd_698248 := by exact prefixLift 698248
  have htrace : WordTrace (prefixWord ++ tailWord_698248) baseStart_698248 baseEnd_698248 := by
    simpa [prefixWord, tailWord_698248, baseEnd_698248] using wordTrace_append hprefix tailTrace_698248
  have hstable : (prefixWord ++ tailWord_698248).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698248).length < 2 ^ (prefixWord ++ tailWord_698248).sum := by decide
  have hdescent : baseEnd_698248 < baseStart_698248 := by decide
  rcases family_descends (prefixWord ++ tailWord_698248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698269 : List Nat := [1, 4, 2, 1, 2, 2, 2, 4, 2]
def baseStart_698269 : Nat := 118140960795 + 698269 * 2 ^ 59
def prefixEnd_698269 : Nat := 4983230072969 + 3 ^ 40 * 698269 * 2
def baseEnd_698269 : Nat := 318708998341718891578867

theorem tailTrace_698269 : CollatzResearch.WordTrace tailWord_698269 prefixEnd_698269 318708998341718891578867 := by
  unfold tailWord_698269
  simp only [CollatzResearch.WordTrace]
  refine ⟨25467962707298142695945861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16978641804865428463963907 25467962707298142695945861)
  ·
    refine ⟨4775243007618401755489849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25467962707298142695945861 4775243007618401755489849)
    ·
      refine ⟨3581432255713801316617387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4775243007618401755489849 3581432255713801316617387)
      ·
        refine ⟨5372148383570701974926081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3581432255713801316617387 5372148383570701974926081)
        ·
          refine ⟨4029111287678026481194561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5372148383570701974926081 4029111287678026481194561)
          ·
            refine ⟨3021833465758519860895921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4029111287678026481194561 3021833465758519860895921)
            ·
              refine ⟨2266375099318889895671941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3021833465758519860895921 2266375099318889895671941)
              ·
                refine ⟨424945331122291855438489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2266375099318889895671941 424945331122291855438489)
                ·
                  refine ⟨318708998341718891578867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 424945331122291855438489 318708998341718891578867)
                  ·
                    rfl

theorem cell20_698269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 4, 2].length) (baseStart_698269 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_698269 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_698269 prefixEnd_698269 := by exact prefixLift 698269
  have htrace : WordTrace (prefixWord ++ tailWord_698269) baseStart_698269 baseEnd_698269 := by
    simpa [prefixWord, tailWord_698269, baseEnd_698269] using wordTrace_append hprefix tailTrace_698269
  have hstable : (prefixWord ++ tailWord_698269).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698269).length < 2 ^ (prefixWord ++ tailWord_698269).sum := by decide
  have hdescent : baseEnd_698269 < baseStart_698269 := by decide
  rcases family_descends (prefixWord ++ tailWord_698269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698324 : List Nat := [2, 4, 1, 2, 1, 1, 5, 2, 2]
def baseStart_698324 : Nat := 118140960795 + 698324 * 2 ^ 59
def prefixEnd_698324 : Nat := 4983230072969 + 3 ^ 40 * 698324 * 2
def baseEnd_698324 : Nat := 318734101840383144745309

theorem tailTrace_698324 : CollatzResearch.WordTrace tailWord_698324 prefixEnd_698324 318734101840383144745309 := by
  unfold tailWord_698324
  simp only [CollatzResearch.WordTrace]
  refine ⟨12734984361049443544599013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16979979148065924726132017 12734984361049443544599013)
  ·
    refine ⟨2387809567696770664612315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12734984361049443544599013 2387809567696770664612315)
    ·
      refine ⟨3581714351545155996918473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2387809567696770664612315 3581714351545155996918473)
      ·
        refine ⟨2686285763658866997688855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3581714351545155996918473 2686285763658866997688855)
        ·
          refine ⟨4029428645488300496533283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2686285763658866997688855 4029428645488300496533283)
          ·
            refine ⟨6044142968232450744799925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4029428645488300496533283 6044142968232450744799925)
            ·
              refine ⟨566638403271792257324993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6044142968232450744799925 566638403271792257324993)
              ·
                refine ⟨424978802453844192993745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 566638403271792257324993 424978802453844192993745)
                ·
                  refine ⟨318734101840383144745309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 424978802453844192993745 318734101840383144745309)
                  ·
                    rfl

theorem cell20_698324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 5, 2, 2].length) (baseStart_698324 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_698324 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_698324 prefixEnd_698324 := by exact prefixLift 698324
  have htrace : WordTrace (prefixWord ++ tailWord_698324) baseStart_698324 baseEnd_698324 := by
    simpa [prefixWord, tailWord_698324, baseEnd_698324] using wordTrace_append hprefix tailTrace_698324
  have hstable : (prefixWord ++ tailWord_698324).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698324).length < 2 ^ (prefixWord ++ tailWord_698324).sum := by decide
  have hdescent : baseEnd_698324 < baseStart_698324 := by decide
  rcases family_descends (prefixWord ++ tailWord_698324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698335 : List Nat := [1, 1, 2, 3, 4, 2, 2, 5]
def baseStart_698335 : Nat := 118140960795 + 698335 * 2 ^ 59
def prefixEnd_698335 : Nat := 4983230072969 + 3 ^ 40 * 698335 * 2
def baseEnd_698335 : Nat := 106246374180038665126199

theorem tailTrace_698335 : CollatzResearch.WordTrace tailWord_698335 prefixEnd_698335 106246374180038665126199 := by
  unfold tailWord_698335
  simp only [CollatzResearch.WordTrace]
  refine ⟨25470369925059035967848459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16980246616706023978565639 25470369925059035967848459)
  ·
    refine ⟨38205554887588553951772689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25470369925059035967848459 38205554887588553951772689)
    ·
      refine ⟨28654166165691415463829517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38205554887588553951772689 28654166165691415463829517)
      ·
        refine ⟨10745312312134280798936069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28654166165691415463829517 10745312312134280798936069)
        ·
          refine ⟨2014746058525177649800513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10745312312134280798936069 2014746058525177649800513)
          ·
            refine ⟨1511059543893883237350385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2014746058525177649800513 1511059543893883237350385)
            ·
              refine ⟨1133294657920412428012789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1511059543893883237350385 1133294657920412428012789)
              ·
                refine ⟨106246374180038665126199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1133294657920412428012789 106246374180038665126199)
                ·
                  rfl

theorem cell20_698335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 2, 5].length) (baseStart_698335 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_698335 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_698335 prefixEnd_698335 := by exact prefixLift 698335
  have htrace : WordTrace (prefixWord ++ tailWord_698335) baseStart_698335 baseEnd_698335 := by
    simpa [prefixWord, tailWord_698335, baseEnd_698335] using wordTrace_append hprefix tailTrace_698335
  have hstable : (prefixWord ++ tailWord_698335).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698335).length < 2 ^ (prefixWord ++ tailWord_698335).sum := by decide
  have hdescent : baseEnd_698335 < baseStart_698335 := by decide
  rcases family_descends (prefixWord ++ tailWord_698335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698363 : List Nat := [1, 1, 1, 1, 1, 3, 4, 1, 7]
def baseStart_698363 : Nat := 118140960795 + 698363 * 2 ^ 59
def prefixEnd_698363 : Nat := 4983230072969 + 3 ^ 40 * 698363 * 2
def baseEnd_698363 : Nat := 318751902503072342445149

theorem tailTrace_698363 : CollatzResearch.WordTrace tailWord_698363 prefixEnd_698363 318751902503072342445149 := by
  unfold tailWord_698363
  simp only [CollatzResearch.WordTrace]
  refine ⟨25471391168957596749867743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16980927445971731166578495 25471391168957596749867743)
  ·
    refine ⟨38207086753436395124801615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25471391168957596749867743 38207086753436395124801615)
    ·
      refine ⟨57310630130154592687202423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38207086753436395124801615 57310630130154592687202423)
      ·
        refine ⟨85965945195231889030803635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57310630130154592687202423 85965945195231889030803635)
        ·
          refine ⟨128948917792847833546205453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85965945195231889030803635 128948917792847833546205453)
          ·
            refine ⟨48355844172317937579827045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 128948917792847833546205453 48355844172317937579827045)
            ·
              refine ⟨9066720782309613296217571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48355844172317937579827045 9066720782309613296217571)
              ·
                refine ⟨13600081173464419944326357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9066720782309613296217571 13600081173464419944326357)
                ·
                  refine ⟨318751902503072342445149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13600081173464419944326357 318751902503072342445149)
                  ·
                    rfl

theorem cell20_698363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 7].length) (baseStart_698363 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_698363 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_698363 prefixEnd_698363 := by exact prefixLift 698363
  have htrace : WordTrace (prefixWord ++ tailWord_698363) baseStart_698363 baseEnd_698363 := by
    simpa [prefixWord, tailWord_698363, baseEnd_698363] using wordTrace_append hprefix tailTrace_698363
  have hstable : (prefixWord ++ tailWord_698363).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698363).length < 2 ^ (prefixWord ++ tailWord_698363).sum := by decide
  have hdescent : baseEnd_698363 < baseStart_698363 := by decide
  rcases family_descends (prefixWord ++ tailWord_698363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698397 : List Nat := [1, 4, 2, 2, 2, 1, 2, 3, 3]
def baseStart_698397 : Nat := 118140960795 + 698397 * 2 ^ 59
def prefixEnd_698397 : Nat := 4983230072969 + 3 ^ 40 * 698397 * 2
def baseEnd_698397 : Nat := 318767421029519335311677

theorem tailTrace_698397 : CollatzResearch.WordTrace tailWord_698397 prefixEnd_698397 318767421029519335311677 := by
  unfold tailWord_698397
  simp only [CollatzResearch.WordTrace]
  refine ⟨25472631250834420556605445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16981754167222947037736963 25472631250834420556605445)
  ·
    refine ⟨4776118359531453854363521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25472631250834420556605445 4776118359531453854363521)
    ·
      refine ⟨3582088769648590390772641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4776118359531453854363521 3582088769648590390772641)
      ·
        refine ⟨2686566577236442793079481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3582088769648590390772641 2686566577236442793079481)
        ·
          refine ⟨2014924932927332094809611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2686566577236442793079481 2014924932927332094809611)
          ·
            refine ⟨3022387399390998142214417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2014924932927332094809611 3022387399390998142214417)
            ·
              refine ⟨2266790549543248606660813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3022387399390998142214417 2266790549543248606660813)
              ·
                refine ⟨850046456078718227497805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2266790549543248606660813 850046456078718227497805)
                ·
                  refine ⟨318767421029519335311677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 850046456078718227497805 318767421029519335311677)
                  ·
                    rfl

theorem cell20_698397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 3, 3].length) (baseStart_698397 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_698397 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_698397 prefixEnd_698397 := by exact prefixLift 698397
  have htrace : WordTrace (prefixWord ++ tailWord_698397) baseStart_698397 baseEnd_698397 := by
    simpa [prefixWord, tailWord_698397, baseEnd_698397] using wordTrace_append hprefix tailTrace_698397
  have hstable : (prefixWord ++ tailWord_698397).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698397).length < 2 ^ (prefixWord ++ tailWord_698397).sum := by decide
  have hdescent : baseEnd_698397 < baseStart_698397 := by decide
  rcases family_descends (prefixWord ++ tailWord_698397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698407 : List Nat := [1, 1, 7, 1, 2, 1, 3, 4]
def baseStart_698407 : Nat := 118140960795 + 698407 * 2 ^ 59
def prefixEnd_698407 : Nat := 4983230072969 + 3 ^ 40 * 698407 * 2
def baseEnd_698407 : Nat := 106257328434001248326101

theorem tailTrace_698407 : CollatzResearch.WordTrace tailWord_698407 prefixEnd_698407 106257328434001248326101 := by
  unfold tailWord_698407
  simp only [CollatzResearch.WordTrace]
  refine ⟨25472995980798192264469475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16981997320532128176312983 25472995980798192264469475)
  ·
    refine ⟨38209493971197288396704213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25472995980798192264469475 38209493971197288396704213)
    ·
      refine ⟨895535014949936446797755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 38209493971197288396704213 895535014949936446797755)
      ·
        refine ⟨1343302522424904670196633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 895535014949936446797755 1343302522424904670196633)
        ·
          refine ⟨1007476891818678502647475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1343302522424904670196633 1007476891818678502647475)
          ·
            refine ⟨1511215337728017753971213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1007476891818678502647475 1511215337728017753971213)
            ·
              refine ⟨566705751648006657739205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1511215337728017753971213 566705751648006657739205)
              ·
                refine ⟨106257328434001248326101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 566705751648006657739205 106257328434001248326101)
                ·
                  rfl

theorem cell20_698407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 3, 4].length) (baseStart_698407 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_698407 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_698407 prefixEnd_698407 := by exact prefixLift 698407
  have htrace : WordTrace (prefixWord ++ tailWord_698407) baseStart_698407 baseEnd_698407 := by
    simpa [prefixWord, tailWord_698407, baseEnd_698407] using wordTrace_append hprefix tailTrace_698407
  have hstable : (prefixWord ++ tailWord_698407).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698407).length < 2 ^ (prefixWord ++ tailWord_698407).sum := by decide
  have hdescent : baseEnd_698407 < baseStart_698407 := by decide
  rcases family_descends (prefixWord ++ tailWord_698407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698432 : List Nat := [2, 1, 1, 2, 2, 5, 7]
def baseStart_698432 : Nat := 118140960795 + 698432 * 2 ^ 59
def prefixEnd_698432 : Nat := 4983230072969 + 3 ^ 40 * 698432 * 2
def baseEnd_698432 : Nat := 35420377331468307682763

theorem tailTrace_698432 : CollatzResearch.WordTrace tailWord_698432 prefixEnd_698432 35420377331468307682763 := by
  unfold tailWord_698432
  simp only [CollatzResearch.WordTrace]
  refine ⟨12736953902853810767064775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16982605203805081022753033 12736953902853810767064775)
  ·
    refine ⟨19105430854280716150597163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12736953902853810767064775 19105430854280716150597163)
    ·
      refine ⟨28658146281421074225895745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19105430854280716150597163 28658146281421074225895745)
      ·
        refine ⟨21493609711065805669421809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28658146281421074225895745 21493609711065805669421809)
        ·
          refine ⟨16120207283299354252066357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21493609711065805669421809 16120207283299354252066357)
          ·
            refine ⟨1511269432809314461131221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16120207283299354252066357 1511269432809314461131221)
            ·
              refine ⟨35420377331468307682763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1511269432809314461131221 35420377331468307682763)
              ·
                rfl

theorem cell20_698432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 7].length) (baseStart_698432 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_698432 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_698432 prefixEnd_698432 := by exact prefixLift 698432
  have htrace : WordTrace (prefixWord ++ tailWord_698432) baseStart_698432 baseEnd_698432 := by
    simpa [prefixWord, tailWord_698432, baseEnd_698432] using wordTrace_append hprefix tailTrace_698432
  have hstable : (prefixWord ++ tailWord_698432).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698432).length < 2 ^ (prefixWord ++ tailWord_698432).sum := by decide
  have hdescent : baseEnd_698432 < baseStart_698432 := by decide
  rcases family_descends (prefixWord ++ tailWord_698432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698438 : List Nat := [6, 1, 1, 1, 1, 1, 1, 6, 2]
def baseStart_698438 : Nat := 118140960795 + 698438 * 2 ^ 59
def prefixEnd_698438 : Nat := 4983230072969 + 3 ^ 40 * 698438 * 2
def baseEnd_698438 : Nat := 318786134546705414944843

theorem tailTrace_698438 : CollatzResearch.WordTrace tailWord_698438 prefixEnd_698438 318786134546705414944843 := by
  unfold tailWord_698438
  simp only [CollatzResearch.WordTrace]
  refine ⟨796066457615183892463999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 16982751095790589705898645 796066457615183892463999)
  ·
    refine ⟨1194099686422775838695999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 796066457615183892463999 1194099686422775838695999)
    ·
      refine ⟨1791149529634163758043999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1194099686422775838695999 1791149529634163758043999)
      ·
        refine ⟨2686724294451245637065999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1791149529634163758043999 2686724294451245637065999)
        ·
          refine ⟨4030086441676868455598999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2686724294451245637065999 4030086441676868455598999)
          ·
            refine ⟨6045129662515302683398499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4030086441676868455598999 6045129662515302683398499)
            ·
              refine ⟨9067694493772954025097749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6045129662515302683398499 9067694493772954025097749)
              ·
                refine ⟨425048179395607219926457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9067694493772954025097749 425048179395607219926457)
                ·
                  refine ⟨318786134546705414944843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 425048179395607219926457 318786134546705414944843)
                  ·
                    rfl

theorem cell20_698438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 6, 2].length) (baseStart_698438 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_698438 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_698438 prefixEnd_698438 := by exact prefixLift 698438
  have htrace : WordTrace (prefixWord ++ tailWord_698438) baseStart_698438 baseEnd_698438 := by
    simpa [prefixWord, tailWord_698438, baseEnd_698438] using wordTrace_append hprefix tailTrace_698438
  have hstable : (prefixWord ++ tailWord_698438).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698438).length < 2 ^ (prefixWord ++ tailWord_698438).sum := by decide
  have hdescent : baseEnd_698438 < baseStart_698438 := by decide
  rcases family_descends (prefixWord ++ tailWord_698438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698466 : List Nat := [3, 3, 2, 2, 2, 1, 1, 6]
def baseStart_698466 : Nat := 118140960795 + 698466 * 2 ^ 59
def prefixEnd_698466 : Nat := 4983230072969 + 3 ^ 40 * 698466 * 2
def baseEnd_698466 : Nat := 106266304836553920670465

theorem tailTrace_698466 : CollatzResearch.WordTrace tailWord_698466 prefixEnd_698466 106266304836553920670465 := by
  unfold tailWord_698466
  simp only [CollatzResearch.WordTrace]
  refine ⟨6368786971896111335216813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16983431925056296893911501 6368786971896111335216813)
  ·
    refine ⟨2388295114461041750706305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6368786971896111335216813 2388295114461041750706305)
    ·
      refine ⟨1791221335845781313029729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2388295114461041750706305 1791221335845781313029729)
      ·
        refine ⟨1343416001884335984772297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1791221335845781313029729 1343416001884335984772297)
        ·
          refine ⟨1007562001413251988579223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1343416001884335984772297 1007562001413251988579223)
          ·
            refine ⟨1511343002119877982868835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1007562001413251988579223 1511343002119877982868835)
            ·
              refine ⟨2267014503179816974303253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1511343002119877982868835 2267014503179816974303253)
              ·
                refine ⟨106266304836553920670465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2267014503179816974303253 106266304836553920670465)
                ·
                  rfl

theorem cell20_698466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 6].length) (baseStart_698466 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_698466 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_698466 prefixEnd_698466 := by exact prefixLift 698466
  have htrace : WordTrace (prefixWord ++ tailWord_698466) baseStart_698466 baseEnd_698466 := by
    simpa [prefixWord, tailWord_698466, baseEnd_698466] using wordTrace_append hprefix tailTrace_698466
  have hstable : (prefixWord ++ tailWord_698466).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698466).length < 2 ^ (prefixWord ++ tailWord_698466).sum := by decide
  have hdescent : baseEnd_698466 < baseStart_698466 := by decide
  rcases family_descends (prefixWord ++ tailWord_698466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698497 : List Nat := [1, 2, 4, 2, 3, 2, 1, 1, 4]
def baseStart_698497 : Nat := 118140960795 + 698497 * 2 ^ 59
def prefixEnd_698497 : Nat := 4983230072969 + 3 ^ 40 * 698497 * 2
def baseEnd_698497 : Nat := 318813063754363431977935

theorem tailTrace_698497 : CollatzResearch.WordTrace tailWord_698497 prefixEnd_698497 318813063754363431977935 := by
  unfold tailWord_698497
  simp only [CollatzResearch.WordTrace]
  refine ⟨25476278550472137635245745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16984185700314758423497163 25476278550472137635245745)
  ·
    refine ⟨19107208912854103226434309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25476278550472137635245745 19107208912854103226434309)
    ·
      refine ⟨3582601671160144354956433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19107208912854103226434309 3582601671160144354956433)
      ·
        refine ⟨2686951253370108266217325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3582601671160144354956433 2686951253370108266217325)
        ·
          refine ⟨1007606720013790599831497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2686951253370108266217325 1007606720013790599831497)
          ·
            refine ⟨755705040010342949873623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1007606720013790599831497 755705040010342949873623)
            ·
              refine ⟨1133557560015514424810435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 755705040010342949873623 1133557560015514424810435)
              ·
                refine ⟨1700336340023271637215653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1133557560015514424810435 1700336340023271637215653)
                ·
                  refine ⟨318813063754363431977935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1700336340023271637215653 318813063754363431977935)
                  ·
                    rfl

theorem cell20_698497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 1, 1, 4].length) (baseStart_698497 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_698497 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_698497 prefixEnd_698497 := by exact prefixLift 698497
  have htrace : WordTrace (prefixWord ++ tailWord_698497) baseStart_698497 baseEnd_698497 := by
    simpa [prefixWord, tailWord_698497, baseEnd_698497] using wordTrace_append hprefix tailTrace_698497
  have hstable : (prefixWord ++ tailWord_698497).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698497).length < 2 ^ (prefixWord ++ tailWord_698497).sum := by decide
  have hdescent : baseEnd_698497 < baseStart_698497 := by decide
  rcases family_descends (prefixWord ++ tailWord_698497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698542 : List Nat := [4, 1, 4, 2, 1, 8]
def baseStart_698542 : Nat := 118140960795 + 698542 * 2 ^ 59
def prefixEnd_698542 : Nat := 4983230072969 + 3 ^ 40 * 698542 * 2
def baseEnd_698542 : Nat := 11808651962242343536213

theorem tailTrace_698542 : CollatzResearch.WordTrace tailWord_698542 prefixEnd_698542 11808651962242343536213 := by
  unfold tailWord_698542
  simp only [CollatzResearch.WordTrace]
  refine ⟨3184739979413638790079235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16985279890206073547089253 3184739979413638790079235)
  ·
    refine ⟨4777109969120458185118853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3184739979413638790079235 4777109969120458185118853)
    ·
      refine ⟨895708119210085909709785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4777109969120458185118853 895708119210085909709785)
      ·
        refine ⟨671781089407564432282339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 895708119210085909709785 671781089407564432282339)
        ·
          refine ⟨1007671634111346648423509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 671781089407564432282339 1007671634111346648423509)
          ·
            refine ⟨11808651962242343536213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1007671634111346648423509 11808651962242343536213)
            ·
              rfl

theorem cell20_698542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 8].length) (baseStart_698542 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_698542 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_698542 prefixEnd_698542 := by exact prefixLift 698542
  have htrace : WordTrace (prefixWord ++ tailWord_698542) baseStart_698542 baseEnd_698542 := by
    simpa [prefixWord, tailWord_698542, baseEnd_698542] using wordTrace_append hprefix tailTrace_698542
  have hstable : (prefixWord ++ tailWord_698542).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698542).length < 2 ^ (prefixWord ++ tailWord_698542).sum := by decide
  have hdescent : baseEnd_698542 < baseStart_698542 := by decide
  rcases family_descends (prefixWord ++ tailWord_698542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698548 : List Nat := [2, 5, 3, 1, 1, 1, 1, 4, 2]
def baseStart_698548 : Nat := 118140960795 + 698548 * 2 ^ 59
def prefixEnd_698548 : Nat := 4983230072969 + 3 ^ 40 * 698548 * 2
def baseEnd_698548 : Nat := 318836341544033921277727

theorem tailTrace_698548 : CollatzResearch.WordTrace tailWord_698548 prefixEnd_698548 318836341544033921277727 := by
  unfold tailWord_698548
  simp only [CollatzResearch.WordTrace]
  refine ⟨12739069336643686672676149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16985425782191582230234865 12739069336643686672676149)
  ·
    refine ⟨1194287750310345625563389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12739069336643686672676149 1194287750310345625563389)
    ·
      refine ⟨447857906366379609586271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1194287750310345625563389 447857906366379609586271)
      ·
        refine ⟨671786859549569414379407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 447857906366379609586271 671786859549569414379407)
        ·
          refine ⟨1007680289324354121569111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 671786859549569414379407 1007680289324354121569111)
          ·
            refine ⟨1511520433986531182353667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1007680289324354121569111 1511520433986531182353667)
            ·
              refine ⟨2267280650979796773530501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1511520433986531182353667 2267280650979796773530501)
              ·
                refine ⟨425115122058711895036969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2267280650979796773530501 425115122058711895036969)
                ·
                  refine ⟨318836341544033921277727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 425115122058711895036969 318836341544033921277727)
                  ·
                    rfl

theorem cell20_698548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 4, 2].length) (baseStart_698548 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_698548 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_698548 prefixEnd_698548 := by exact prefixLift 698548
  have htrace : WordTrace (prefixWord ++ tailWord_698548) baseStart_698548 baseEnd_698548 := by
    simpa [prefixWord, tailWord_698548, baseEnd_698548] using wordTrace_append hprefix tailTrace_698548
  have hstable : (prefixWord ++ tailWord_698548).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698548).length < 2 ^ (prefixWord ++ tailWord_698548).sum := by decide
  have hdescent : baseEnd_698548 < baseStart_698548 := by decide
  rcases family_descends (prefixWord ++ tailWord_698548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698570 : List Nat := [3, 1, 2, 1, 3, 1, 1, 5, 3]
def baseStart_698570 : Nat := 118140960795 + 698570 * 2 ^ 59
def prefixEnd_698570 : Nat := 4983230072969 + 3 ^ 40 * 698570 * 2
def baseEnd_698570 : Nat := 318846382943499622544303

theorem tailTrace_698570 : CollatzResearch.WordTrace tailWord_698570 prefixEnd_698570 318846382943499622544303 := by
  unfold tailWord_698570
  simp only [CollatzResearch.WordTrace]
  refine ⟨6369735269801917775663291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16985960719471780735102109 6369735269801917775663291)
  ·
    refine ⟨9554602904702876663494937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6369735269801917775663291 9554602904702876663494937)
    ·
      refine ⟨7165952178527157497621203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9554602904702876663494937 7165952178527157497621203)
      ·
        refine ⟨10748928267790736246431805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7165952178527157497621203 10748928267790736246431805)
        ·
          refine ⟨4030848100421526092411927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10748928267790736246431805 4030848100421526092411927)
          ·
            refine ⟨6046272150632289138617891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4030848100421526092411927 6046272150632289138617891)
            ·
              refine ⟨9069408225948433707926837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6046272150632289138617891 9069408225948433707926837)
              ·
                refine ⟨850257021182665660118141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9069408225948433707926837 850257021182665660118141)
                ·
                  refine ⟨318846382943499622544303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 850257021182665660118141 318846382943499622544303)
                  ·
                    rfl

theorem cell20_698570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 5, 3].length) (baseStart_698570 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_698570 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_698570 prefixEnd_698570 := by exact prefixLift 698570
  have htrace : WordTrace (prefixWord ++ tailWord_698570) baseStart_698570 baseEnd_698570 := by
    simpa [prefixWord, tailWord_698570, baseEnd_698570] using wordTrace_append hprefix tailTrace_698570
  have hstable : (prefixWord ++ tailWord_698570).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698570).length < 2 ^ (prefixWord ++ tailWord_698570).sum := by decide
  have hdescent : baseEnd_698570 < baseStart_698570 := by decide
  rcases family_descends (prefixWord ++ tailWord_698570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698591 : List Nat := [1, 1, 2, 3, 2, 1, 1, 4, 5]
def baseStart_698591 : Nat := 118140960795 + 698591 * 2 ^ 59
def prefixEnd_698591 : Nat := 4983230072969 + 3 ^ 40 * 698591 * 2
def baseEnd_698591 : Nat := 318855967915716882844217

theorem tailTrace_698591 : CollatzResearch.WordTrace tailWord_698591 prefixEnd_698591 318855967915716882844217 := by
  unfold tailWord_698591
  simp only [CollatzResearch.WordTrace]
  refine ⟨25479707012131591689167627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16986471341421061126111751 25479707012131591689167627)
  ·
    refine ⟨38219560518197387533751441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25479707012131591689167627 38219560518197387533751441)
    ·
      refine ⟨28664670388648040650313581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38219560518197387533751441 28664670388648040650313581)
      ·
        refine ⟨10749251395743015243867593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28664670388648040650313581 10749251395743015243867593)
        ·
          refine ⟨8061938546807261432900695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10749251395743015243867593 8061938546807261432900695)
          ·
            refine ⟨12092907820210892149351043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8061938546807261432900695 12092907820210892149351043)
            ·
              refine ⟨18139361730316338224026565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12092907820210892149351043 18139361730316338224026565)
              ·
                refine ⟨3401130324434313417004981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18139361730316338224026565 3401130324434313417004981)
                ·
                  refine ⟨318855967915716882844217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3401130324434313417004981 318855967915716882844217)
                  ·
                    rfl

theorem cell20_698591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 4, 5].length) (baseStart_698591 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_698591 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_698591 prefixEnd_698591 := by exact prefixLift 698591
  have htrace : WordTrace (prefixWord ++ tailWord_698591) baseStart_698591 baseEnd_698591 := by
    simpa [prefixWord, tailWord_698591, baseEnd_698591] using wordTrace_append hprefix tailTrace_698591
  have hstable : (prefixWord ++ tailWord_698591).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698591).length < 2 ^ (prefixWord ++ tailWord_698591).sum := by decide
  have hdescent : baseEnd_698591 < baseStart_698591 := by decide
  rcases family_descends (prefixWord ++ tailWord_698591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698625 : List Nat := [1, 2, 4, 1, 1, 2, 5, 1, 3]
def baseStart_698625 : Nat := 118140960795 + 698625 * 2 ^ 59
def prefixEnd_698625 : Nat := 4983230072969 + 3 ^ 40 * 698625 * 2
def baseEnd_698625 : Nat := 318871486442163875710745

theorem tailTrace_698625 : CollatzResearch.WordTrace tailWord_698625 prefixEnd_698625 318871486442163875710745 := by
  unfold tailWord_698625
  simp only [CollatzResearch.WordTrace]
  refine ⟨25480947094008415495905329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16987298062672276997270219 25480947094008415495905329)
  ·
    refine ⟨19110710320506311621928997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25480947094008415495905329 19110710320506311621928997)
    ·
      refine ⟨3583258185094933429111687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19110710320506311621928997 3583258185094933429111687)
      ·
        refine ⟨5374887277642400143667531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3583258185094933429111687 5374887277642400143667531)
        ·
          refine ⟨8062330916463600215501297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5374887277642400143667531 8062330916463600215501297)
          ·
            refine ⟨6046748187347700161625973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8062330916463600215501297 6046748187347700161625973)
            ·
              refine ⟨566882642563846890152435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6046748187347700161625973 566882642563846890152435)
              ·
                refine ⟨850323963845770335228653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 566882642563846890152435 850323963845770335228653)
                ·
                  refine ⟨318871486442163875710745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 850323963845770335228653 318871486442163875710745)
                  ·
                    rfl

theorem cell20_698625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 5, 1, 3].length) (baseStart_698625 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_698625 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_698625 prefixEnd_698625 := by exact prefixLift 698625
  have htrace : WordTrace (prefixWord ++ tailWord_698625) baseStart_698625 baseEnd_698625 := by
    simpa [prefixWord, tailWord_698625, baseEnd_698625] using wordTrace_append hprefix tailTrace_698625
  have hstable : (prefixWord ++ tailWord_698625).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698625).length < 2 ^ (prefixWord ++ tailWord_698625).sum := by decide
  have hdescent : baseEnd_698625 < baseStart_698625 := by decide
  rcases family_descends (prefixWord ++ tailWord_698625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698660 : List Nat := [2, 3, 1, 3, 1, 2, 8]
def baseStart_698660 : Nat := 118140960795 + 698660 * 2 ^ 59
def prefixEnd_698660 : Nat := 4983230072969 + 3 ^ 40 * 698660 * 2
def baseEnd_698660 : Nat := 35431940155095478838215

theorem tailTrace_698660 : CollatzResearch.WordTrace tailWord_698660 prefixEnd_698660 35431940155095478838215 := by
  unfold tailWord_698660
  simp only [CollatzResearch.WordTrace]
  refine ⟨12741111824440808236714717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16988149099254410982286289 12741111824440808236714717)
  ·
    refine ⟨4777916934165303088768019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12741111824440808236714717 4777916934165303088768019)
    ·
      refine ⟨7166875401247954633152029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4777916934165303088768019 7166875401247954633152029)
      ·
        refine ⟨2687578275467982987432011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7166875401247954633152029 2687578275467982987432011)
        ·
          refine ⟨4031367413201974481148017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2687578275467982987432011 4031367413201974481148017)
          ·
            refine ⟨3023525559901480860861013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4031367413201974481148017 3023525559901480860861013)
            ·
              refine ⟨35431940155095478838215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3023525559901480860861013 35431940155095478838215)
              ·
                rfl

theorem cell20_698660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 8].length) (baseStart_698660 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_698660 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_698660 prefixEnd_698660 := by exact prefixLift 698660
  have htrace : WordTrace (prefixWord ++ tailWord_698660) baseStart_698660 baseEnd_698660 := by
    simpa [prefixWord, tailWord_698660, baseEnd_698660] using wordTrace_append hprefix tailTrace_698660
  have hstable : (prefixWord ++ tailWord_698660).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698660).length < 2 ^ (prefixWord ++ tailWord_698660).sum := by decide
  have hdescent : baseEnd_698660 < baseStart_698660 := by decide
  rcases family_descends (prefixWord ++ tailWord_698660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698666 : List Nat := [3, 1, 4, 2, 3, 1, 1, 1, 4]
def baseStart_698666 : Nat := 118140960795 + 698666 * 2 ^ 59
def prefixEnd_698666 : Nat := 4983230072969 + 3 ^ 40 * 698666 * 2
def baseEnd_698666 : Nat := 318890199959349955343911

theorem tailTrace_698666 : CollatzResearch.WordTrace tailWord_698666 prefixEnd_698666 318890199959349955343911 := by
  unfold tailWord_698666
  simp only [CollatzResearch.WordTrace]
  refine ⟨6370610621714969874536963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16988294991239919665431901 6370610621714969874536963)
  ·
    refine ⟨9555915932572454811805445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6370610621714969874536963 9555915932572454811805445)
    ·
      refine ⟨1791734237357335277213521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9555915932572454811805445 1791734237357335277213521)
      ·
        refine ⟨1343800678018001457910141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1791734237357335277213521 1343800678018001457910141)
        ·
          refine ⟨503925254256750546716303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1343800678018001457910141 503925254256750546716303)
          ·
            refine ⟨755887881385125820074455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 503925254256750546716303 755887881385125820074455)
            ·
              refine ⟨1133831822077688730111683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 755887881385125820074455 1133831822077688730111683)
              ·
                refine ⟨1700747733116533095167525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1133831822077688730111683 1700747733116533095167525)
                ·
                  refine ⟨318890199959349955343911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1700747733116533095167525 318890199959349955343911)
                  ·
                    rfl

theorem cell20_698666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 1, 1, 4].length) (baseStart_698666 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_698666 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_698666 prefixEnd_698666 := by exact prefixLift 698666
  have htrace : WordTrace (prefixWord ++ tailWord_698666) baseStart_698666 baseEnd_698666 := by
    simpa [prefixWord, tailWord_698666, baseEnd_698666] using wordTrace_append hprefix tailTrace_698666
  have hstable : (prefixWord ++ tailWord_698666).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698666).length < 2 ^ (prefixWord ++ tailWord_698666).sum := by decide
  have hdescent : baseEnd_698666 < baseStart_698666 := by decide
  rcases family_descends (prefixWord ++ tailWord_698666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698684 : List Nat := [2, 2, 2, 2, 1, 2, 3, 3, 3]
def baseStart_698684 : Nat := 118140960795 + 698684 * 2 ^ 59
def prefixEnd_698684 : Nat := 4983230072969 + 3 ^ 40 * 698684 * 2
def baseEnd_698684 : Nat := 318898415649821892743837

theorem tailTrace_698684 : CollatzResearch.WordTrace tailWord_698684 prefixEnd_698684 318898415649821892743837 := by
  unfold tailWord_698684
  simp only [CollatzResearch.WordTrace]
  refine ⟨12741549500397334286151553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16988732667196445714868737 12741549500397334286151553)
  ·
    refine ⟨9556162125298000714613665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12741549500397334286151553 9556162125298000714613665)
    ·
      refine ⟨7167121593973500535960249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9556162125298000714613665 7167121593973500535960249)
      ·
        refine ⟨5375341195480125401970187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7167121593973500535960249 5375341195480125401970187)
        ·
          refine ⟨8063011793220188102955281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5375341195480125401970187 8063011793220188102955281)
          ·
            refine ⟨6047258844915141077216461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8063011793220188102955281 6047258844915141077216461)
            ·
              refine ⟨2267722066843177903956173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6047258844915141077216461 2267722066843177903956173)
              ·
                refine ⟨850395775066191713983565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2267722066843177903956173 850395775066191713983565)
                ·
                  refine ⟨318898415649821892743837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 850395775066191713983565 318898415649821892743837)
                  ·
                    rfl

theorem cell20_698684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 3, 3].length) (baseStart_698684 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_698684 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_698684 prefixEnd_698684 := by exact prefixLift 698684
  have htrace : WordTrace (prefixWord ++ tailWord_698684) baseStart_698684 baseEnd_698684 := by
    simpa [prefixWord, tailWord_698684, baseEnd_698684] using wordTrace_append hprefix tailTrace_698684
  have hstable : (prefixWord ++ tailWord_698684).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698684).length < 2 ^ (prefixWord ++ tailWord_698684).sum := by decide
  have hdescent : baseEnd_698684 < baseStart_698684 := by decide
  rcases family_descends (prefixWord ++ tailWord_698684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698712 : List Nat := [2, 1, 2, 2, 1, 1, 2, 1, 8]
def baseStart_698712 : Nat := 118140960795 + 698712 * 2 ^ 59
def prefixEnd_698712 : Nat := 4983230072969 + 3 ^ 40 * 698712 * 2
def baseEnd_698712 : Nat := 318911195612778239810389

theorem tailTrace_698712 : CollatzResearch.WordTrace tailWord_698712 prefixEnd_698712 318911195612778239810389 := by
  unfold tailWord_698712
  simp only [CollatzResearch.WordTrace]
  refine ⟨12742060122346614677161195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16989413496462152902881593 12742060122346614677161195)
  ·
    refine ⟨19113090183519922015741793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12742060122346614677161195 19113090183519922015741793)
    ·
      refine ⟨14334817637639941511806345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19113090183519922015741793 14334817637639941511806345)
      ·
        refine ⟨10751113228229956133854759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14334817637639941511806345 10751113228229956133854759)
        ·
          refine ⟨16126669842344934200782139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10751113228229956133854759 16126669842344934200782139)
          ·
            refine ⟨24190004763517401301173209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16126669842344934200782139 24190004763517401301173209)
            ·
              refine ⟨18142503572638050975879907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24190004763517401301173209 18142503572638050975879907)
              ·
                refine ⟨27213755358957076463819861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18142503572638050975879907 27213755358957076463819861)
                ·
                  refine ⟨318911195612778239810389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27213755358957076463819861 318911195612778239810389)
                  ·
                    rfl

theorem cell20_698712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 8].length) (baseStart_698712 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_698712 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_698712 prefixEnd_698712 := by exact prefixLift 698712
  have htrace : WordTrace (prefixWord ++ tailWord_698712) baseStart_698712 baseEnd_698712 := by
    simpa [prefixWord, tailWord_698712, baseEnd_698712] using wordTrace_append hprefix tailTrace_698712
  have hstable : (prefixWord ++ tailWord_698712).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698712).length < 2 ^ (prefixWord ++ tailWord_698712).sum := by decide
  have hdescent : baseEnd_698712 < baseStart_698712 := by decide
  rcases family_descends (prefixWord ++ tailWord_698712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698725 : List Nat := [1, 3, 1, 3, 1, 3, 4, 2, 2]
def baseStart_698725 : Nat := 118140960795 + 698725 * 2 ^ 59
def prefixEnd_698725 : Nat := 4983230072969 + 3 ^ 40 * 698725 * 2
def baseEnd_698725 : Nat := 318917129167007972377003

theorem tailTrace_698725 : CollatzResearch.WordTrace tailWord_698725 prefixEnd_698725 318917129167007972377003 := by
  unfold tailWord_698725
  simp only [CollatzResearch.WordTrace]
  refine ⟨25484594393646132574545629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16989729595764088383030419 25484594393646132574545629)
  ·
    refine ⟨9556722897617299715454611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25484594393646132574545629 9556722897617299715454611)
    ·
      refine ⟨14335084346425949573181917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9556722897617299715454611 14335084346425949573181917)
      ·
        refine ⟨5375656629909731089943219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14335084346425949573181917 5375656629909731089943219)
        ·
          refine ⟨8063484944864596634914829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5375656629909731089943219 8063484944864596634914829)
          ·
            refine ⟨3023806854324223738093061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8063484944864596634914829 3023806854324223738093061)
            ·
              refine ⟨566963785185791950892449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3023806854324223738093061 566963785185791950892449)
              ·
                refine ⟨425222838889343963169337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 566963785185791950892449 425222838889343963169337)
                ·
                  refine ⟨318917129167007972377003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 425222838889343963169337 318917129167007972377003)
                  ·
                    rfl

theorem cell20_698725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 4, 2, 2].length) (baseStart_698725 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_698725 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_698725 prefixEnd_698725 := by exact prefixLift 698725
  have htrace : WordTrace (prefixWord ++ tailWord_698725) baseStart_698725 baseEnd_698725 := by
    simpa [prefixWord, tailWord_698725, baseEnd_698725] using wordTrace_append hprefix tailTrace_698725
  have hstable : (prefixWord ++ tailWord_698725).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698725).length < 2 ^ (prefixWord ++ tailWord_698725).sum := by decide
  have hdescent : baseEnd_698725 < baseStart_698725 := by decide
  rcases family_descends (prefixWord ++ tailWord_698725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698732 : List Nat := [2, 2, 1, 1, 7, 1, 1, 5]
def baseStart_698732 : Nat := 118140960795 + 698732 * 2 ^ 59
def prefixEnd_698732 : Nat := 4983230072969 + 3 ^ 40 * 698732 * 2
def baseEnd_698732 : Nat := 106306774719249019714547

theorem tailTrace_698732 : CollatzResearch.WordTrace tailWord_698732 prefixEnd_698732 106306774719249019714547 := by
  unfold tailWord_698732
  simp only [CollatzResearch.WordTrace]
  refine ⟨12742424852310386385025225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16989899803080515180033633 12742424852310386385025225)
  ·
    refine ⟨9556818639232789788768919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12742424852310386385025225 9556818639232789788768919)
    ·
      refine ⟨14335227958849184683153379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9556818639232789788768919 14335227958849184683153379)
      ·
        refine ⟨21502841938273777024730069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14335227958849184683153379 21502841938273777024730069)
        ·
          refine ⟨503972857928291649017111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 21502841938273777024730069 503972857928291649017111)
          ·
            refine ⟨755959286892437473525667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 503972857928291649017111 755959286892437473525667)
            ·
              refine ⟨1133938930338656210288501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 755959286892437473525667 1133938930338656210288501)
              ·
                refine ⟨106306774719249019714547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1133938930338656210288501 106306774719249019714547)
                ·
                  rfl

theorem cell20_698732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 1, 5].length) (baseStart_698732 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_698732 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_698732 prefixEnd_698732 := by exact prefixLift 698732
  have htrace : WordTrace (prefixWord ++ tailWord_698732) baseStart_698732 baseEnd_698732 := by
    simpa [prefixWord, tailWord_698732, baseEnd_698732] using wordTrace_append hprefix tailTrace_698732
  have hstable : (prefixWord ++ tailWord_698732).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698732).length < 2 ^ (prefixWord ++ tailWord_698732).sum := by decide
  have hdescent : baseEnd_698732 < baseStart_698732 := by decide
  rcases family_descends (prefixWord ++ tailWord_698732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698736 : List Nat := [2, 1, 1, 1, 4, 3, 3, 5]
def baseStart_698736 : Nat := 118140960795 + 698736 * 2 ^ 59
def prefixEnd_698736 : Nat := 4983230072969 + 3 ^ 40 * 698736 * 2
def baseEnd_698736 : Nat := 106307383288913607670097

theorem tailTrace_698736 : CollatzResearch.WordTrace tailWord_698736 prefixEnd_698736 106307383288913607670097 := by
  unfold tailWord_698736
  simp only [CollatzResearch.WordTrace]
  refine ⟨12742497798303140726598031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16989997064404187635464041 12742497798303140726598031)
  ·
    refine ⟨19113746697454711089897047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12742497798303140726598031 19113746697454711089897047)
    ·
      refine ⟨28670620046182066634845571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19113746697454711089897047 28670620046182066634845571)
      ·
        refine ⟨43005930069273099952268357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28670620046182066634845571 43005930069273099952268357)
        ·
          refine ⟨8063611887988706241050317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43005930069273099952268357 8063611887988706241050317)
          ·
            refine ⟨3023854457995764840393869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8063611887988706241050317 3023854457995764840393869)
            ·
              refine ⟨1133945421748411815147701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3023854457995764840393869 1133945421748411815147701)
              ·
                refine ⟨106307383288913607670097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1133945421748411815147701 106307383288913607670097)
                ·
                  rfl

theorem cell20_698736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 3, 5].length) (baseStart_698736 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_698736 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_698736 prefixEnd_698736 := by exact prefixLift 698736
  have htrace : WordTrace (prefixWord ++ tailWord_698736) baseStart_698736 baseEnd_698736 := by
    simpa [prefixWord, tailWord_698736, baseEnd_698736] using wordTrace_append hprefix tailTrace_698736
  have hstable : (prefixWord ++ tailWord_698736).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698736).length < 2 ^ (prefixWord ++ tailWord_698736).sum := by decide
  have hdescent : baseEnd_698736 < baseStart_698736 := by decide
  rcases family_descends (prefixWord ++ tailWord_698736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698784 : List Nat := [2, 1, 1, 4, 1, 3, 2, 4, 2]
def baseStart_698784 : Nat := 118140960795 + 698784 * 2 ^ 59
def prefixEnd_698784 : Nat := 4983230072969 + 3 ^ 40 * 698784 * 2
def baseEnd_698784 : Nat := 318944058374665989410095

theorem tailTrace_698784 : CollatzResearch.WordTrace tailWord_698784 prefixEnd_698784 318944058374665989410095 := by
  unfold tailWord_698784
  simp only [CollatzResearch.WordTrace]
  refine ⟨12743373150216192825471703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16991164200288257100628937 12743373150216192825471703)
  ·
    refine ⟨19115059725324289238207555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12743373150216192825471703 19115059725324289238207555)
    ·
      refine ⟨28672589587986433857311333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19115059725324289238207555 28672589587986433857311333)
      ·
        refine ⟨5376110547747456348245875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28672589587986433857311333 5376110547747456348245875)
        ·
          refine ⟨8064165821621184522368813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5376110547747456348245875 8064165821621184522368813)
          ·
            refine ⟨3024062183107944195888305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8064165821621184522368813 3024062183107944195888305)
            ·
              refine ⟨2268046637330958146916229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3024062183107944195888305 2268046637330958146916229)
              ·
                refine ⟨425258744499554652546793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2268046637330958146916229 425258744499554652546793)
                ·
                  refine ⟨318944058374665989410095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 425258744499554652546793 318944058374665989410095)
                  ·
                    rfl

theorem cell20_698784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 4, 2].length) (baseStart_698784 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_698784 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_698784 prefixEnd_698784 := by exact prefixLift 698784
  have htrace : WordTrace (prefixWord ++ tailWord_698784) baseStart_698784 baseEnd_698784 := by
    simpa [prefixWord, tailWord_698784, baseEnd_698784] using wordTrace_append hprefix tailTrace_698784
  have hstable : (prefixWord ++ tailWord_698784).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698784).length < 2 ^ (prefixWord ++ tailWord_698784).sum := by decide
  have hdescent : baseEnd_698784 < baseStart_698784 := by decide
  rcases family_descends (prefixWord ++ tailWord_698784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698804 : List Nat := [2, 5, 2, 2, 1, 2, 2, 4]
def baseStart_698804 : Nat := 118140960795 + 698804 * 2 ^ 59
def prefixEnd_698804 : Nat := 4983230072969 + 3 ^ 40 * 698804 * 2
def baseEnd_698804 : Nat := 106317728973211602914449

theorem tailTrace_698804 : CollatzResearch.WordTrace tailWord_698804 prefixEnd_698804 106317728973211602914449 := by
  unfold tailWord_698804
  simp only [CollatzResearch.WordTrace]
  refine ⟨12743737880179964533335733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16991650506906619377780977 12743737880179964533335733)
  ·
    refine ⟨1194725426266871675000225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12743737880179964533335733 1194725426266871675000225)
    ·
      refine ⟨896044069700153756250169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1194725426266871675000225 896044069700153756250169)
      ·
        refine ⟨672033052275115317187627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 896044069700153756250169 672033052275115317187627)
        ·
          refine ⟨1008049578412672975781441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 672033052275115317187627 1008049578412672975781441)
          ·
            refine ⟨756037183809504731836081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1008049578412672975781441 756037183809504731836081)
            ·
              refine ⟨567027887857128548877061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 756037183809504731836081 567027887857128548877061)
              ·
                refine ⟨106317728973211602914449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 567027887857128548877061 106317728973211602914449)
                ·
                  rfl

theorem cell20_698804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 2, 4].length) (baseStart_698804 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_698804 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_698804 prefixEnd_698804 := by exact prefixLift 698804
  have htrace : WordTrace (prefixWord ++ tailWord_698804) baseStart_698804 baseEnd_698804 := by
    simpa [prefixWord, tailWord_698804, baseEnd_698804] using wordTrace_append hprefix tailTrace_698804
  have hstable : (prefixWord ++ tailWord_698804).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698804).length < 2 ^ (prefixWord ++ tailWord_698804).sum := by decide
  have hdescent : baseEnd_698804 < baseStart_698804 := by decide
  rcases family_descends (prefixWord ++ tailWord_698804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698836 : List Nat := [2, 4, 1, 2, 2, 1, 2, 1, 5]
def baseStart_698836 : Nat := 118140960795 + 698836 * 2 ^ 59
def prefixEnd_698836 : Nat := 4983230072969 + 3 ^ 40 * 698836 * 2
def baseEnd_698836 : Nat := 318967792591584919676549

theorem tailTrace_698836 : CollatzResearch.WordTrace tailWord_698836 prefixEnd_698836 318967792591584919676549 := by
  unfold tailWord_698836
  simp only [CollatzResearch.WordTrace]
  refine ⟨12744321448121999265918181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16992428597495999021224241 12744321448121999265918181)
  ·
    refine ⟨2389560271522874862359659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12744321448121999265918181 2389560271522874862359659)
    ·
      refine ⟨3584340407284312293539489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2389560271522874862359659 3584340407284312293539489)
      ·
        refine ⟨2688255305463234220154617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3584340407284312293539489 2688255305463234220154617)
        ·
          refine ⟨2016191479097425665115963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2688255305463234220154617 2016191479097425665115963)
          ·
            refine ⟨3024287218646138497673945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2016191479097425665115963 3024287218646138497673945)
            ·
              refine ⟨2268215413984603873255459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3024287218646138497673945 2268215413984603873255459)
              ·
                refine ⟨3402323120976905809883189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2268215413984603873255459 3402323120976905809883189)
                ·
                  refine ⟨318967792591584919676549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3402323120976905809883189 318967792591584919676549)
                  ·
                    rfl

theorem cell20_698836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_698836 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_698836 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_698836 prefixEnd_698836 := by exact prefixLift 698836
  have htrace : WordTrace (prefixWord ++ tailWord_698836) baseStart_698836 baseEnd_698836 := by
    simpa [prefixWord, tailWord_698836, baseEnd_698836] using wordTrace_append hprefix tailTrace_698836
  have hstable : (prefixWord ++ tailWord_698836).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698836).length < 2 ^ (prefixWord ++ tailWord_698836).sum := by decide
  have hdescent : baseEnd_698836 < baseStart_698836 := by decide
  rcases family_descends (prefixWord ++ tailWord_698836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698853 : List Nat := [1, 3, 1, 5, 2, 1, 1, 3, 3]
def baseStart_698853 : Nat := 118140960795 + 698853 * 2 ^ 59
def prefixEnd_698853 : Nat := 4983230072969 + 3 ^ 40 * 698853 * 2
def baseEnd_698853 : Nat := 318975551854808416109813

theorem tailTrace_698853 : CollatzResearch.WordTrace tailWord_698853 prefixEnd_698853 318975551854808416109813 := by
  unfold tailWord_698853
  simp only [CollatzResearch.WordTrace]
  refine ⟨25489262937182410435205213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16992841958121606956803475 25489262937182410435205213)
  ·
    refine ⟨9558473601443403913201955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25489262937182410435205213 9558473601443403913201955)
    ·
      refine ⟨14337710402165105869802933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9558473601443403913201955 14337710402165105869802933)
      ·
        refine ⟨1344160350202978675294025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14337710402165105869802933 1344160350202978675294025)
        ·
          refine ⟨1008120262652234006470519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1344160350202978675294025 1008120262652234006470519)
          ·
            refine ⟨1512180393978351009705779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1008120262652234006470519 1512180393978351009705779)
            ·
              refine ⟨2268270590967526514558669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1512180393978351009705779 2268270590967526514558669)
              ·
                refine ⟨850601471612822442959501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2268270590967526514558669 850601471612822442959501)
                ·
                  refine ⟨318975551854808416109813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 850601471612822442959501 318975551854808416109813)
                  ·
                    rfl

theorem cell20_698853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 3, 3].length) (baseStart_698853 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_698853 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_698853 prefixEnd_698853 := by exact prefixLift 698853
  have htrace : WordTrace (prefixWord ++ tailWord_698853) baseStart_698853 baseEnd_698853 := by
    simpa [prefixWord, tailWord_698853, baseEnd_698853] using wordTrace_append hprefix tailTrace_698853
  have hstable : (prefixWord ++ tailWord_698853).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698853).length < 2 ^ (prefixWord ++ tailWord_698853).sum := by decide
  have hdescent : baseEnd_698853 < baseStart_698853 := by decide
  rcases family_descends (prefixWord ++ tailWord_698853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698864 : List Nat := [2, 1, 1, 1, 3, 3, 2, 1, 6]
def baseStart_698864 : Nat := 118140960795 + 698864 * 2 ^ 59
def prefixEnd_698864 : Nat := 4983230072969 + 3 ^ 40 * 698864 * 2
def baseEnd_698864 : Nat := 318980572554541266743101

theorem tailTrace_698864 : CollatzResearch.WordTrace tailWord_698864 prefixEnd_698864 318980572554541266743101 := by
  unfold tailWord_698864
  simp only [CollatzResearch.WordTrace]
  refine ⟨12744832070071279656927823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16993109426761706209237097 12744832070071279656927823)
  ·
    refine ⟨19117248105106919485391735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12744832070071279656927823 19117248105106919485391735)
    ·
      refine ⟨28675872157660379228087603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19117248105106919485391735 28675872157660379228087603)
      ·
        refine ⟨43013808236490568842131405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28675872157660379228087603 43013808236490568842131405)
        ·
          refine ⟨16130178088683963315799277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43013808236490568842131405 16130178088683963315799277)
          ·
            refine ⟨6048816783256486243424729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16130178088683963315799277 6048816783256486243424729)
            ·
              refine ⟨4536612587442364682568547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6048816783256486243424729 4536612587442364682568547)
              ·
                refine ⟨6804918881163547023852821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4536612587442364682568547 6804918881163547023852821)
                ·
                  refine ⟨318980572554541266743101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6804918881163547023852821 318980572554541266743101)
                  ·
                    rfl

theorem cell20_698864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 1, 6].length) (baseStart_698864 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_698864 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_698864 prefixEnd_698864 := by exact prefixLift 698864
  have htrace : WordTrace (prefixWord ++ tailWord_698864) baseStart_698864 baseEnd_698864 := by
    simpa [prefixWord, tailWord_698864, baseEnd_698864] using wordTrace_append hprefix tailTrace_698864
  have hstable : (prefixWord ++ tailWord_698864).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698864).length < 2 ^ (prefixWord ++ tailWord_698864).sum := by decide
  have hdescent : baseEnd_698864 < baseStart_698864 := by decide
  rcases family_descends (prefixWord ++ tailWord_698864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698894 : List Nat := [4, 1, 1, 2, 3, 3, 2, 2, 2]
def baseStart_698894 : Nat := 118140960795 + 698894 * 2 ^ 59
def prefixEnd_698894 : Nat := 4983230072969 + 3 ^ 40 * 698894 * 2
def baseEnd_698894 : Nat := 318994265371994495742979

theorem tailTrace_698894 : CollatzResearch.WordTrace tailWord_698894 prefixEnd_698894 318994265371994495742979 := by
  unfold tailWord_698894
  simp only [CollatzResearch.WordTrace]
  refine ⟨3186344791254234304680967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16993838886689249624965157 3186344791254234304680967)
  ·
    refine ⟨4779517186881351457021451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3186344791254234304680967 4779517186881351457021451)
    ·
      refine ⟨7169275780322027185532177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4779517186881351457021451 7169275780322027185532177)
      ·
        refine ⟨5376956835241520389149133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7169275780322027185532177 5376956835241520389149133)
        ·
          refine ⟨2016358813215570145930925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5376956835241520389149133 2016358813215570145930925)
          ·
            refine ⟨756134554955838804724097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2016358813215570145930925 756134554955838804724097)
            ·
              refine ⟨567100916216879103543073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 756134554955838804724097 567100916216879103543073)
              ·
                refine ⟨425325687162659327657305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 567100916216879103543073 425325687162659327657305)
                ·
                  refine ⟨318994265371994495742979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 425325687162659327657305 318994265371994495742979)
                  ·
                    rfl

theorem cell20_698894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 2, 2, 2].length) (baseStart_698894 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_698894 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_698894 prefixEnd_698894 := by exact prefixLift 698894
  have htrace : WordTrace (prefixWord ++ tailWord_698894) baseStart_698894 baseEnd_698894 := by
    simpa [prefixWord, tailWord_698894, baseEnd_698894] using wordTrace_append hprefix tailTrace_698894
  have hstable : (prefixWord ++ tailWord_698894).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698894).length < 2 ^ (prefixWord ++ tailWord_698894).sum := by decide
  have hdescent : baseEnd_698894 < baseStart_698894 := by decide
  rcases family_descends (prefixWord ++ tailWord_698894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698895 : List Nat := [1, 1, 2, 1, 1, 1, 2, 8, 3]
def baseStart_698895 : Nat := 118140960795 + 698895 * 2 ^ 59
def prefixEnd_698895 : Nat := 4983230072969 + 3 ^ 40 * 698895 * 2
def baseEnd_698895 : Nat := 318994721799242936709641

theorem tailTrace_698895 : CollatzResearch.WordTrace tailWord_698895 prefixEnd_698895 318994721799242936709641 := by
  unfold tailWord_698895
  simp only [CollatzResearch.WordTrace]
  refine ⟨25490794803030251608234139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16993863202020167738822759 25490794803030251608234139)
  ·
    refine ⟨38236192204545377412351209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25490794803030251608234139 38236192204545377412351209)
    ·
      refine ⟨28677144153409033059263407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38236192204545377412351209 28677144153409033059263407)
      ·
        refine ⟨43015716230113549588895111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28677144153409033059263407 43015716230113549588895111)
        ·
          refine ⟨64523574345170324383342667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43015716230113549588895111 64523574345170324383342667)
          ·
            refine ⟨96785361517755486575014001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64523574345170324383342667 96785361517755486575014001)
            ·
              refine ⟨72589021138316614931260501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96785361517755486575014001 72589021138316614931260501)
              ·
                refine ⟨850652591464647831225709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 72589021138316614931260501 850652591464647831225709)
                ·
                  refine ⟨318994721799242936709641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 850652591464647831225709 318994721799242936709641)
                  ·
                    rfl

theorem cell20_698895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 8, 3].length) (baseStart_698895 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_698895 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_698895 prefixEnd_698895 := by exact prefixLift 698895
  have htrace : WordTrace (prefixWord ++ tailWord_698895) baseStart_698895 baseEnd_698895 := by
    simpa [prefixWord, tailWord_698895, baseEnd_698895] using wordTrace_append hprefix tailTrace_698895
  have hstable : (prefixWord ++ tailWord_698895).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698895).length < 2 ^ (prefixWord ++ tailWord_698895).sum := by decide
  have hdescent : baseEnd_698895 < baseStart_698895 := by decide
  rcases family_descends (prefixWord ++ tailWord_698895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698933 : List Nat := [1, 3, 3, 1, 1, 2, 2, 2, 5]
def baseStart_698933 : Nat := 118140960795 + 698933 * 2 ^ 59
def prefixEnd_698933 : Nat := 4983230072969 + 3 ^ 40 * 698933 * 2
def baseEnd_698933 : Nat := 319012066034683693442819

theorem tailTrace_698933 : CollatzResearch.WordTrace tailWord_698933 prefixEnd_698933 319012066034683693442819 := by
  unfold tailWord_698933
  simp only [CollatzResearch.WordTrace]
  refine ⟨25492180776892584098117453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16994787184595056065411635 25492180776892584098117453)
  ·
    refine ⟨9559567791334719036794045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25492180776892584098117453 9559567791334719036794045)
    ·
      refine ⟨3584837921750519638797767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9559567791334719036794045 3584837921750519638797767)
      ·
        refine ⟨5377256882625779458196651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3584837921750519638797767 5377256882625779458196651)
        ·
          refine ⟨8065885323938669187294977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5377256882625779458196651 8065885323938669187294977)
          ·
            refine ⟨6049413992954001890471233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8065885323938669187294977 6049413992954001890471233)
            ·
              refine ⟨4537060494715501417853425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6049413992954001890471233 4537060494715501417853425)
              ·
                refine ⟨3402795371036626063390069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4537060494715501417853425 3402795371036626063390069)
                ·
                  refine ⟨319012066034683693442819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3402795371036626063390069 319012066034683693442819)
                  ·
                    rfl

theorem cell20_698933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 2, 5].length) (baseStart_698933 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_698933 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_698933 prefixEnd_698933 := by exact prefixLift 698933
  have htrace : WordTrace (prefixWord ++ tailWord_698933) baseStart_698933 baseEnd_698933 := by
    simpa [prefixWord, tailWord_698933, baseEnd_698933] using wordTrace_append hprefix tailTrace_698933
  have hstable : (prefixWord ++ tailWord_698933).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698933).length < 2 ^ (prefixWord ++ tailWord_698933).sum := by decide
  have hdescent : baseEnd_698933 < baseStart_698933 := by decide
  rcases family_descends (prefixWord ++ tailWord_698933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698936 : List Nat := [2, 1, 2, 1, 4, 1, 4, 3, 2]
def baseStart_698936 : Nat := 118140960795 + 698936 * 2 ^ 59
def prefixEnd_698936 : Nat := 4983230072969 + 3 ^ 40 * 698936 * 2
def baseEnd_698936 : Nat := 319013435316429016342807

theorem tailTrace_698936 : CollatzResearch.WordTrace tailWord_698936 prefixEnd_698936 319013435316429016342807 := by
  unfold tailWord_698936
  simp only [CollatzResearch.WordTrace]
  refine ⟨12746145097940857805238331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16994860130587810406984441 12746145097940857805238331)
  ·
    refine ⟨19119217646911286707857497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12746145097940857805238331 19119217646911286707857497)
    ·
      refine ⟨14339413235183465030893123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19119217646911286707857497 14339413235183465030893123)
      ·
        refine ⟨21509119852775197546339685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14339413235183465030893123 21509119852775197546339685)
        ·
          refine ⟨4032959972395349539938691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21509119852775197546339685 4032959972395349539938691)
          ·
            refine ⟨6049439958593024309908037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4032959972395349539938691 6049439958593024309908037)
            ·
              refine ⟨1134269992236192058107757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6049439958593024309908037 1134269992236192058107757)
              ·
                refine ⟨425351247088572021790409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1134269992236192058107757 425351247088572021790409)
                ·
                  refine ⟨319013435316429016342807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 425351247088572021790409 319013435316429016342807)
                  ·
                    rfl

theorem cell20_698936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 4, 3, 2].length) (baseStart_698936 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_698936 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_698936 prefixEnd_698936 := by exact prefixLift 698936
  have htrace : WordTrace (prefixWord ++ tailWord_698936) baseStart_698936 baseEnd_698936 := by
    simpa [prefixWord, tailWord_698936, baseEnd_698936] using wordTrace_append hprefix tailTrace_698936
  have hstable : (prefixWord ++ tailWord_698936).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698936).length < 2 ^ (prefixWord ++ tailWord_698936).sum := by decide
  have hdescent : baseEnd_698936 < baseStart_698936 := by decide
  rcases family_descends (prefixWord ++ tailWord_698936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698995 : List Nat := [1, 1, 1, 2, 2, 1, 1, 9, 2]
def baseStart_698995 : Nat := 118140960795 + 698995 * 2 ^ 59
def prefixEnd_698995 : Nat := 4983230072969 + 3 ^ 40 * 698995 * 2
def baseEnd_698995 : Nat := 319040364524087033375899

theorem tailTrace_698995 : CollatzResearch.WordTrace tailWord_698995 prefixEnd_698995 319040364524087033375899 := by
  unfold tailWord_698995
  simp only [CollatzResearch.WordTrace]
  refine ⟨25494442102667968686874439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16996294735111979124582959 25494442102667968686874439)
  ·
    refine ⟨38241663154001953030311659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25494442102667968686874439 38241663154001953030311659)
    ·
      refine ⟨57362494731002929545467489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38241663154001953030311659 57362494731002929545467489)
      ·
        refine ⟨43021871048252197159100617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57362494731002929545467489 43021871048252197159100617)
        ·
          refine ⟨32266403286189147869325463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43021871048252197159100617 32266403286189147869325463)
          ·
            refine ⟨48399604929283721803988195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32266403286189147869325463 48399604929283721803988195)
            ·
              refine ⟨72599407393925582705982293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48399604929283721803988195 72599407393925582705982293)
              ·
                refine ⟨425387152698782711167865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 72599407393925582705982293 425387152698782711167865)
                ·
                  refine ⟨319040364524087033375899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 425387152698782711167865 319040364524087033375899)
                  ·
                    rfl

theorem cell20_698995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 9, 2].length) (baseStart_698995 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_698995 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_698995 prefixEnd_698995 := by exact prefixLift 698995
  have htrace : WordTrace (prefixWord ++ tailWord_698995) baseStart_698995 baseEnd_698995 := by
    simpa [prefixWord, tailWord_698995, baseEnd_698995] using wordTrace_append hprefix tailTrace_698995
  have hstable : (prefixWord ++ tailWord_698995).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698995).length < 2 ^ (prefixWord ++ tailWord_698995).sum := by decide
  have hdescent : baseEnd_698995 < baseStart_698995 := by decide
  rcases family_descends (prefixWord ++ tailWord_698995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_698998 : List Nat := [5, 1, 1, 2, 4, 1, 6]
def baseStart_698998 : Nat := 118140960795 + 698998 * 2 ^ 59
def prefixEnd_698998 : Nat := 4983230072969 + 3 ^ 40 * 698998 * 2
def baseEnd_698998 : Nat := 35449081533981372919543

theorem tailTrace_698998 : CollatzResearch.WordTrace tailWord_698998 prefixEnd_698998 35449081533981372919543 := by
  unfold tailWord_698998
  simp only [CollatzResearch.WordTrace]
  refine ⟨1593409470103568762452103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16996367681104733466155765 1593409470103568762452103)
  ·
    refine ⟨2390114205155353143678155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1593409470103568762452103 2390114205155353143678155)
    ·
      refine ⟨3585171307733029715517233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2390114205155353143678155 3585171307733029715517233)
      ·
        refine ⟨2688878480799772286637925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3585171307733029715517233 2688878480799772286637925)
        ·
          refine ⟨504164715149957303744611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2688878480799772286637925 504164715149957303744611)
          ·
            refine ⟨756247072724935955616917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 504164715149957303744611 756247072724935955616917)
            ·
              refine ⟨35449081533981372919543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 756247072724935955616917 35449081533981372919543)
              ·
                rfl

theorem cell20_698998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 6].length) (baseStart_698998 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_698998 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_698998 prefixEnd_698998 := by exact prefixLift 698998
  have htrace : WordTrace (prefixWord ++ tailWord_698998) baseStart_698998 baseEnd_698998 := by
    simpa [prefixWord, tailWord_698998, baseEnd_698998] using wordTrace_append hprefix tailTrace_698998
  have hstable : (prefixWord ++ tailWord_698998).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_698998).length < 2 ^ (prefixWord ++ tailWord_698998).sum := by decide
  have hdescent : baseEnd_698998 < baseStart_698998 := by decide
  rcases family_descends (prefixWord ++ tailWord_698998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699009 : List Nat := [1, 2, 4, 2, 1, 1, 1, 3, 5]
def baseStart_699009 : Nat := 118140960795 + 699009 * 2 ^ 59
def prefixEnd_699009 : Nat := 4983230072969 + 3 ^ 40 * 699009 * 2
def baseEnd_699009 : Nat := 319046754505565206909175

theorem tailTrace_699009 : CollatzResearch.WordTrace tailWord_699009 prefixEnd_699009 319046754505565206909175 := by
  unfold tailWord_699009
  simp only [CollatzResearch.WordTrace]
  refine ⟨25494952724617249077884081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16996635149744832718589387 25494952724617249077884081)
  ·
    refine ⟨19121214543462936808413061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25494952724617249077884081 19121214543462936808413061)
    ·
      refine ⟨3585227726899300651577449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19121214543462936808413061 3585227726899300651577449)
      ·
        refine ⟨2688920795174475488683087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3585227726899300651577449 2688920795174475488683087)
        ·
          refine ⟨4033381192761713233024631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2688920795174475488683087 4033381192761713233024631)
          ·
            refine ⟨6050071789142569849536947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4033381192761713233024631 6050071789142569849536947)
            ·
              refine ⟨9075107683713854774305421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6050071789142569849536947 9075107683713854774305421)
              ·
                refine ⟨3403165381392695540364533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9075107683713854774305421 3403165381392695540364533)
                ·
                  refine ⟨319046754505565206909175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3403165381392695540364533 319046754505565206909175)
                  ·
                    rfl

theorem cell20_699009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 3, 5].length) (baseStart_699009 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_699009 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_699009 prefixEnd_699009 := by exact prefixLift 699009
  have htrace : WordTrace (prefixWord ++ tailWord_699009) baseStart_699009 baseEnd_699009 := by
    simpa [prefixWord, tailWord_699009, baseEnd_699009] using wordTrace_append hprefix tailTrace_699009
  have hstable : (prefixWord ++ tailWord_699009).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699009).length < 2 ^ (prefixWord ++ tailWord_699009).sum := by decide
  have hdescent : baseEnd_699009 < baseStart_699009 := by decide
  rcases family_descends (prefixWord ++ tailWord_699009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699012 : List Nat := [2, 3, 2, 1, 3, 3, 1, 1, 4]
def baseStart_699012 : Nat := 118140960795 + 699012 * 2 ^ 59
def prefixEnd_699012 : Nat := 4983230072969 + 3 ^ 40 * 699012 * 2
def baseEnd_699012 : Nat := 319048123787310529809163

theorem tailTrace_699012 : CollatzResearch.WordTrace tailWord_699012 prefixEnd_699012 319048123787310529809163 := by
  unfold tailWord_699012
  simp only [CollatzResearch.WordTrace]
  refine ⟨12747531071803190295121645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16996708095737587060162193 12747531071803190295121645)
  ·
    refine ⟨4780324151926196360670617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12747531071803190295121645 4780324151926196360670617)
    ·
      refine ⟨3585243113944647270502963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4780324151926196360670617 3585243113944647270502963)
      ·
        refine ⟨5377864670916970905754445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3585243113944647270502963 5377864670916970905754445)
        ·
          refine ⟨2016699251593864089657917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5377864670916970905754445 2016699251593864089657917)
          ·
            refine ⟨756262219347699033621719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2016699251593864089657917 756262219347699033621719)
            ·
              refine ⟨1134393329021548550432579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 756262219347699033621719 1134393329021548550432579)
              ·
                refine ⟨1701589993532322825648869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1134393329021548550432579 1701589993532322825648869)
                ·
                  refine ⟨319048123787310529809163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1701589993532322825648869 319048123787310529809163)
                  ·
                    rfl

theorem cell20_699012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 1, 1, 4].length) (baseStart_699012 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_699012 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_699012 prefixEnd_699012 := by exact prefixLift 699012
  have htrace : WordTrace (prefixWord ++ tailWord_699012) baseStart_699012 baseEnd_699012 := by
    simpa [prefixWord, tailWord_699012, baseEnd_699012] using wordTrace_append hprefix tailTrace_699012
  have hstable : (prefixWord ++ tailWord_699012).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699012).length < 2 ^ (prefixWord ++ tailWord_699012).sum := by decide
  have hdescent : baseEnd_699012 < baseStart_699012 := by decide
  rcases family_descends (prefixWord ++ tailWord_699012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699057 : List Nat := [1, 2, 2, 6, 2, 7]
def baseStart_699057 : Nat := 118140960795 + 699057 * 2 ^ 59
def prefixEnd_699057 : Nat := 4983230072969 + 3 ^ 40 * 699057 * 2
def baseEnd_699057 : Nat := 11817357889388532344777

theorem tailTrace_699057 : CollatzResearch.WordTrace tailWord_699057 prefixEnd_699057 11817357889388532344777 := by
  unfold tailWord_699057
  simp only [CollatzResearch.WordTrace]
  refine ⟨25496703428443353275631425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16997802285628902183754283 25496703428443353275631425)
  ·
    refine ⟨19122527571332514956723569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25496703428443353275631425 19122527571332514956723569)
    ·
      refine ⟨14341895678499386217542677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19122527571332514956723569 14341895678499386217542677)
      ·
        refine ⟨672276359929658728947313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 14341895678499386217542677 672276359929658728947313)
        ·
          refine ⟨504207269947244046710485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 672276359929658728947313 504207269947244046710485)
          ·
            refine ⟨11817357889388532344777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 504207269947244046710485 11817357889388532344777)
            ·
              rfl

theorem cell20_699057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 7].length) (baseStart_699057 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_699057 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_699057 prefixEnd_699057 := by exact prefixLift 699057
  have htrace : WordTrace (prefixWord ++ tailWord_699057) baseStart_699057 baseEnd_699057 := by
    simpa [prefixWord, tailWord_699057, baseEnd_699057] using wordTrace_append hprefix tailTrace_699057
  have hstable : (prefixWord ++ tailWord_699057).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699057).length < 2 ^ (prefixWord ++ tailWord_699057).sum := by decide
  have hdescent : baseEnd_699057 < baseStart_699057 := by decide
  rcases family_descends (prefixWord ++ tailWord_699057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_699126 : List Nat := [5, 1, 1, 1, 1, 2, 1, 6, 2]
def baseStart_699126 : Nat := 118140960795 + 699126 * 2 ^ 59
def prefixEnd_699126 : Nat := 4983230072969 + 3 ^ 40 * 699126 * 2
def baseEnd_699126 : Nat := 319100156493632800008697

theorem tailTrace_699126 : CollatzResearch.WordTrace tailWord_699126 prefixEnd_699126 319100156493632800008697 := by
  unfold tailWord_699126
  simp only [CollatzResearch.WordTrace]
  refine ⟨1593701254074586128743327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16999480043462252039928821 1593701254074586128743327)
  ·
    refine ⟨2390551881111879193114991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1593701254074586128743327 2390551881111879193114991)
    ·
      refine ⟨3585827821667818789672487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2390551881111879193114991 3585827821667818789672487)
      ·
        refine ⟨5378741732501728184508731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3585827821667818789672487 5378741732501728184508731)
        ·
          refine ⟨8068112598752592276763097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5378741732501728184508731 8068112598752592276763097)
          ·
            refine ⟨6051084449064444207572323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8068112598752592276763097 6051084449064444207572323)
            ·
              refine ⟨9076626673596666311358485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6051084449064444207572323 9076626673596666311358485)
              ·
                refine ⟨425466875324843733344929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9076626673596666311358485 425466875324843733344929)
                ·
                  refine ⟨319100156493632800008697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 425466875324843733344929 319100156493632800008697)
                  ·
                    rfl

theorem cell20_699126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 6, 2].length) (baseStart_699126 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_699126 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_699126 prefixEnd_699126 := by exact prefixLift 699126
  have htrace : WordTrace (prefixWord ++ tailWord_699126) baseStart_699126 baseEnd_699126 := by
    simpa [prefixWord, tailWord_699126, baseEnd_699126] using wordTrace_append hprefix tailTrace_699126
  have hstable : (prefixWord ++ tailWord_699126).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_699126).length < 2 ^ (prefixWord ++ tailWord_699126).sum := by decide
  have hdescent : baseEnd_699126 < baseStart_699126 := by decide
  rcases family_descends (prefixWord ++ tailWord_699126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
