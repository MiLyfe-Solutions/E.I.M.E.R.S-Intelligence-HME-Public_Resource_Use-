import V185TrunkScan23Chunk0620

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3672285 : List Nat := [1, 4, 3, 2, 1, 1, 3, 2, 1, 2, 3]
def baseStart_3672285 : Nat := 118140960795 + 3672285 * 2 ^ 59
def prefixEnd_3672285 : Nat := 4983230072969 + 3 ^ 40 * 3672285 * 2
def baseEnd_3672285 : Nat := 1885647305296269901748975

theorem tailTrace_3672285 : CollatzResearch.WordTrace tailWord_3672285 prefixEnd_3672285 1885647305296269901748975 := by
  unfold tailWord_3672285
  simp only [CollatzResearch.WordTrace]
  refine ⟨133939237500946096191050309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89292825000630730794033539 133939237500946096191050309)
  ·
    refine ⟨25113607031427393035821933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133939237500946096191050309 25113607031427393035821933)
    ·
      refine ⟨9417602636785272388433225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25113607031427393035821933 9417602636785272388433225)
      ·
        refine ⟨7063201977588954291324919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9417602636785272388433225 7063201977588954291324919)
        ·
          refine ⟨10594802966383431436987379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7063201977588954291324919 10594802966383431436987379)
          ·
            refine ⟨15892204449575147155481069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10594802966383431436987379 15892204449575147155481069)
            ·
              refine ⟨5959576668590680183305401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15892204449575147155481069 5959576668590680183305401)
              ·
                refine ⟨4469682501443010137479051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5959576668590680183305401 4469682501443010137479051)
                ·
                  refine ⟨6704523752164515206218577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4469682501443010137479051 6704523752164515206218577)
                  ·
                    refine ⟨5028392814123386404663933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6704523752164515206218577 5028392814123386404663933)
                    ·
                      refine ⟨1885647305296269901748975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5028392814123386404663933 1885647305296269901748975)
                      ·
                        rfl

theorem cell23_3672285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_3672285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3672285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3672285 prefixEnd_3672285 := by exact prefixLift 3672285
  have htrace : WordTrace (prefixWord ++ tailWord_3672285) baseStart_3672285 baseEnd_3672285 := by
    simpa [prefixWord, tailWord_3672285, baseEnd_3672285] using wordTrace_append hprefix tailTrace_3672285
  have hstable : (prefixWord ++ tailWord_3672285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3672285).length < 2 ^ (prefixWord ++ tailWord_3672285).sum := by decide
  have hdescent : baseEnd_3672285 < baseStart_3672285 := by decide
  rcases family_descends (prefixWord ++ tailWord_3672285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3672304 : List Nat := [2, 1, 1, 1, 3, 1, 1, 2, 4, 3, 4]
def baseStart_3672304 : Nat := 118140960795 + 3672304 * 2 ^ 59
def prefixEnd_3672304 : Nat := 4983230072969 + 3 ^ 40 * 3672304 * 2
def baseEnd_3672304 : Nat := 1885657061428705327411387

theorem tailTrace_3672304 : CollatzResearch.WordTrace tailWord_3672304 prefixEnd_3672304 1885657061428705327411387 := by
  unfold tailWord_3672304
  simp only [CollatzResearch.WordTrace]
  refine ⟨66969965243938631217995983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89293286991918174957327977 66969965243938631217995983)
  ·
    refine ⟨100454947865907946826993975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66969965243938631217995983 100454947865907946826993975)
    ·
      refine ⟨150682421798861920240490963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100454947865907946826993975 150682421798861920240490963)
      ·
        refine ⟨226023632698292880360736445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150682421798861920240490963 226023632698292880360736445)
        ·
          refine ⟨84758862261859830135276167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 226023632698292880360736445 84758862261859830135276167)
          ·
            refine ⟨127138293392789745202914251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84758862261859830135276167 127138293392789745202914251)
            ·
              refine ⟨190707440089184617804371377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127138293392789745202914251 190707440089184617804371377)
              ·
                refine ⟨143030580066888463353278533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 190707440089184617804371377 143030580066888463353278533)
                ·
                  refine ⟨26818233762541586878739725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 143030580066888463353278533 26818233762541586878739725)
                  ·
                    refine ⟨10056837660953095079527397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26818233762541586878739725 10056837660953095079527397)
                    ·
                      refine ⟨1885657061428705327411387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10056837660953095079527397 1885657061428705327411387)
                      ·
                        rfl

theorem cell23_3672304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 4, 3, 4].length) (baseStart_3672304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3672304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3672304 prefixEnd_3672304 := by exact prefixLift 3672304
  have htrace : WordTrace (prefixWord ++ tailWord_3672304) baseStart_3672304 baseEnd_3672304 := by
    simpa [prefixWord, tailWord_3672304, baseEnd_3672304] using wordTrace_append hprefix tailTrace_3672304
  have hstable : (prefixWord ++ tailWord_3672304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3672304).length < 2 ^ (prefixWord ++ tailWord_3672304).sum := by decide
  have hdescent : baseEnd_3672304 < baseStart_3672304 := by decide
  rcases family_descends (prefixWord ++ tailWord_3672304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3672366 : List Nat := [4, 1, 3, 3, 2, 1, 1, 2, 2, 1, 3]
def baseStart_3672366 : Nat := 118140960795 + 3672366 * 2 ^ 59
def prefixEnd_3672366 : Nat := 4983230072969 + 3 ^ 40 * 3672366 * 2
def baseEnd_3672366 : Nat := 1885688897229284084836103

theorem tailTrace_3672366 : CollatzResearch.WordTrace tailWord_3672366 prefixEnd_3672366 1885688897229284084836103 := by
  unfold tailWord_3672366
  simp only [CollatzResearch.WordTrace]
  refine ⟨16742773976706580878093619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89294794542435098016499301 16742773976706580878093619)
  ·
    refine ⟨25114160965059871317140429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16742773976706580878093619 25114160965059871317140429)
    ·
      refine ⟨9417810361897451743927661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25114160965059871317140429 9417810361897451743927661)
      ·
        refine ⟨3531678885711544403972873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9417810361897451743927661 3531678885711544403972873)
        ·
          refine ⟨2648759164283658302979655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3531678885711544403972873 2648759164283658302979655)
          ·
            refine ⟨3973138746425487454469483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2648759164283658302979655 3973138746425487454469483)
            ·
              refine ⟨5959708119638231181704225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3973138746425487454469483 5959708119638231181704225)
              ·
                refine ⟨4469781089728673386278169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5959708119638231181704225 4469781089728673386278169)
                ·
                  refine ⟨3352335817296505039708627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4469781089728673386278169 3352335817296505039708627)
                  ·
                    refine ⟨5028503725944757559562941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3352335817296505039708627 5028503725944757559562941)
                    ·
                      refine ⟨1885688897229284084836103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5028503725944757559562941 1885688897229284084836103)
                      ·
                        rfl

theorem cell23_3672366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_3672366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3672366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3672366 prefixEnd_3672366 := by exact prefixLift 3672366
  have htrace : WordTrace (prefixWord ++ tailWord_3672366) baseStart_3672366 baseEnd_3672366 := by
    simpa [prefixWord, tailWord_3672366, baseEnd_3672366] using wordTrace_append hprefix tailTrace_3672366
  have hstable : (prefixWord ++ tailWord_3672366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3672366).length < 2 ^ (prefixWord ++ tailWord_3672366).sum := by decide
  have hdescent : baseEnd_3672366 < baseStart_3672366 := by decide
  rcases family_descends (prefixWord ++ tailWord_3672366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3672371 : List Nat := [1, 1, 1, 2, 5, 1, 1, 1, 4, 3, 3]
def baseStart_3672371 : Nat := 118140960795 + 3672371 * 2 ^ 59
def prefixEnd_3672371 : Nat := 4983230072969 + 3 ^ 40 * 3672371 * 2
def baseEnd_3672371 : Nat := 1885691464632556565273579

theorem tailTrace_3672371 : CollatzResearch.WordTrace tailWord_3672371 prefixEnd_3672371 1885691464632556565273579 := by
  unfold tailWord_3672371
  simp only [CollatzResearch.WordTrace]
  refine ⟨133942374178634532878680967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89294916119089688585787311 133942374178634532878680967)
  ·
    refine ⟨200913561267951799318021451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133942374178634532878680967 200913561267951799318021451)
    ·
      refine ⟨301370341901927698977032177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200913561267951799318021451 301370341901927698977032177)
      ·
        refine ⟨226027756426445774232774133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 301370341901927698977032177 226027756426445774232774133)
        ·
          refine ⟨21190102164979291334322575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 226027756426445774232774133 21190102164979291334322575)
          ·
            refine ⟨31785153247468937001483863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21190102164979291334322575 31785153247468937001483863)
            ·
              refine ⟨47677729871203405502225795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31785153247468937001483863 47677729871203405502225795)
              ·
                refine ⟨71516594806805108253338693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47677729871203405502225795 71516594806805108253338693)
                ·
                  refine ⟨13409361526275957797501005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71516594806805108253338693 13409361526275957797501005)
                  ·
                    refine ⟨5028510572353484174062877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13409361526275957797501005 5028510572353484174062877)
                    ·
                      refine ⟨1885691464632556565273579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5028510572353484174062877 1885691464632556565273579)
                      ·
                        rfl

theorem cell23_3672371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 1, 4, 3, 3].length) (baseStart_3672371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3672371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3672371 prefixEnd_3672371 := by exact prefixLift 3672371
  have htrace : WordTrace (prefixWord ++ tailWord_3672371) baseStart_3672371 baseEnd_3672371 := by
    simpa [prefixWord, tailWord_3672371, baseEnd_3672371] using wordTrace_append hprefix tailTrace_3672371
  have hstable : (prefixWord ++ tailWord_3672371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3672371).length < 2 ^ (prefixWord ++ tailWord_3672371).sum := by decide
  have hdescent : baseEnd_3672371 < baseStart_3672371 := by decide
  rcases family_descends (prefixWord ++ tailWord_3672371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3672372 : List Nat := [2, 5, 1, 1, 1, 3, 1, 1, 4, 2, 2]
def baseStart_3672372 : Nat := 118140960795 + 3672372 * 2 ^ 59
def prefixEnd_3672372 : Nat := 4983230072969 + 3 ^ 40 * 3672372 * 2
def baseEnd_3672372 : Nat := 1885691978113211061361075

theorem tailTrace_3672372 : CollatzResearch.WordTrace tailWord_3672372 prefixEnd_3672372 1885691978113211061361075 := by
  unfold tailWord_3672372
  simp only [CollatzResearch.WordTrace]
  refine ⟨66971205325815455024733685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89294940434420606699644913 66971205325815455024733685)
  ·
    refine ⟨6278550499295198908568783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 66971205325815455024733685 6278550499295198908568783)
    ·
      refine ⟨9417825748942798362853175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6278550499295198908568783 9417825748942798362853175)
      ·
        refine ⟨14126738623414197544279763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9417825748942798362853175 14126738623414197544279763)
        ·
          refine ⟨21190107935121296316419645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14126738623414197544279763 21190107935121296316419645)
          ·
            refine ⟨7946290475670486118657367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21190107935121296316419645 7946290475670486118657367)
            ·
              refine ⟨11919435713505729177986051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7946290475670486118657367 11919435713505729177986051)
              ·
                refine ⟨17879153570258593766979077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11919435713505729177986051 17879153570258593766979077)
                ·
                  refine ⟨3352341294423486331308577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17879153570258593766979077 3352341294423486331308577)
                  ·
                    refine ⟨2514255970817614748481433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3352341294423486331308577 2514255970817614748481433)
                    ·
                      refine ⟨1885691978113211061361075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2514255970817614748481433 1885691978113211061361075)
                      ·
                        rfl

theorem cell23_3672372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 1, 4, 2, 2].length) (baseStart_3672372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3672372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3672372 prefixEnd_3672372 := by exact prefixLift 3672372
  have htrace : WordTrace (prefixWord ++ tailWord_3672372) baseStart_3672372 baseEnd_3672372 := by
    simpa [prefixWord, tailWord_3672372, baseEnd_3672372] using wordTrace_append hprefix tailTrace_3672372
  have hstable : (prefixWord ++ tailWord_3672372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3672372).length < 2 ^ (prefixWord ++ tailWord_3672372).sum := by decide
  have hdescent : baseEnd_3672372 < baseStart_3672372 := by decide
  rcases family_descends (prefixWord ++ tailWord_3672372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3672378 : List Nat := [3, 1, 1, 1, 4, 2, 2, 4, 5]
def baseStart_3672378 : Nat := 118140960795 + 3672378 * 2 ^ 59
def prefixEnd_3672378 : Nat := 4983230072969 + 3 ^ 40 * 3672378 * 2
def baseEnd_3672378 : Nat := 209521673221904226431783

theorem tailTrace_3672378 : CollatzResearch.WordTrace tailWord_3672378 prefixEnd_3672378 209521673221904226431783 := by
  unfold tailWord_3672378
  simp only [CollatzResearch.WordTrace]
  refine ⟨33485657372402293268546447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89295086326406115382790525 33485657372402293268546447)
  ·
    refine ⟨50228486058603439902819671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33485657372402293268546447 50228486058603439902819671)
    ·
      refine ⟨75342729087905159854229507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50228486058603439902819671 75342729087905159854229507)
      ·
        refine ⟨113014093631857739781344261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75342729087905159854229507 113014093631857739781344261)
        ·
          refine ⟨21190142555973326209002049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 113014093631857739781344261 21190142555973326209002049)
          ·
            refine ⟨15892606916979994656751537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21190142555973326209002049 15892606916979994656751537)
            ·
              refine ⟨11919455187734995992563653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15892606916979994656751537 11919455187734995992563653)
              ·
                refine ⟨2234897847700311748605685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11919455187734995992563653 2234897847700311748605685)
                ·
                  refine ⟨209521673221904226431783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2234897847700311748605685 209521673221904226431783)
                  ·
                    rfl

theorem cell23_3672378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 4, 5].length) (baseStart_3672378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3672378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3672378 prefixEnd_3672378 := by exact prefixLift 3672378
  have htrace : WordTrace (prefixWord ++ tailWord_3672378) baseStart_3672378 baseEnd_3672378 := by
    simpa [prefixWord, tailWord_3672378, baseEnd_3672378] using wordTrace_append hprefix tailTrace_3672378
  have hstable : (prefixWord ++ tailWord_3672378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3672378).length < 2 ^ (prefixWord ++ tailWord_3672378).sum := by decide
  have hdescent : baseEnd_3672378 < baseStart_3672378 := by decide
  rcases family_descends (prefixWord ++ tailWord_3672378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3672431 : List Nat := [1, 1, 2, 1, 3, 1, 2, 2, 3, 4, 3]
def baseStart_3672431 : Nat := 118140960795 + 3672431 * 2 ^ 59
def prefixEnd_3672431 : Nat := 4983230072969 + 3 ^ 40 * 3672431 * 2
def baseEnd_3672431 : Nat := 1885722273471826330523303

theorem tailTrace_3672431 : CollatzResearch.WordTrace tailWord_3672431 prefixEnd_3672431 1885722273471826330523303 := by
  unfold tailWord_3672431
  simp only [CollatzResearch.WordTrace]
  refine ⟨133944562558417163125865147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89296375038944775417243431 133944562558417163125865147)
  ·
    refine ⟨200916843837625744688797721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133944562558417163125865147 200916843837625744688797721)
    ·
      refine ⟨150687632878219308516598291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200916843837625744688797721 150687632878219308516598291)
      ·
        refine ⟨226031449317328962774897437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150687632878219308516598291 226031449317328962774897437)
        ·
          refine ⟨84761793493998361040586539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 226031449317328962774897437 84761793493998361040586539)
          ·
            refine ⟨127142690240997541560879809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84761793493998361040586539 127142690240997541560879809)
            ·
              refine ⟨95357017680748156170659857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127142690240997541560879809 95357017680748156170659857)
              ·
                refine ⟨71517763260561117127994893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95357017680748156170659857 71517763260561117127994893)
                ·
                  refine ⟨26819161222710418922998085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71517763260561117127994893 26819161222710418922998085)
                  ·
                    refine ⟨5028592729258203548062141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26819161222710418922998085 5028592729258203548062141)
                    ·
                      refine ⟨1885722273471826330523303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5028592729258203548062141 1885722273471826330523303)
                      ·
                        rfl

theorem cell23_3672431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 2, 3, 4, 3].length) (baseStart_3672431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3672431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3672431 prefixEnd_3672431 := by exact prefixLift 3672431
  have htrace : WordTrace (prefixWord ++ tailWord_3672431) baseStart_3672431 baseEnd_3672431 := by
    simpa [prefixWord, tailWord_3672431, baseEnd_3672431] using wordTrace_append hprefix tailTrace_3672431
  have hstable : (prefixWord ++ tailWord_3672431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3672431).length < 2 ^ (prefixWord ++ tailWord_3672431).sum := by decide
  have hdescent : baseEnd_3672431 < baseStart_3672431 := by decide
  rcases family_descends (prefixWord ++ tailWord_3672431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3672531 : List Nat := [1, 1, 1, 2, 1, 1, 1, 1, 4, 6, 4]
def baseStart_3672531 : Nat := 118140960795 + 3672531 * 2 ^ 59
def prefixEnd_3672531 : Nat := 4983230072969 + 3 ^ 40 * 3672531 * 2
def baseEnd_3672531 : Nat := 1885773621537275939272843

theorem tailTrace_3672531 : CollatzResearch.WordTrace tailWord_3672531 prefixEnd_3672531 1885773621537275939272843 := by
  unfold tailWord_3672531
  simp only [CollatzResearch.WordTrace]
  refine ⟨133948209858054880204505447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89298806572036586803003631 133948209858054880204505447)
  ·
    refine ⟨200922314787082320306758171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133948209858054880204505447 200922314787082320306758171)
    ·
      refine ⟨301383472180623480460137257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200922314787082320306758171 301383472180623480460137257)
      ·
        refine ⟨226037604135467610345102943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 301383472180623480460137257 226037604135467610345102943)
        ·
          refine ⟨339056406203201415517654415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226037604135467610345102943 339056406203201415517654415)
          ·
            refine ⟨508584609304802123276481623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 339056406203201415517654415 508584609304802123276481623)
            ·
              refine ⟨762876913957203184914722435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 508584609304802123276481623 762876913957203184914722435)
              ·
                refine ⟨1144315370935804777372083653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 762876913957203184914722435 1144315370935804777372083653)
                ·
                  refine ⟨214559132050463395757265685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1144315370935804777372083653 214559132050463395757265685)
                  ·
                    refine ⟨10057459314865471676121829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 214559132050463395757265685 10057459314865471676121829)
                    ·
                      refine ⟨1885773621537275939272843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10057459314865471676121829 1885773621537275939272843)
                      ·
                        rfl

theorem cell23_3672531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 6, 4].length) (baseStart_3672531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3672531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3672531 prefixEnd_3672531 := by exact prefixLift 3672531
  have htrace : WordTrace (prefixWord ++ tailWord_3672531) baseStart_3672531 baseEnd_3672531 := by
    simpa [prefixWord, tailWord_3672531, baseEnd_3672531] using wordTrace_append hprefix tailTrace_3672531
  have hstable : (prefixWord ++ tailWord_3672531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3672531).length < 2 ^ (prefixWord ++ tailWord_3672531).sum := by decide
  have hdescent : baseEnd_3672531 < baseStart_3672531 := by decide
  rcases family_descends (prefixWord ++ tailWord_3672531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3672532 : List Nat := [2, 4, 1, 2, 2, 1, 4, 1, 1, 5]
def baseStart_3672532 : Nat := 118140960795 + 3672532 * 2 ^ 59
def prefixEnd_3672532 : Nat := 4983230072969 + 3 ^ 40 * 3672532 * 2
def baseEnd_3672532 : Nat := 628591378339310145120113

theorem tailTrace_3672532 : CollatzResearch.WordTrace tailWord_3672532 prefixEnd_3672532 628591378339310145120113 := by
  unfold tailWord_3672532
  simp only [CollatzResearch.WordTrace]
  refine ⟨66974123165525628687645925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89298830887367504916861233 66974123165525628687645925)
  ·
    refine ⟨12557648093536055378933611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66974123165525628687645925 12557648093536055378933611)
    ·
      refine ⟨18836472140304083068400417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12557648093536055378933611 18836472140304083068400417)
      ·
        refine ⟨14127354105228062301300313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18836472140304083068400417 14127354105228062301300313)
        ·
          refine ⟨10595515578921046725975235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14127354105228062301300313 10595515578921046725975235)
          ·
            refine ⟨15893273368381570088962853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10595515578921046725975235 15893273368381570088962853)
            ·
              refine ⟨2979988756571544391680535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15893273368381570088962853 2979988756571544391680535)
              ·
                refine ⟨4469983134857316587520803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2979988756571544391680535 4469983134857316587520803)
                ·
                  refine ⟨6704974702285974881281205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4469983134857316587520803 6704974702285974881281205)
                  ·
                    refine ⟨628591378339310145120113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6704974702285974881281205 628591378339310145120113)
                    ·
                      rfl

theorem cell23_3672532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 4, 1, 1, 5].length) (baseStart_3672532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3672532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3672532 prefixEnd_3672532 := by exact prefixLift 3672532
  have htrace : WordTrace (prefixWord ++ tailWord_3672532) baseStart_3672532 baseEnd_3672532 := by
    simpa [prefixWord, tailWord_3672532, baseEnd_3672532] using wordTrace_append hprefix tailTrace_3672532
  have hstable : (prefixWord ++ tailWord_3672532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3672532).length < 2 ^ (prefixWord ++ tailWord_3672532).sum := by decide
  have hdescent : baseEnd_3672532 < baseStart_3672532 := by decide
  rcases family_descends (prefixWord ++ tailWord_3672532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3672538 : List Nat := [3, 1, 1, 2, 3, 1, 2, 3, 1, 1, 5]
def baseStart_3672538 : Nat := 118140960795 + 3672538 * 2 ^ 59
def prefixEnd_3672538 : Nat := 4983230072969 + 3 ^ 40 * 3672538 * 2
def baseEnd_3672538 : Nat := 1885777215901857411885311

theorem tailTrace_3672538 : CollatzResearch.WordTrace tailWord_3672538 prefixEnd_3672538 1885777215901857411885311 := by
  unfold tailWord_3672538
  simp only [CollatzResearch.WordTrace]
  refine ⟨33487116292257380100002567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89298976779353013600006845 33487116292257380100002567)
  ·
    refine ⟨50230674438386070150003851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33487116292257380100002567 50230674438386070150003851)
    ·
      refine ⟨75346011657579105225005777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50230674438386070150003851 75346011657579105225005777)
      ·
        refine ⟨56509508743184328918754333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75346011657579105225005777 56509508743184328918754333)
        ·
          refine ⟨21191065778694123344532875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56509508743184328918754333 21191065778694123344532875)
          ·
            refine ⟨31786598668041185016799313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21191065778694123344532875 31786598668041185016799313)
            ·
              refine ⟨23839949001030888762599485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31786598668041185016799313 23839949001030888762599485)
              ·
                refine ⟨8939980875386583285974807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23839949001030888762599485 8939980875386583285974807)
                ·
                  refine ⟨13409971313079874928962211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8939980875386583285974807 13409971313079874928962211)
                  ·
                    refine ⟨20114956969619812393443317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13409971313079874928962211 20114956969619812393443317)
                    ·
                      refine ⟨1885777215901857411885311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20114956969619812393443317 1885777215901857411885311)
                      ·
                        rfl

theorem cell23_3672538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 3, 1, 1, 5].length) (baseStart_3672538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3672538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3672538 prefixEnd_3672538 := by exact prefixLift 3672538
  have htrace : WordTrace (prefixWord ++ tailWord_3672538) baseStart_3672538 baseEnd_3672538 := by
    simpa [prefixWord, tailWord_3672538, baseEnd_3672538] using wordTrace_append hprefix tailTrace_3672538
  have hstable : (prefixWord ++ tailWord_3672538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3672538).length < 2 ^ (prefixWord ++ tailWord_3672538).sum := by decide
  have hdescent : baseEnd_3672538 < baseStart_3672538 := by decide
  rcases family_descends (prefixWord ++ tailWord_3672538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3672546 : List Nat := [3, 3, 3, 2, 1, 1, 2, 1, 3, 1, 3]
def baseStart_3672546 : Nat := 118140960795 + 3672546 * 2 ^ 59
def prefixEnd_3672546 : Nat := 4983230072969 + 3 ^ 40 * 3672546 * 2
def baseEnd_3672546 : Nat := 1885781323747093380585275

theorem tailTrace_3672546 : CollatzResearch.WordTrace tailWord_3672546 prefixEnd_3672546 1885781323747093380585275 := by
  unfold tailWord_3672546
  simp only [CollatzResearch.WordTrace]
  refine ⟨33487189238250134441575373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89299171302000358510867661 33487189238250134441575373)
  ·
    refine ⟨12557695964343800415590765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33487189238250134441575373 12557695964343800415590765)
    ·
      refine ⟨4709135986628925155846537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12557695964343800415590765 4709135986628925155846537)
      ·
        refine ⟨3531851989971693866884903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4709135986628925155846537 3531851989971693866884903)
        ·
          refine ⟨5297777984957540800327355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3531851989971693866884903 5297777984957540800327355)
          ·
            refine ⟨7946666977436311200491033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5297777984957540800327355 7946666977436311200491033)
            ·
              refine ⟨5960000233077233400368275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7946666977436311200491033 5960000233077233400368275)
              ·
                refine ⟨8940000349615850100552413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5960000233077233400368275 8940000349615850100552413)
                ·
                  refine ⟨3352500131105943787707155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8940000349615850100552413 3352500131105943787707155)
                  ·
                    refine ⟨5028750196658915681560733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3352500131105943787707155 5028750196658915681560733)
                    ·
                      refine ⟨1885781323747093380585275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5028750196658915681560733 1885781323747093380585275)
                      ·
                        rfl

theorem cell23_3672546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_3672546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3672546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3672546 prefixEnd_3672546 := by exact prefixLift 3672546
  have htrace : WordTrace (prefixWord ++ tailWord_3672546) baseStart_3672546 baseEnd_3672546 := by
    simpa [prefixWord, tailWord_3672546, baseEnd_3672546] using wordTrace_append hprefix tailTrace_3672546
  have hstable : (prefixWord ++ tailWord_3672546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3672546).length < 2 ^ (prefixWord ++ tailWord_3672546).sum := by decide
  have hdescent : baseEnd_3672546 < baseStart_3672546 := by decide
  rcases family_descends (prefixWord ++ tailWord_3672546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3672552 : List Nat := [2, 1, 4, 1, 1, 3, 1, 3, 3, 2, 2]
def baseStart_3672552 : Nat := 118140960795 + 3672552 * 2 ^ 59
def prefixEnd_3672552 : Nat := 4983230072969 + 3 ^ 40 * 3672552 * 2
def baseEnd_3672552 : Nat := 1885784404631020357110247

theorem tailTrace_3672552 : CollatzResearch.WordTrace tailWord_3672552 prefixEnd_3672552 1885784404631020357110247 := by
  unfold tailWord_3672552
  simp only [CollatzResearch.WordTrace]
  refine ⟨66974487895489400395509955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89299317193985867194013273 66974487895489400395509955)
  ·
    refine ⟨100461731843234100593264933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66974487895489400395509955 100461731843234100593264933)
    ·
      refine ⟨18836574720606393861237175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100461731843234100593264933 18836574720606393861237175)
      ·
        refine ⟨28254862080909590791855763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18836574720606393861237175 28254862080909590791855763)
        ·
          refine ⟨42382293121364386187783645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28254862080909590791855763 42382293121364386187783645)
          ·
            refine ⟨15893359920511644820418867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42382293121364386187783645 15893359920511644820418867)
            ·
              refine ⟨23840039880767467230628301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15893359920511644820418867 23840039880767467230628301)
              ·
                refine ⟨8940014955287800211485613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23840039880767467230628301 8940014955287800211485613)
                ·
                  refine ⟨3352505608232925079307105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8940014955287800211485613 3352505608232925079307105)
                  ·
                    refine ⟨2514379206174693809480329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3352505608232925079307105 2514379206174693809480329)
                    ·
                      refine ⟨1885784404631020357110247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2514379206174693809480329 1885784404631020357110247)
                      ·
                        rfl

theorem cell23_3672552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 3, 3, 2, 2].length) (baseStart_3672552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3672552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3672552 prefixEnd_3672552 := by exact prefixLift 3672552
  have htrace : WordTrace (prefixWord ++ tailWord_3672552) baseStart_3672552 baseEnd_3672552 := by
    simpa [prefixWord, tailWord_3672552, baseEnd_3672552] using wordTrace_append hprefix tailTrace_3672552
  have hstable : (prefixWord ++ tailWord_3672552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3672552).length < 2 ^ (prefixWord ++ tailWord_3672552).sum := by decide
  have hdescent : baseEnd_3672552 < baseStart_3672552 := by decide
  rcases family_descends (prefixWord ++ tailWord_3672552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3672562 : List Nat := [3, 2, 1, 4, 2, 2, 1, 1, 1, 6]
def baseStart_3672562 : Nat := 118140960795 + 3672562 * 2 ^ 59
def prefixEnd_3672562 : Nat := 4983230072969 + 3 ^ 40 * 3672562 * 2
def baseEnd_3672562 : Nat := 628596513145855105995067

theorem tailTrace_3672562 : CollatzResearch.WordTrace tailWord_3672562 prefixEnd_3672562 628596513145855105995067 := by
  unfold tailWord_3672562
  simp only [CollatzResearch.WordTrace]
  refine ⟨33487335130235643124720985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89299560347295048332589293 33487335130235643124720985)
  ·
    refine ⟨25115501347676732343540739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33487335130235643124720985 25115501347676732343540739)
    ·
      refine ⟨37673252021515098515311109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25115501347676732343540739 37673252021515098515311109)
      ·
        refine ⟨7063734754034080971620833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37673252021515098515311109 7063734754034080971620833)
        ·
          refine ⟨5297801065525560728715625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7063734754034080971620833 5297801065525560728715625)
          ·
            refine ⟨3973350799144170546536719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5297801065525560728715625 3973350799144170546536719)
            ·
              refine ⟨5960026198716255819805079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3973350799144170546536719 5960026198716255819805079)
              ·
                refine ⟨8940039298074383729707619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5960026198716255819805079 8940039298074383729707619)
                ·
                  refine ⟨13410058947111575594561429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8940039298074383729707619 13410058947111575594561429)
                  ·
                    refine ⟨628596513145855105995067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13410058947111575594561429 628596513145855105995067)
                    ·
                      rfl

theorem cell23_3672562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 1, 1, 1, 6].length) (baseStart_3672562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3672562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3672562 prefixEnd_3672562 := by exact prefixLift 3672562
  have htrace : WordTrace (prefixWord ++ tailWord_3672562) baseStart_3672562 baseEnd_3672562 := by
    simpa [prefixWord, tailWord_3672562, baseEnd_3672562] using wordTrace_append hprefix tailTrace_3672562
  have hstable : (prefixWord ++ tailWord_3672562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3672562).length < 2 ^ (prefixWord ++ tailWord_3672562).sum := by decide
  have hdescent : baseEnd_3672562 < baseStart_3672562 := by decide
  rcases family_descends (prefixWord ++ tailWord_3672562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3672589 : List Nat := [1, 7, 1, 1, 1, 2, 2, 1, 1, 1, 5]
def baseStart_3672589 : Nat := 118140960795 + 3672589 * 2 ^ 59
def prefixEnd_3672589 : Nat := 4983230072969 + 3 ^ 40 * 3672589 * 2
def baseEnd_3672589 : Nat := 1885803403415236712347577

theorem tailTrace_3672589 : CollatzResearch.WordTrace tailWord_3672589 prefixEnd_3672589 1885803403415236712347577 := by
  unfold tailWord_3672589
  simp only [CollatzResearch.WordTrace]
  refine ⟨133950325291844756110116821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89300216861229837406744547 133950325291844756110116821)
  ·
    refine ⟨3139460749027611471330863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 133950325291844756110116821 3139460749027611471330863)
    ·
      refine ⟨4709191123541417206996295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3139460749027611471330863 4709191123541417206996295)
      ·
        refine ⟨7063786685312125810494443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4709191123541417206996295 7063786685312125810494443)
        ·
          refine ⟨10595680027968188715741665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7063786685312125810494443 10595680027968188715741665)
          ·
            refine ⟨7946760020976141536806249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10595680027968188715741665 7946760020976141536806249)
            ·
              refine ⟨5960070015732106152604687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7946760020976141536806249 5960070015732106152604687)
              ·
                refine ⟨8940105023598159228907031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5960070015732106152604687 8940105023598159228907031)
                ·
                  refine ⟨13410157535397238843360547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8940105023598159228907031 13410157535397238843360547)
                  ·
                    refine ⟨20115236303095858265040821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13410157535397238843360547 20115236303095858265040821)
                    ·
                      refine ⟨1885803403415236712347577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20115236303095858265040821 1885803403415236712347577)
                      ·
                        rfl

theorem cell23_3672589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_3672589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3672589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3672589 prefixEnd_3672589 := by exact prefixLift 3672589
  have htrace : WordTrace (prefixWord ++ tailWord_3672589) baseStart_3672589 baseEnd_3672589 := by
    simpa [prefixWord, tailWord_3672589, baseEnd_3672589] using wordTrace_append hprefix tailTrace_3672589
  have hstable : (prefixWord ++ tailWord_3672589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3672589).length < 2 ^ (prefixWord ++ tailWord_3672589).sum := by decide
  have hdescent : baseEnd_3672589 < baseStart_3672589 := by decide
  rcases family_descends (prefixWord ++ tailWord_3672589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3672675 : List Nat := [1, 1, 1, 5, 1, 2, 3, 1, 2, 3, 3]
def baseStart_3672675 : Nat := 118140960795 + 3672675 * 2 ^ 59
def prefixEnd_3672675 : Nat := 4983230072969 + 3 ^ 40 * 3672675 * 2
def baseEnd_3672675 : Nat := 1885847562751523375872181

theorem tailTrace_3672675 : CollatzResearch.WordTrace tailWord_3672675 prefixEnd_3672675 1885847562751523375872181 := by
  unfold tailWord_3672675
  simp only [CollatzResearch.WordTrace]
  refine ⟨133953461969533192797747479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89302307979688795198498319 133953461969533192797747479)
  ·
    refine ⟨200930192954299789196621219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133953461969533192797747479 200930192954299789196621219)
    ·
      refine ⟨301395289431449683794931829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200930192954299789196621219 301395289431449683794931829)
      ·
        refine ⟨28255808384198407855774859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 301395289431449683794931829 28255808384198407855774859)
        ·
          refine ⟨42383712576297611783662289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28255808384198407855774859 42383712576297611783662289)
          ·
            refine ⟨31787784432223208837746717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42383712576297611783662289 31787784432223208837746717)
            ·
              refine ⟨11920419162083703314155019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31787784432223208837746717 11920419162083703314155019)
              ·
                refine ⟨17880628743125554971232529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11920419162083703314155019 17880628743125554971232529)
                ·
                  refine ⟨13410471557344166228424397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17880628743125554971232529 13410471557344166228424397)
                  ·
                    refine ⟨5028926834004062335659149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13410471557344166228424397 5028926834004062335659149)
                    ·
                      refine ⟨1885847562751523375872181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5028926834004062335659149 1885847562751523375872181)
                      ·
                        rfl

theorem cell23_3672675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 1, 2, 3, 3].length) (baseStart_3672675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3672675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3672675 prefixEnd_3672675 := by exact prefixLift 3672675
  have htrace : WordTrace (prefixWord ++ tailWord_3672675) baseStart_3672675 baseEnd_3672675 := by
    simpa [prefixWord, tailWord_3672675, baseEnd_3672675] using wordTrace_append hprefix tailTrace_3672675
  have hstable : (prefixWord ++ tailWord_3672675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3672675).length < 2 ^ (prefixWord ++ tailWord_3672675).sum := by decide
  have hdescent : baseEnd_3672675 < baseStart_3672675 := by decide
  rcases family_descends (prefixWord ++ tailWord_3672675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3672695 : List Nat := [1, 1, 3, 1, 1, 3, 5, 1, 2, 5]
def baseStart_3672695 : Nat := 118140960795 + 3672695 * 2 ^ 59
def prefixEnd_3672695 : Nat := 4983230072969 + 3 ^ 40 * 3672695 * 2
def baseEnd_3672695 : Nat := 628619277454871099207363

theorem tailTrace_3672695 : CollatzResearch.WordTrace tailWord_3672695 prefixEnd_3672695 628619277454871099207363 := by
  unfold tailWord_3672695
  simp only [CollatzResearch.WordTrace]
  refine ⟨133954191429460736213475539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89302794286307157475650359 133954191429460736213475539)
  ·
    refine ⟨200931287144191104320213309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133954191429460736213475539 200931287144191104320213309)
    ·
      refine ⟨75349232679071664120079991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 200931287144191104320213309 75349232679071664120079991)
      ·
        refine ⟨113023849018607496180119987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75349232679071664120079991 113023849018607496180119987)
        ·
          refine ⟨169535773527911244270179981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113023849018607496180119987 169535773527911244270179981)
          ·
            refine ⟨63575915072966716601317493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 169535773527911244270179981 63575915072966716601317493)
            ·
              refine ⟨5960242038090629681373515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63575915072966716601317493 5960242038090629681373515)
              ·
                refine ⟨8940363057135944522060273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5960242038090629681373515 8940363057135944522060273)
                ·
                  refine ⟨6705272292851958391545205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8940363057135944522060273 6705272292851958391545205)
                  ·
                    refine ⟨628619277454871099207363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6705272292851958391545205 628619277454871099207363)
                    ·
                      rfl

theorem cell23_3672695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 5, 1, 2, 5].length) (baseStart_3672695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3672695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3672695 prefixEnd_3672695 := by exact prefixLift 3672695
  have htrace : WordTrace (prefixWord ++ tailWord_3672695) baseStart_3672695 baseEnd_3672695 := by
    simpa [prefixWord, tailWord_3672695, baseEnd_3672695] using wordTrace_append hprefix tailTrace_3672695
  have hstable : (prefixWord ++ tailWord_3672695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3672695).length < 2 ^ (prefixWord ++ tailWord_3672695).sum := by decide
  have hdescent : baseEnd_3672695 < baseStart_3672695 := by decide
  rcases family_descends (prefixWord ++ tailWord_3672695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3672748 : List Nat := [2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 9]
def baseStart_3672748 : Nat := 118140960795 + 3672748 * 2 ^ 59
def prefixEnd_3672748 : Nat := 4983230072969 + 3 ^ 40 * 3672748 * 2
def baseEnd_3672748 : Nat := 1885885046839301590259345

theorem tailTrace_3672748 : CollatzResearch.WordTrace tailWord_3672748 prefixEnd_3672748 1885885046839301590259345 := by
  unfold tailWord_3672748
  simp only [CollatzResearch.WordTrace]
  refine ⟨66978062249134363132577449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89304082998845817510103265 66978062249134363132577449)
  ·
    refine ⟨50233546686850772349433087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66978062249134363132577449 50233546686850772349433087)
    ·
      refine ⟨75350320030276158524149631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50233546686850772349433087 75350320030276158524149631)
      ·
        refine ⟨113025480045414237786224447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75350320030276158524149631 113025480045414237786224447)
        ·
          refine ⟨169538220068121356679336671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113025480045414237786224447 169538220068121356679336671)
          ·
            refine ⟨254307330102182035019005007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169538220068121356679336671 254307330102182035019005007)
            ·
              refine ⟨381460995153273052528507511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 254307330102182035019005007 381460995153273052528507511)
              ·
                refine ⟨572191492729909578792761267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 381460995153273052528507511 572191492729909578792761267)
                ·
                  refine ⟨858287239094864368189141901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 572191492729909578792761267 858287239094864368189141901)
                  ·
                    refine ⟨321857714660574138070928213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 858287239094864368189141901 321857714660574138070928213)
                    ·
                      refine ⟨1885885046839301590259345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 321857714660574138070928213 1885885046839301590259345)
                      ·
                        rfl

theorem cell23_3672748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 9].length) (baseStart_3672748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3672748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3672748 prefixEnd_3672748 := by exact prefixLift 3672748
  have htrace : WordTrace (prefixWord ++ tailWord_3672748) baseStart_3672748 baseEnd_3672748 := by
    simpa [prefixWord, tailWord_3672748, baseEnd_3672748] using wordTrace_append hprefix tailTrace_3672748
  have hstable : (prefixWord ++ tailWord_3672748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3672748).length < 2 ^ (prefixWord ++ tailWord_3672748).sum := by decide
  have hdescent : baseEnd_3672748 < baseStart_3672748 := by decide
  rcases family_descends (prefixWord ++ tailWord_3672748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3672776 : List Nat := [2, 1, 3, 1, 2, 4, 3, 2, 1, 4]
def baseStart_3672776 : Nat := 118140960795 + 3672776 * 2 ^ 59
def prefixEnd_3672776 : Nat := 4983230072969 + 3 ^ 40 * 3672776 * 2
def baseEnd_3672776 : Nat := 628633141432542493569739

theorem tailTrace_3672776 : CollatzResearch.WordTrace tailWord_3672776 prefixEnd_3672776 628633141432542493569739 := by
  unfold tailWord_3672776
  simp only [CollatzResearch.WordTrace]
  refine ⟨66978572871083643523587091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89304763828111524698116121 66978572871083643523587091)
  ·
    refine ⟨100467859306625465285380637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66978572871083643523587091 100467859306625465285380637)
    ·
      refine ⟨37675447239984549482017739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100467859306625465285380637 37675447239984549482017739)
      ·
        refine ⟨56513170859976824223026609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37675447239984549482017739 56513170859976824223026609)
        ·
          refine ⟨42384878144982618167269957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56513170859976824223026609 42384878144982618167269957)
          ·
            refine ⟨7947164652184240906363117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42384878144982618167269957 7947164652184240906363117)
            ·
              refine ⟨2980186744569090339886169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7947164652184240906363117 2980186744569090339886169)
              ·
                refine ⟨2235140058426817754914627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2980186744569090339886169 2235140058426817754914627)
                ·
                  refine ⟨3352710087640226632371941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2235140058426817754914627 3352710087640226632371941)
                  ·
                    refine ⟨628633141432542493569739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3352710087640226632371941 628633141432542493569739)
                    ·
                      rfl

theorem cell23_3672776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 3, 2, 1, 4].length) (baseStart_3672776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3672776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3672776 prefixEnd_3672776 := by exact prefixLift 3672776
  have htrace : WordTrace (prefixWord ++ tailWord_3672776) baseStart_3672776 baseEnd_3672776 := by
    simpa [prefixWord, tailWord_3672776, baseEnd_3672776] using wordTrace_append hprefix tailTrace_3672776
  have hstable : (prefixWord ++ tailWord_3672776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3672776).length < 2 ^ (prefixWord ++ tailWord_3672776).sum := by decide
  have hdescent : baseEnd_3672776 < baseStart_3672776 := by decide
  rcases family_descends (prefixWord ++ tailWord_3672776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3672785 : List Nat := [1, 2, 2, 1, 2, 3, 2, 2, 3, 5]
def baseStart_3672785 : Nat := 118140960795 + 3672785 * 2 ^ 59
def prefixEnd_3672785 : Nat := 4983230072969 + 3 ^ 40 * 3672785 * 2
def baseEnd_3672785 : Nat := 628634681874505981832225

theorem tailTrace_3672785 : CollatzResearch.WordTrace tailWord_3672785 prefixEnd_3672785 628634681874505981832225 := by
  unfold tailWord_3672785
  simp only [CollatzResearch.WordTrace]
  refine ⟨133957473999134681584251809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89304982666089787722834539 133957473999134681584251809)
  ·
    refine ⟨100468105499351011188188857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133957473999134681584251809 100468105499351011188188857)
    ·
      refine ⟨75351079124513258391141643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100468105499351011188188857 75351079124513258391141643)
      ·
        refine ⟨113026618686769887586712465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75351079124513258391141643 113026618686769887586712465)
        ·
          refine ⟨84769964015077415690034349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113026618686769887586712465 84769964015077415690034349)
          ·
            refine ⟨31788736505654030883762881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84769964015077415690034349 31788736505654030883762881)
            ·
              refine ⟨23841552379240523162822161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31788736505654030883762881 23841552379240523162822161)
              ·
                refine ⟨17881164284430392372116621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23841552379240523162822161 17881164284430392372116621)
                ·
                  refine ⟨6705436606661397139543733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17881164284430392372116621 6705436606661397139543733)
                  ·
                    refine ⟨628634681874505981832225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6705436606661397139543733 628634681874505981832225)
                    ·
                      rfl

theorem cell23_3672785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 2, 3, 5].length) (baseStart_3672785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3672785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3672785 prefixEnd_3672785 := by exact prefixLift 3672785
  have htrace : WordTrace (prefixWord ++ tailWord_3672785) baseStart_3672785 baseEnd_3672785 := by
    simpa [prefixWord, tailWord_3672785, baseEnd_3672785] using wordTrace_append hprefix tailTrace_3672785
  have hstable : (prefixWord ++ tailWord_3672785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3672785).length < 2 ^ (prefixWord ++ tailWord_3672785).sum := by decide
  have hdescent : baseEnd_3672785 < baseStart_3672785 := by decide
  rcases family_descends (prefixWord ++ tailWord_3672785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3672789 : List Nat := [1, 3, 2, 5, 1, 1, 1, 3, 6]
def baseStart_3672789 : Nat := 118140960795 + 3672789 * 2 ^ 59
def prefixEnd_3672789 : Nat := 4983230072969 + 3 ^ 40 * 3672789 * 2
def baseEnd_3672789 : Nat := 209545122171792881094073

theorem tailTrace_3672789 : CollatzResearch.WordTrace tailWord_3672789 prefixEnd_3672789 209545122171792881094073 := by
  unfold tailWord_3672789
  simp only [CollatzResearch.WordTrace]
  refine ⟨133957619891120190267397421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89305079927413460178264947 133957619891120190267397421)
  ·
    refine ⟨50234107459170071350274033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133957619891120190267397421 50234107459170071350274033)
    ·
      refine ⟨37675580594377553512705525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50234107459170071350274033 37675580594377553512705525)
      ·
        refine ⟨3532085680722895641816143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37675580594377553512705525 3532085680722895641816143)
        ·
          refine ⟨5298128521084343462724215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3532085680722895641816143 5298128521084343462724215)
          ·
            refine ⟨7947192781626515194086323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5298128521084343462724215 7947192781626515194086323)
            ·
              refine ⟨11920789172439772791129485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7947192781626515194086323 11920789172439772791129485)
              ·
                refine ⟨4470295939664914796673557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11920789172439772791129485 4470295939664914796673557)
                ·
                  refine ⟨209545122171792881094073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4470295939664914796673557 209545122171792881094073)
                  ·
                    rfl

theorem cell23_3672789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 3, 6].length) (baseStart_3672789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3672789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3672789 prefixEnd_3672789 := by exact prefixLift 3672789
  have htrace : WordTrace (prefixWord ++ tailWord_3672789) baseStart_3672789 baseEnd_3672789 := by
    simpa [prefixWord, tailWord_3672789, baseEnd_3672789] using wordTrace_append hprefix tailTrace_3672789
  have hstable : (prefixWord ++ tailWord_3672789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3672789).length < 2 ^ (prefixWord ++ tailWord_3672789).sum := by decide
  have hdescent : baseEnd_3672789 < baseStart_3672789 := by decide
  rcases family_descends (prefixWord ++ tailWord_3672789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3672815 : List Nat := [1, 1, 2, 1, 5, 2, 1, 1, 3, 6]
def baseStart_3672815 : Nat := 118140960795 + 3672815 * 2 ^ 59
def prefixEnd_3672815 : Nat := 4983230072969 + 3 ^ 40 * 3672815 * 2
def baseEnd_3672815 : Nat := 628639816681050942707179

theorem tailTrace_3672815 : CollatzResearch.WordTrace tailWord_3672815 prefixEnd_3672815 628639816681050942707179 := by
  unfold tailWord_3672815
  simp only [CollatzResearch.WordTrace]
  refine ⟨133958568189025996707843899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89305712126017331138562599 133958568189025996707843899)
  ·
    refine ⟨200937852283538995061765849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133958568189025996707843899 200937852283538995061765849)
    ·
      refine ⟨150703389212654246296324387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200937852283538995061765849 150703389212654246296324387)
      ·
        refine ⟨226055083818981369444486581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150703389212654246296324387 226055083818981369444486581)
        ·
          refine ⟨21192664108029503385420617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 226055083818981369444486581 21192664108029503385420617)
          ·
            refine ⟨15894498081022127539065463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21192664108029503385420617 15894498081022127539065463)
            ·
              refine ⟨23841747121533191308598195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15894498081022127539065463 23841747121533191308598195)
              ·
                refine ⟨35762620682299786962897293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23841747121533191308598195 35762620682299786962897293)
                ·
                  refine ⟨13410982755862420111086485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35762620682299786962897293 13410982755862420111086485)
                  ·
                    refine ⟨628639816681050942707179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13410982755862420111086485 628639816681050942707179)
                    ·
                      rfl

theorem cell23_3672815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 1, 3, 6].length) (baseStart_3672815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3672815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3672815 prefixEnd_3672815 := by exact prefixLift 3672815
  have htrace : WordTrace (prefixWord ++ tailWord_3672815) baseStart_3672815 baseEnd_3672815 := by
    simpa [prefixWord, tailWord_3672815, baseEnd_3672815] using wordTrace_append hprefix tailTrace_3672815
  have hstable : (prefixWord ++ tailWord_3672815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3672815).length < 2 ^ (prefixWord ++ tailWord_3672815).sum := by decide
  have hdescent : baseEnd_3672815 < baseStart_3672815 := by decide
  rcases family_descends (prefixWord ++ tailWord_3672815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3672835 : List Nat := [1, 1, 1, 3, 2, 2, 1, 1, 5, 2, 4]
def baseStart_3672835 : Nat := 118140960795 + 3672835 * 2 ^ 59
def prefixEnd_3672835 : Nat := 4983230072969 + 3 ^ 40 * 3672835 * 2
def baseEnd_3672835 : Nat := 1885929719656242749871445

theorem tailTrace_3672835 : CollatzResearch.WordTrace tailWord_3672835 prefixEnd_3672835 1885929719656242749871445 := by
  unfold tailWord_3672835
  simp only [CollatzResearch.WordTrace]
  refine ⟨133959297648953540123571959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89306198432635693415714639 133959297648953540123571959)
  ·
    refine ⟨200938946473430310185357939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133959297648953540123571959 200938946473430310185357939)
    ·
      refine ⟨301408419710145465278036909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200938946473430310185357939 301408419710145465278036909)
      ·
        refine ⟨113028157391304549479263841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 301408419710145465278036909 113028157391304549479263841)
        ·
          refine ⟨84771118043478412109447881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113028157391304549479263841 84771118043478412109447881)
          ·
            refine ⟨63578338532608809082085911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84771118043478412109447881 63578338532608809082085911)
            ·
              refine ⟨95367507798913213623128867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63578338532608809082085911 95367507798913213623128867)
              ·
                refine ⟨143051261698369820434693301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95367507798913213623128867 143051261698369820434693301)
                ·
                  refine ⟨13411055784222170665752497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 143051261698369820434693301 13411055784222170665752497)
                  ·
                    refine ⟨10058291838166627999314373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13411055784222170665752497 10058291838166627999314373)
                    ·
                      refine ⟨1885929719656242749871445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10058291838166627999314373 1885929719656242749871445)
                      ·
                        rfl

theorem cell23_3672835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 5, 2, 4].length) (baseStart_3672835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3672835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3672835 prefixEnd_3672835 := by exact prefixLift 3672835
  have htrace : WordTrace (prefixWord ++ tailWord_3672835) baseStart_3672835 baseEnd_3672835 := by
    simpa [prefixWord, tailWord_3672835, baseEnd_3672835] using wordTrace_append hprefix tailTrace_3672835
  have hstable : (prefixWord ++ tailWord_3672835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3672835).length < 2 ^ (prefixWord ++ tailWord_3672835).sum := by decide
  have hdescent : baseEnd_3672835 < baseStart_3672835 := by decide
  rcases family_descends (prefixWord ++ tailWord_3672835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3672842 : List Nat := [3, 1, 2, 2, 1, 2, 1, 1, 5, 2, 3]
def baseStart_3672842 : Nat := 118140960795 + 3672842 * 2 ^ 59
def prefixEnd_3672842 : Nat := 4983230072969 + 3 ^ 40 * 3672842 * 2
def baseEnd_3672842 : Nat := 1885933314020824222483913

theorem tailTrace_3672842 : CollatzResearch.WordTrace tailWord_3672842 prefixEnd_3672842 1885933314020824222483913 := by
  unfold tailWord_3672842
  simp only [CollatzResearch.WordTrace]
  refine ⟨33489888239982045079769195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89306368639952120212717853 33489888239982045079769195)
  ·
    refine ⟨50234832359973067619653793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33489888239982045079769195 50234832359973067619653793)
    ·
      refine ⟨37676124269979800714740345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50234832359973067619653793 37676124269979800714740345)
      ·
        refine ⟨28257093202484850536055259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37676124269979800714740345 28257093202484850536055259)
        ·
          refine ⟨42385639803727275804082889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28257093202484850536055259 42385639803727275804082889)
          ·
            refine ⟨31789229852795456853062167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42385639803727275804082889 31789229852795456853062167)
            ·
              refine ⟨47683844779193185279593251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31789229852795456853062167 47683844779193185279593251)
              ·
                refine ⟨71525767168789777919389877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47683844779193185279593251 71525767168789777919389877)
                ·
                  refine ⟨6705540672074041679942801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71525767168789777919389877 6705540672074041679942801)
                  ·
                    refine ⟨5029155504055531259957101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6705540672074041679942801 5029155504055531259957101)
                    ·
                      refine ⟨1885933314020824222483913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5029155504055531259957101 1885933314020824222483913)
                      ·
                        rfl

theorem cell23_3672842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 5, 2, 3].length) (baseStart_3672842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3672842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3672842 prefixEnd_3672842 := by exact prefixLift 3672842
  have htrace : WordTrace (prefixWord ++ tailWord_3672842) baseStart_3672842 baseEnd_3672842 := by
    simpa [prefixWord, tailWord_3672842, baseEnd_3672842] using wordTrace_append hprefix tailTrace_3672842
  have hstable : (prefixWord ++ tailWord_3672842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3672842).length < 2 ^ (prefixWord ++ tailWord_3672842).sum := by decide
  have hdescent : baseEnd_3672842 < baseStart_3672842 := by decide
  rcases family_descends (prefixWord ++ tailWord_3672842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3672900 : List Nat := [2, 3, 4, 2, 1, 1, 3, 1, 2, 4]
def baseStart_3672900 : Nat := 118140960795 + 3672900 * 2 ^ 59
def prefixEnd_3672900 : Nat := 4983230072969 + 3 ^ 40 * 3672900 * 2
def baseEnd_3672900 : Nat := 628654365299594998519549

theorem tailTrace_3672900 : CollatzResearch.WordTrace tailWord_3672900 prefixEnd_3672900 628654365299594998519549 := by
  unfold tailWord_3672900
  simp only [CollatzResearch.WordTrace]
  refine ⟨66980834196859028112344077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89307778929145370816458769 66980834196859028112344077)
  ·
    refine ⟨25117812823822135542129029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66980834196859028112344077 25117812823822135542129029)
    ·
      refine ⟨4709589904466650414149193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25117812823822135542129029 4709589904466650414149193)
      ·
        refine ⟨3532192428349987810611895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4709589904466650414149193 3532192428349987810611895)
        ·
          refine ⟨5298288642524981715917843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3532192428349987810611895 5298288642524981715917843)
          ·
            refine ⟨7947432963787472573876765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5298288642524981715917843 7947432963787472573876765)
            ·
              refine ⟨2980287361420302215203787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7947432963787472573876765 2980287361420302215203787)
              ·
                refine ⟨4470431042130453322805681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2980287361420302215203787 4470431042130453322805681)
                ·
                  refine ⟨3352823281597839992104261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4470431042130453322805681 3352823281597839992104261)
                  ·
                    refine ⟨628654365299594998519549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3352823281597839992104261 628654365299594998519549)
                    ·
                      rfl

theorem cell23_3672900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_3672900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3672900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3672900 prefixEnd_3672900 := by exact prefixLift 3672900
  have htrace : WordTrace (prefixWord ++ tailWord_3672900) baseStart_3672900 baseEnd_3672900 := by
    simpa [prefixWord, tailWord_3672900, baseEnd_3672900] using wordTrace_append hprefix tailTrace_3672900
  have hstable : (prefixWord ++ tailWord_3672900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3672900).length < 2 ^ (prefixWord ++ tailWord_3672900).sum := by decide
  have hdescent : baseEnd_3672900 < baseStart_3672900 := by decide
  rcases family_descends (prefixWord ++ tailWord_3672900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3672915 : List Nat := [1, 1, 1, 2, 1, 1, 3, 2, 3, 3, 5]
def baseStart_3672915 : Nat := 118140960795 + 3672915 * 2 ^ 59
def prefixEnd_3672915 : Nat := 4983230072969 + 3 ^ 40 * 3672915 * 2
def baseEnd_3672915 : Nat := 1885970798108602436871077

theorem tailTrace_3672915 : CollatzResearch.WordTrace tailWord_3672915 prefixEnd_3672915 1885970798108602436871077 := by
  unfold tailWord_3672915
  simp only [CollatzResearch.WordTrace]
  refine ⟨133962215488663713786484199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89308143659109142524322799 133962215488663713786484199)
  ·
    refine ⟨200943323232995570679726299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133962215488663713786484199 200943323232995570679726299)
    ·
      refine ⟨301414984849493356019589449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200943323232995570679726299 301414984849493356019589449)
      ·
        refine ⟨226061238637120017014692087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 301414984849493356019589449 226061238637120017014692087)
        ·
          refine ⟨339091857955680025522038131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226061238637120017014692087 339091857955680025522038131)
          ·
            refine ⟨508637786933520038283057197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 339091857955680025522038131 508637786933520038283057197)
            ·
              refine ⟨190739170100070014356146449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 508637786933520038283057197 190739170100070014356146449)
              ·
                refine ⟨143054377575052510767109837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 190739170100070014356146449 143054377575052510767109837)
                ·
                  refine ⟨53645391590644691537666189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 143054377575052510767109837 53645391590644691537666189)
                  ·
                    refine ⟨20117021846491759326624821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53645391590644691537666189 20117021846491759326624821)
                    ·
                      refine ⟨1885970798108602436871077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20117021846491759326624821 1885970798108602436871077)
                      ·
                        rfl

theorem cell23_3672915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 3, 3, 5].length) (baseStart_3672915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3672915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3672915 prefixEnd_3672915 := by exact prefixLift 3672915
  have htrace : WordTrace (prefixWord ++ tailWord_3672915) baseStart_3672915 baseEnd_3672915 := by
    simpa [prefixWord, tailWord_3672915, baseEnd_3672915] using wordTrace_append hprefix tailTrace_3672915
  have hstable : (prefixWord ++ tailWord_3672915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3672915).length < 2 ^ (prefixWord ++ tailWord_3672915).sum := by decide
  have hdescent : baseEnd_3672915 < baseStart_3672915 := by decide
  rcases family_descends (prefixWord ++ tailWord_3672915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3672932 : List Nat := [2, 3, 1, 1, 4, 1, 1, 1, 1, 3, 5]
def baseStart_3672932 : Nat := 118140960795 + 3672932 * 2 ^ 59
def prefixEnd_3672932 : Nat := 4983230072969 + 3 ^ 40 * 3672932 * 2
def baseEnd_3672932 : Nat := 1885979527279728870358499

theorem tailTrace_3672932 : CollatzResearch.WordTrace tailWord_3672932 prefixEnd_3672932 1885979527279728870358499 := by
  unfold tailWord_3672932
  simp only [CollatzResearch.WordTrace]
  refine ⟨66981417764801062844926525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89308557019734750459902033 66981417764801062844926525)
  ·
    refine ⟨25118031661800398566847447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66981417764801062844926525 25118031661800398566847447)
    ·
      refine ⟨37677047492700597850271171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25118031661800398566847447 37677047492700597850271171)
      ·
        refine ⟨56515571239050896775406757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37677047492700597850271171 56515571239050896775406757)
        ·
          refine ⟨10596669607322043145388767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56515571239050896775406757 10596669607322043145388767)
          ·
            refine ⟨15895004410983064718083151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10596669607322043145388767 15895004410983064718083151)
            ·
              refine ⟨23842506616474597077124727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15895004410983064718083151 23842506616474597077124727)
              ·
                refine ⟨35763759924711895615687091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23842506616474597077124727 35763759924711895615687091)
                ·
                  refine ⟨53645639887067843423530637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35763759924711895615687091 53645639887067843423530637)
                  ·
                    refine ⟨20117114957650441283823989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53645639887067843423530637 20117114957650441283823989)
                    ·
                      refine ⟨1885979527279728870358499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20117114957650441283823989 1885979527279728870358499)
                      ·
                        rfl

theorem cell23_3672932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 1, 1, 3, 5].length) (baseStart_3672932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3672932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3672932 prefixEnd_3672932 := by exact prefixLift 3672932
  have htrace : WordTrace (prefixWord ++ tailWord_3672932) baseStart_3672932 baseEnd_3672932 := by
    simpa [prefixWord, tailWord_3672932, baseEnd_3672932] using wordTrace_append hprefix tailTrace_3672932
  have hstable : (prefixWord ++ tailWord_3672932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3672932).length < 2 ^ (prefixWord ++ tailWord_3672932).sum := by decide
  have hdescent : baseEnd_3672932 < baseStart_3672932 := by decide
  rcases family_descends (prefixWord ++ tailWord_3672932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3672946 : List Nat := [3, 2, 1, 2, 1, 1, 4, 1, 4, 2, 2]
def baseStart_3672946 : Nat := 118140960795 + 3672946 * 2 ^ 59
def prefixEnd_3672946 : Nat := 4983230072969 + 3 ^ 40 * 3672946 * 2
def baseEnd_3672946 : Nat := 1885986716008891815583435

theorem tailTrace_3672946 : CollatzResearch.WordTrace tailWord_3672946 prefixEnd_3672946 1885986716008891815583435 := by
  unfold tailWord_3672946
  simp only [CollatzResearch.WordTrace]
  refine ⟨33490836537887851520215673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89308897434367604053908461 33490836537887851520215673)
  ·
    refine ⟨25118127403415888640161755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33490836537887851520215673 25118127403415888640161755)
    ·
      refine ⟨37677191105123832960242633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25118127403415888640161755 37677191105123832960242633)
      ·
        refine ⟨28257893328842874720181975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37677191105123832960242633 28257893328842874720181975)
        ·
          refine ⟨42386839993264312080272963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28257893328842874720181975 42386839993264312080272963)
          ·
            refine ⟨63580259989896468120409445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42386839993264312080272963 63580259989896468120409445)
            ·
              refine ⟨11921298748105587772576771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63580259989896468120409445 11921298748105587772576771)
              ·
                refine ⟨17881948122158381658865157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11921298748105587772576771 17881948122158381658865157)
                ·
                  refine ⟨3352865272904696561037217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17881948122158381658865157 3352865272904696561037217)
                  ·
                    refine ⟨2514648954678522420777913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3352865272904696561037217 2514648954678522420777913)
                    ·
                      refine ⟨1885986716008891815583435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2514648954678522420777913 1885986716008891815583435)
                      ·
                        rfl

theorem cell23_3672946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 1, 4, 2, 2].length) (baseStart_3672946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3672946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3672946 prefixEnd_3672946 := by exact prefixLift 3672946
  have htrace : WordTrace (prefixWord ++ tailWord_3672946) baseStart_3672946 baseEnd_3672946 := by
    simpa [prefixWord, tailWord_3672946, baseEnd_3672946] using wordTrace_append hprefix tailTrace_3672946
  have hstable : (prefixWord ++ tailWord_3672946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3672946).length < 2 ^ (prefixWord ++ tailWord_3672946).sum := by decide
  have hdescent : baseEnd_3672946 < baseStart_3672946 := by decide
  rcases family_descends (prefixWord ++ tailWord_3672946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3672992 : List Nat := [2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 5]
def baseStart_3672992 : Nat := 118140960795 + 3672992 * 2 ^ 59
def prefixEnd_3672992 : Nat := 4983230072969 + 3 ^ 40 * 3672992 * 2
def baseEnd_3672992 : Nat := 1886010336118998635608223

theorem tailTrace_3672992 : CollatzResearch.WordTrace tailWord_3672992 prefixEnd_3672992 1886010336118998635608223 := by
  unfold tailWord_3672992
  simp only [CollatzResearch.WordTrace]
  refine ⟨66982511954692377968518615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89310015939589837291358153 66982511954692377968518615)
  ·
    refine ⟨100473767932038566952777923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66982511954692377968518615 100473767932038566952777923)
    ·
      refine ⟨150710651898057850429166885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100473767932038566952777923 150710651898057850429166885)
      ·
        refine ⟨28258247230885846955468791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 150710651898057850429166885 28258247230885846955468791)
        ·
          refine ⟨42387370846328770433203187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28258247230885846955468791 42387370846328770433203187)
          ·
            refine ⟨63581056269493155649804781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42387370846328770433203187 63581056269493155649804781)
            ·
              refine ⟨23842896101059933368676793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63581056269493155649804781 23842896101059933368676793)
              ·
                refine ⟨17882172075794950026507595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23842896101059933368676793 17882172075794950026507595)
                ·
                  refine ⟨26823258113692425039761393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17882172075794950026507595 26823258113692425039761393)
                  ·
                    refine ⟨20117443585269318779821045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26823258113692425039761393 20117443585269318779821045)
                    ·
                      refine ⟨1886010336118998635608223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20117443585269318779821045 1886010336118998635608223)
                      ·
                        rfl

theorem cell23_3672992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 5].length) (baseStart_3672992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3672992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3672992 prefixEnd_3672992 := by exact prefixLift 3672992
  have htrace : WordTrace (prefixWord ++ tailWord_3672992) baseStart_3672992 baseEnd_3672992 := by
    simpa [prefixWord, tailWord_3672992, baseEnd_3672992] using wordTrace_append hprefix tailTrace_3672992
  have hstable : (prefixWord ++ tailWord_3672992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3672992).length < 2 ^ (prefixWord ++ tailWord_3672992).sum := by decide
  have hdescent : baseEnd_3672992 < baseStart_3672992 := by decide
  rcases family_descends (prefixWord ++ tailWord_3672992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3673037 : List Nat := [1, 6, 3, 1, 1, 1, 2, 3, 5]
def baseStart_3673037 : Nat := 118140960795 + 3673037 * 2 ^ 59
def prefixEnd_3673037 : Nat := 4983230072969 + 3 ^ 40 * 3673037 * 2
def baseEnd_3673037 : Nat := 209559271416494551060613

theorem tailTrace_3673037 : CollatzResearch.WordTrace tailWord_3673037 prefixEnd_3673037 209559271416494551060613 := by
  unfold tailWord_3673037
  simp only [CollatzResearch.WordTrace]
  refine ⟨133966665194221728622425365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89311110129481152414950243 133966665194221728622425365)
  ·
    refine ⟨6279687430979143529176189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 133966665194221728622425365 6279687430979143529176189)
    ·
      refine ⟨2354882786617178823441071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6279687430979143529176189 2354882786617178823441071)
      ·
        refine ⟨3532324179925768235161607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2354882786617178823441071 3532324179925768235161607)
        ·
          refine ⟨5298486269888652352742411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3532324179925768235161607 5298486269888652352742411)
          ·
            refine ⟨7947729404832978529113617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5298486269888652352742411 7947729404832978529113617)
            ·
              refine ⟨5960797053624733896835213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7947729404832978529113617 5960797053624733896835213)
              ·
                refine ⟨2235298895109275211313205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5960797053624733896835213 2235298895109275211313205)
                ·
                  refine ⟨209559271416494551060613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2235298895109275211313205 209559271416494551060613)
                  ·
                    rfl

theorem cell23_3673037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 2, 3, 5].length) (baseStart_3673037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3673037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3673037 prefixEnd_3673037 := by exact prefixLift 3673037
  have htrace : WordTrace (prefixWord ++ tailWord_3673037) baseStart_3673037 baseEnd_3673037 := by
    simpa [prefixWord, tailWord_3673037, baseEnd_3673037] using wordTrace_append hprefix tailTrace_3673037
  have hstable : (prefixWord ++ tailWord_3673037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3673037).length < 2 ^ (prefixWord ++ tailWord_3673037).sum := by decide
  have hdescent : baseEnd_3673037 < baseStart_3673037 := by decide
  rcases family_descends (prefixWord ++ tailWord_3673037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3673039 : List Nat := [1, 1, 2, 1, 1, 7, 1, 1, 1, 4, 3]
def baseStart_3673039 : Nat := 118140960795 + 3673039 * 2 ^ 59
def prefixEnd_3673039 : Nat := 4983230072969 + 3 ^ 40 * 3673039 * 2
def baseEnd_3673039 : Nat := 1886034469709759951720507

theorem tailTrace_3673039 : CollatzResearch.WordTrace tailWord_3673039 prefixEnd_3673039 1886034469709759951720507 := by
  unfold tailWord_3673039
  simp only [CollatzResearch.WordTrace]
  refine ⟨133966738140214482963998171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89311158760142988642665447 133966738140214482963998171)
  ·
    refine ⟨200950107210321724445997257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133966738140214482963998171 200950107210321724445997257)
    ·
      refine ⟨150712580407741293334497943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200950107210321724445997257 150712580407741293334497943)
      ·
        refine ⟨226068870611611940001746915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150712580407741293334497943 226068870611611940001746915)
        ·
          refine ⟨339103305917417910002620373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226068870611611940001746915 339103305917417910002620373)
          ·
            refine ⟨7947733732439482265686415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 339103305917417910002620373 7947733732439482265686415)
            ·
              refine ⟨11921600598659223398529623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7947733732439482265686415 11921600598659223398529623)
              ·
                refine ⟨17882400897988835097794435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11921600598659223398529623 17882400897988835097794435)
                ·
                  refine ⟨26823601346983252646691653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17882400897988835097794435 26823601346983252646691653)
                  ·
                    refine ⟨5029425252559359871254685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26823601346983252646691653 5029425252559359871254685)
                    ·
                      refine ⟨1886034469709759951720507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5029425252559359871254685 1886034469709759951720507)
                      ·
                        rfl

theorem cell23_3673039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 1, 1, 4, 3].length) (baseStart_3673039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3673039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3673039 prefixEnd_3673039 := by exact prefixLift 3673039
  have htrace : WordTrace (prefixWord ++ tailWord_3673039) baseStart_3673039 baseEnd_3673039 := by
    simpa [prefixWord, tailWord_3673039, baseEnd_3673039] using wordTrace_append hprefix tailTrace_3673039
  have hstable : (prefixWord ++ tailWord_3673039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3673039).length < 2 ^ (prefixWord ++ tailWord_3673039).sum := by decide
  have hdescent : baseEnd_3673039 < baseStart_3673039 := by decide
  rcases family_descends (prefixWord ++ tailWord_3673039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3673063 : List Nat := [1, 1, 5, 2, 2, 1, 2, 4, 1, 4]
def baseStart_3673063 : Nat := 118140960795 + 3673063 * 2 ^ 59
def prefixEnd_3673063 : Nat := 4983230072969 + 3 ^ 40 * 3673063 * 2
def baseEnd_3673063 : Nat := 628682264415155952606799

theorem tailTrace_3673063 : CollatzResearch.WordTrace tailWord_3673063 prefixEnd_3673063 628682264415155952606799 := by
  unfold tailWord_3673063
  simp only [CollatzResearch.WordTrace]
  refine ⟨133967613492127535062871843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89311742328085023375247895 133967613492127535062871843)
  ·
    refine ⟨200951420238191302594307765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133967613492127535062871843 200951420238191302594307765)
    ·
      refine ⟨18839195647330434618216353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 200951420238191302594307765 18839195647330434618216353)
      ·
        refine ⟨14129396735497825963662265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18839195647330434618216353 14129396735497825963662265)
        ·
          refine ⟨10597047551623369472746699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14129396735497825963662265 10597047551623369472746699)
          ·
            refine ⟨15895571327435054209120049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10597047551623369472746699 15895571327435054209120049)
            ·
              refine ⟨11921678495576290656840037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15895571327435054209120049 11921678495576290656840037)
              ·
                refine ⟨2235314717920554498157507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11921678495576290656840037 2235314717920554498157507)
                ·
                  refine ⟨3352972076880831747236261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2235314717920554498157507 3352972076880831747236261)
                  ·
                    refine ⟨628682264415155952606799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3352972076880831747236261 628682264415155952606799)
                    ·
                      rfl

theorem cell23_3673063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 4, 1, 4].length) (baseStart_3673063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3673063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3673063 prefixEnd_3673063 := by exact prefixLift 3673063
  have htrace : WordTrace (prefixWord ++ tailWord_3673063) baseStart_3673063 baseEnd_3673063 := by
    simpa [prefixWord, tailWord_3673063, baseEnd_3673063] using wordTrace_append hprefix tailTrace_3673063
  have hstable : (prefixWord ++ tailWord_3673063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3673063).length < 2 ^ (prefixWord ++ tailWord_3673063).sum := by decide
  have hdescent : baseEnd_3673063 < baseStart_3673063 := by decide
  rcases family_descends (prefixWord ++ tailWord_3673063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3673082 : List Nat := [3, 1, 1, 1, 1, 2, 1, 3, 2, 1, 7]
def baseStart_3673082 : Nat := 118140960795 + 3673082 * 2 ^ 59
def prefixEnd_3673082 : Nat := 4983230072969 + 3 ^ 40 * 3673082 * 2
def baseEnd_3673082 : Nat := 1886056549377903283482809

theorem tailTrace_3673082 : CollatzResearch.WordTrace tailWord_3673082 prefixEnd_3673082 1886056549377903283482809 := by
  unfold tailWord_3673082
  simp only [CollatzResearch.WordTrace]
  refine ⟨33492076619764675326953375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89312204319372467538542333 33492076619764675326953375)
  ·
    refine ⟨50238114929647012990430063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33492076619764675326953375 50238114929647012990430063)
    ·
      refine ⟨75357172394470519485645095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50238114929647012990430063 75357172394470519485645095)
      ·
        refine ⟨113035758591705779228467643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75357172394470519485645095 113035758591705779228467643)
        ·
          refine ⟨169553637887558668842701465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113035758591705779228467643 169553637887558668842701465)
          ·
            refine ⟨127165228415669001632026099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169553637887558668842701465 127165228415669001632026099)
            ·
              refine ⟨190747842623503502448039149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127165228415669001632026099 190747842623503502448039149)
              ·
                refine ⟨71530440983813813418014681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 190747842623503502448039149 71530440983813813418014681)
                ·
                  refine ⟨53647830737860360063511011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71530440983813813418014681 53647830737860360063511011)
                  ·
                    refine ⟨80471746106790540095266517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53647830737860360063511011 80471746106790540095266517)
                    ·
                      refine ⟨1886056549377903283482809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 80471746106790540095266517 1886056549377903283482809)
                      ·
                        rfl

theorem cell23_3673082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 3, 2, 1, 7].length) (baseStart_3673082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3673082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3673082 prefixEnd_3673082 := by exact prefixLift 3673082
  have htrace : WordTrace (prefixWord ++ tailWord_3673082) baseStart_3673082 baseEnd_3673082 := by
    simpa [prefixWord, tailWord_3673082, baseEnd_3673082] using wordTrace_append hprefix tailTrace_3673082
  have hstable : (prefixWord ++ tailWord_3673082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3673082).length < 2 ^ (prefixWord ++ tailWord_3673082).sum := by decide
  have hdescent : baseEnd_3673082 < baseStart_3673082 := by decide
  rcases family_descends (prefixWord ++ tailWord_3673082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3673096 : List Nat := [2, 1, 3, 2, 1, 3, 2, 1, 1, 5, 2]
def baseStart_3673096 : Nat := 118140960795 + 3673096 * 2 ^ 59
def prefixEnd_3673096 : Nat := 4983230072969 + 3 ^ 40 * 3673096 * 2
def baseEnd_3673096 : Nat := 1886063738107066228707745

theorem tailTrace_3673096 : CollatzResearch.WordTrace tailWord_3673096 prefixEnd_3673096 1886063738107066228707745 := by
  unfold tailWord_3673096
  simp only [CollatzResearch.WordTrace]
  refine ⟨66984408550503990849411571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89312544734005321132548761 66984408550503990849411571)
  ·
    refine ⟨100476612825755986274117357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66984408550503990849411571 100476612825755986274117357)
    ·
      refine ⟨37678729809658494852794009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100476612825755986274117357 37678729809658494852794009)
      ·
        refine ⟨28259047357243871139595507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37678729809658494852794009 28259047357243871139595507)
        ·
          refine ⟨42388571035865806709393261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28259047357243871139595507 42388571035865806709393261)
          ·
            refine ⟨15895714138449677516022473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42388571035865806709393261 15895714138449677516022473)
            ·
              refine ⟨11921785603837258137016855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15895714138449677516022473 11921785603837258137016855)
              ·
                refine ⟨17882678405755887205525283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11921785603837258137016855 17882678405755887205525283)
                ·
                  refine ⟨26824017608633830808287925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17882678405755887205525283 26824017608633830808287925)
                  ·
                    refine ⟨2514751650809421638276993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26824017608633830808287925 2514751650809421638276993)
                    ·
                      refine ⟨1886063738107066228707745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2514751650809421638276993 1886063738107066228707745)
                      ·
                        rfl

theorem cell23_3673096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 1, 1, 5, 2].length) (baseStart_3673096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3673096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3673096 prefixEnd_3673096 := by exact prefixLift 3673096
  have htrace : WordTrace (prefixWord ++ tailWord_3673096) baseStart_3673096 baseEnd_3673096 := by
    simpa [prefixWord, tailWord_3673096, baseEnd_3673096] using wordTrace_append hprefix tailTrace_3673096
  have hstable : (prefixWord ++ tailWord_3673096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3673096).length < 2 ^ (prefixWord ++ tailWord_3673096).sum := by decide
  have hdescent : baseEnd_3673096 < baseStart_3673096 := by decide
  rcases family_descends (prefixWord ++ tailWord_3673096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3673136 : List Nat := [2, 1, 1, 1, 2, 4, 3, 3, 2, 4]
def baseStart_3673136 : Nat := 118140960795 + 3673136 * 2 ^ 59
def prefixEnd_3673136 : Nat := 4983230072969 + 3 ^ 40 * 3673136 * 2
def baseEnd_3673136 : Nat := 628694759111082024069187

theorem tailTrace_3673136 : CollatzResearch.WordTrace tailWord_3673136 prefixEnd_3673136 628694759111082024069187 := by
  unfold tailWord_3673136
  simp only [CollatzResearch.WordTrace]
  refine ⟨66985138010431534265139631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89313517347242045686852841 66985138010431534265139631)
  ·
    refine ⟨100477707015647301397709447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66985138010431534265139631 100477707015647301397709447)
    ·
      refine ⟨150716560523470952096564171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100477707015647301397709447 150716560523470952096564171)
      ·
        refine ⟨226074840785206428144846257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150716560523470952096564171 226074840785206428144846257)
        ·
          refine ⟨169556130588904821108634693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226074840785206428144846257 169556130588904821108634693)
          ·
            refine ⟨31791774485419653957869005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 169556130588904821108634693 31791774485419653957869005)
            ·
              refine ⟨11921915432032370234200877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31791774485419653957869005 11921915432032370234200877)
              ·
                refine ⟨4470718287012138837825329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11921915432032370234200877 4470718287012138837825329)
                ·
                  refine ⟨3353038715259104128368997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4470718287012138837825329 3353038715259104128368997)
                  ·
                    refine ⟨628694759111082024069187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3353038715259104128368997 628694759111082024069187)
                    ·
                      rfl

theorem cell23_3673136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 3, 2, 4].length) (baseStart_3673136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3673136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3673136 prefixEnd_3673136 := by exact prefixLift 3673136
  have htrace : WordTrace (prefixWord ++ tailWord_3673136) baseStart_3673136 baseEnd_3673136 := by
    simpa [prefixWord, tailWord_3673136, baseEnd_3673136] using wordTrace_append hprefix tailTrace_3673136
  have hstable : (prefixWord ++ tailWord_3673136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3673136).length < 2 ^ (prefixWord ++ tailWord_3673136).sum := by decide
  have hdescent : baseEnd_3673136 < baseStart_3673136 := by decide
  rcases family_descends (prefixWord ++ tailWord_3673136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3673139 : List Nat := [1, 1, 1, 2, 4, 1, 1, 5, 1, 2, 4]
def baseStart_3673139 : Nat := 118140960795 + 3673139 * 2 ^ 59
def prefixEnd_3673139 : Nat := 4983230072969 + 3 ^ 40 * 3673139 * 2
def baseEnd_3673139 : Nat := 1886085817775209560470047

theorem tailTrace_3673139 : CollatzResearch.WordTrace tailWord_3673139 prefixEnd_3673139 1886085817775209560470047 := by
  unfold tailWord_3673139
  simp only [CollatzResearch.WordTrace]
  refine ⟨133970385439852200042638471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89313590293234800028425647 133970385439852200042638471)
  ·
    refine ⟨200955578159778300063957707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133970385439852200042638471 200955578159778300063957707)
    ·
      refine ⟨301433367239667450095936561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200955578159778300063957707 301433367239667450095936561)
      ·
        refine ⟨226075025429750587571952421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 301433367239667450095936561 226075025429750587571952421)
        ·
          refine ⟨42389067268078235169741079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 226075025429750587571952421 42389067268078235169741079)
          ·
            refine ⟨63583600902117352754611619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42389067268078235169741079 63583600902117352754611619)
            ·
              refine ⟨95375401353176029131917429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63583600902117352754611619 95375401353176029131917429)
              ·
                refine ⟨8941443876860252731117259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 95375401353176029131917429 8941443876860252731117259)
                ·
                  refine ⟨13412165815290379096675889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8941443876860252731117259 13412165815290379096675889)
                  ·
                    refine ⟨10059124361467784322506917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13412165815290379096675889 10059124361467784322506917)
                    ·
                      refine ⟨1886085817775209560470047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10059124361467784322506917 1886085817775209560470047)
                      ·
                        rfl

theorem cell23_3673139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 5, 1, 2, 4].length) (baseStart_3673139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3673139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3673139 prefixEnd_3673139 := by exact prefixLift 3673139
  have htrace : WordTrace (prefixWord ++ tailWord_3673139) baseStart_3673139 baseEnd_3673139 := by
    simpa [prefixWord, tailWord_3673139, baseEnd_3673139] using wordTrace_append hprefix tailTrace_3673139
  have hstable : (prefixWord ++ tailWord_3673139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3673139).length < 2 ^ (prefixWord ++ tailWord_3673139).sum := by decide
  have hdescent : baseEnd_3673139 < baseStart_3673139 := by decide
  rcases family_descends (prefixWord ++ tailWord_3673139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3673140 : List Nat := [2, 5, 1, 2, 1, 3, 1, 2, 1, 5]
def baseStart_3673140 : Nat := 118140960795 + 3673140 * 2 ^ 59
def prefixEnd_3673140 : Nat := 4983230072969 + 3 ^ 40 * 3673140 * 2
def baseEnd_3673140 : Nat := 628695443751954685519181

theorem tailTrace_3673140 : CollatzResearch.WordTrace tailWord_3673140 prefixEnd_3673140 628695443751954685519181 := by
  unfold tailWord_3673140
  simp only [CollatzResearch.WordTrace]
  refine ⟨66985210956424288606712437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89313614608565718142283249 66985210956424288606712437)
  ·
    refine ⟨6279863527164777056879291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 66985210956424288606712437 6279863527164777056879291)
    ·
      refine ⟨9419795290747165585318937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6279863527164777056879291 9419795290747165585318937)
      ·
        refine ⟨7064846468060374188989203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9419795290747165585318937 7064846468060374188989203)
        ·
          refine ⟨10597269702090561283483805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7064846468060374188989203 10597269702090561283483805)
          ·
            refine ⟨3973976138283960481306427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10597269702090561283483805 3973976138283960481306427)
            ·
              refine ⟨5960964207425940721959641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3973976138283960481306427 5960964207425940721959641)
              ·
                refine ⟨4470723155569455541469731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5960964207425940721959641 4470723155569455541469731)
                ·
                  refine ⟨6706084733354183312204597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4470723155569455541469731 6706084733354183312204597)
                  ·
                    refine ⟨628695443751954685519181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6706084733354183312204597 628695443751954685519181)
                    ·
                      rfl

theorem cell23_3673140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 1, 2, 1, 5].length) (baseStart_3673140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3673140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3673140 prefixEnd_3673140 := by exact prefixLift 3673140
  have htrace : WordTrace (prefixWord ++ tailWord_3673140) baseStart_3673140 baseEnd_3673140 := by
    simpa [prefixWord, tailWord_3673140, baseEnd_3673140] using wordTrace_append hprefix tailTrace_3673140
  have hstable : (prefixWord ++ tailWord_3673140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3673140).length < 2 ^ (prefixWord ++ tailWord_3673140).sum := by decide
  have hdescent : baseEnd_3673140 < baseStart_3673140 := by decide
  rcases family_descends (prefixWord ++ tailWord_3673140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3673149 : List Nat := [1, 4, 1, 3, 1, 2, 2, 9]
def baseStart_3673149 : Nat := 118140960795 + 3673149 * 2 ^ 59
def prefixEnd_3673149 : Nat := 4983230072969 + 3 ^ 40 * 3673149 * 2
def baseEnd_3673149 : Nat := 69855220465990908197963

theorem tailTrace_3673149 : CollatzResearch.WordTrace tailWord_3673149 prefixEnd_3673149 69855220465990908197963 := by
  unfold tailWord_3673149
  simp only [CollatzResearch.WordTrace]
  refine ⟨133970750169815971750502501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89313833446543981167001667 133970750169815971750502501)
  ·
    refine ⟨25119515656840494703219219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133970750169815971750502501 25119515656840494703219219)
    ·
      refine ⟨37679273485260742054828829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25119515656840494703219219 37679273485260742054828829)
      ·
        refine ⟨14129727556972778270560811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37679273485260742054828829 14129727556972778270560811)
        ·
          refine ⟨21194591335459167405841217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14129727556972778270560811 21194591335459167405841217)
          ·
            refine ⟨15895943501594375554380913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21194591335459167405841217 15895943501594375554380913)
            ·
              refine ⟨11921957626195781665785685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15895943501594375554380913 11921957626195781665785685)
              ·
                refine ⟨69855220465990908197963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11921957626195781665785685 69855220465990908197963)
                ·
                  rfl

theorem cell23_3673149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 9].length) (baseStart_3673149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3673149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3673149 prefixEnd_3673149 := by exact prefixLift 3673149
  have htrace : WordTrace (prefixWord ++ tailWord_3673149) baseStart_3673149 baseEnd_3673149 := by
    simpa [prefixWord, tailWord_3673149, baseEnd_3673149] using wordTrace_append hprefix tailTrace_3673149
  have hstable : (prefixWord ++ tailWord_3673149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3673149).length < 2 ^ (prefixWord ++ tailWord_3673149).sum := by decide
  have hdescent : baseEnd_3673149 < baseStart_3673149 := by decide
  rcases family_descends (prefixWord ++ tailWord_3673149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3673160 : List Nat := [2, 1, 3, 1, 1, 1, 4, 5, 1, 2, 2]
def baseStart_3673160 : Nat := 118140960795 + 3673160 * 2 ^ 59
def prefixEnd_3673160 : Nat := 4983230072969 + 3 ^ 40 * 3673160 * 2
def baseEnd_3673160 : Nat := 1886096600868953978307451

theorem tailTrace_3673160 : CollatzResearch.WordTrace tailWord_3673160 prefixEnd_3673160 1886096600868953978307451 := by
  unfold tailWord_3673160
  simp only [CollatzResearch.WordTrace]
  refine ⟨66985575686388060314576467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89314100915184080419435289 66985575686388060314576467)
  ·
    refine ⟨100478363529582090471864701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66985575686388060314576467 100478363529582090471864701)
    ·
      refine ⟨37679386323593283926949263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100478363529582090471864701 37679386323593283926949263)
      ·
        refine ⟨56519079485389925890423895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37679386323593283926949263 56519079485389925890423895)
        ·
          refine ⟨84778619228084888835635843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56519079485389925890423895 84778619228084888835635843)
          ·
            refine ⟨127167928842127333253453765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84778619228084888835635843 127167928842127333253453765)
            ·
              refine ⟨23843986657898874985022581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 127167928842127333253453765 23843986657898874985022581)
              ·
                refine ⟨2235373749178019529845867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23843986657898874985022581 2235373749178019529845867)
                ·
                  refine ⟨3353060623767029294768801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2235373749178019529845867 3353060623767029294768801)
                  ·
                    refine ⟨2514795467825271971076601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3353060623767029294768801 2514795467825271971076601)
                    ·
                      refine ⟨1886096600868953978307451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2514795467825271971076601 1886096600868953978307451)
                      ·
                        rfl

theorem cell23_3673160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 5, 1, 2, 2].length) (baseStart_3673160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3673160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3673160 prefixEnd_3673160 := by exact prefixLift 3673160
  have htrace : WordTrace (prefixWord ++ tailWord_3673160) baseStart_3673160 baseEnd_3673160 := by
    simpa [prefixWord, tailWord_3673160, baseEnd_3673160] using wordTrace_append hprefix tailTrace_3673160
  have hstable : (prefixWord ++ tailWord_3673160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3673160).length < 2 ^ (prefixWord ++ tailWord_3673160).sum := by decide
  have hdescent : baseEnd_3673160 < baseStart_3673160 := by decide
  rcases family_descends (prefixWord ++ tailWord_3673160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3673193 : List Nat := [1, 2, 1, 1, 1, 6, 2, 3, 2, 1, 3]
def baseStart_3673193 : Nat := 118140960795 + 3673193 * 2 ^ 59
def prefixEnd_3673193 : Nat := 4983230072969 + 3 ^ 40 * 3673193 * 2
def baseEnd_3673193 : Nat := 1886113545730552349194799

theorem tailTrace_3673193 : CollatzResearch.WordTrace tailWord_3673193 prefixEnd_3673193 1886113545730552349194799 := by
  unfold tailWord_3673193
  simp only [CollatzResearch.WordTrace]
  refine ⟨133972354981656567265104233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89314903321104378176736155 133972354981656567265104233)
  ·
    refine ⟨100479266236242425448828175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133972354981656567265104233 100479266236242425448828175)
    ·
      refine ⟨150718899354363638173242263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100479266236242425448828175 150718899354363638173242263)
      ·
        refine ⟨226078349031545457259863395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150718899354363638173242263 226078349031545457259863395)
        ·
          refine ⟨339117523547318185889795093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226078349031545457259863395 339117523547318185889795093)
          ·
            refine ⟨15896133916280539963584145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 339117523547318185889795093 15896133916280539963584145)
            ·
              refine ⟨11922100437210404972688109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15896133916280539963584145 11922100437210404972688109)
              ·
                refine ⟨4470787663953901864758041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11922100437210404972688109 4470787663953901864758041)
                ·
                  refine ⟨3353090747965426398568531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4470787663953901864758041 3353090747965426398568531)
                  ·
                    refine ⟨5029636121948139597852797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3353090747965426398568531 5029636121948139597852797)
                    ·
                      refine ⟨1886113545730552349194799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5029636121948139597852797 1886113545730552349194799)
                      ·
                        rfl

theorem cell23_3673193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 3, 2, 1, 3].length) (baseStart_3673193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3673193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3673193 prefixEnd_3673193 := by exact prefixLift 3673193
  have htrace : WordTrace (prefixWord ++ tailWord_3673193) baseStart_3673193 baseEnd_3673193 := by
    simpa [prefixWord, tailWord_3673193, baseEnd_3673193] using wordTrace_append hprefix tailTrace_3673193
  have hstable : (prefixWord ++ tailWord_3673193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3673193).length < 2 ^ (prefixWord ++ tailWord_3673193).sum := by decide
  have hdescent : baseEnd_3673193 < baseStart_3673193 := by decide
  rcases family_descends (prefixWord ++ tailWord_3673193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3673199 : List Nat := [1, 1, 2, 1, 3, 3, 1, 2, 2, 3, 4]
def baseStart_3673199 : Nat := 118140960795 + 3673199 * 2 ^ 59
def prefixEnd_3673199 : Nat := 4983230072969 + 3 ^ 40 * 3673199 * 2
def baseEnd_3673199 : Nat := 1886116626614479325719771

theorem tailTrace_3673199 : CollatzResearch.WordTrace tailWord_3673199 prefixEnd_3673199 1886116626614479325719771 := by
  unfold tailWord_3673199
  simp only [CollatzResearch.WordTrace]
  refine ⟨133972573819634830289822651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89315049213089886859881767 133972573819634830289822651)
  ·
    refine ⟨200958860729452245434733977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133972573819634830289822651 200958860729452245434733977)
    ·
      refine ⟨150719145547089184076050483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200958860729452245434733977 150719145547089184076050483)
      ·
        refine ⟨226078718320633776114075725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150719145547089184076050483 226078718320633776114075725)
        ·
          refine ⟨84779519370237666042778397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 226078718320633776114075725 84779519370237666042778397)
          ·
            refine ⟨31792319763839124766041899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84779519370237666042778397 31792319763839124766041899)
            ·
              refine ⟨47688479645758687149062849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31792319763839124766041899 47688479645758687149062849)
              ·
                refine ⟨35766359734319015361797137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47688479645758687149062849 35766359734319015361797137)
                ·
                  refine ⟨26824769800739261521347853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35766359734319015361797137 26824769800739261521347853)
                  ·
                    refine ⟨10059288675277223070505445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26824769800739261521347853 10059288675277223070505445)
                    ·
                      refine ⟨1886116626614479325719771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10059288675277223070505445 1886116626614479325719771)
                      ·
                        rfl

theorem cell23_3673199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 2, 2, 3, 4].length) (baseStart_3673199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3673199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3673199 prefixEnd_3673199 := by exact prefixLift 3673199
  have htrace : WordTrace (prefixWord ++ tailWord_3673199) baseStart_3673199 baseEnd_3673199 := by
    simpa [prefixWord, tailWord_3673199, baseEnd_3673199] using wordTrace_append hprefix tailTrace_3673199
  have hstable : (prefixWord ++ tailWord_3673199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3673199).length < 2 ^ (prefixWord ++ tailWord_3673199).sum := by decide
  have hdescent : baseEnd_3673199 < baseStart_3673199 := by decide
  rcases family_descends (prefixWord ++ tailWord_3673199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3673206 : List Nat := [5, 1, 1, 2, 1, 1, 2, 1, 2, 2, 5]
def baseStart_3673206 : Nat := 118140960795 + 3673206 * 2 ^ 59
def prefixEnd_3673206 : Nat := 4983230072969 + 3 ^ 40 * 3673206 * 2
def baseEnd_3673206 : Nat := 1886120220979060798332239

theorem tailTrace_3673206 : CollatzResearch.WordTrace tailWord_3673206 prefixEnd_3673206 1886120220979060798332239 := by
  unfold tailWord_3673206
  simp only [CollatzResearch.WordTrace]
  refine ⟨8373301820663091905332967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 89315219420406313656884981 8373301820663091905332967)
  ·
    refine ⟨12559952730994637857999451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8373301820663091905332967 12559952730994637857999451)
    ·
      refine ⟨18839929096491956786999177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12559952730994637857999451 18839929096491956786999177)
      ·
        refine ⟨14129946822368967590249383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18839929096491956786999177 14129946822368967590249383)
        ·
          refine ⟨21194920233553451385374075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14129946822368967590249383 21194920233553451385374075)
          ·
            refine ⟨31792380350330177078061113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21194920233553451385374075 31792380350330177078061113)
            ·
              refine ⟨23844285262747632808545835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31792380350330177078061113 23844285262747632808545835)
              ·
                refine ⟨35766427894121449212818753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23844285262747632808545835 35766427894121449212818753)
                ·
                  refine ⟨26824820920591086909614065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35766427894121449212818753 26824820920591086909614065)
                  ·
                    refine ⟨20118615690443315182210549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26824820920591086909614065 20118615690443315182210549)
                    ·
                      refine ⟨1886120220979060798332239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20118615690443315182210549 1886120220979060798332239)
                      ·
                        rfl

theorem cell23_3673206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_3673206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3673206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3673206 prefixEnd_3673206 := by exact prefixLift 3673206
  have htrace : WordTrace (prefixWord ++ tailWord_3673206) baseStart_3673206 baseEnd_3673206 := by
    simpa [prefixWord, tailWord_3673206, baseEnd_3673206] using wordTrace_append hprefix tailTrace_3673206
  have hstable : (prefixWord ++ tailWord_3673206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3673206).length < 2 ^ (prefixWord ++ tailWord_3673206).sum := by decide
  have hdescent : baseEnd_3673206 < baseStart_3673206 := by decide
  rcases family_descends (prefixWord ++ tailWord_3673206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3673214 : List Nat := [4, 2, 4, 1, 1, 1, 1, 3, 1, 2, 3]
def baseStart_3673214 : Nat := 118140960795 + 3673214 * 2 ^ 59
def prefixEnd_3673214 : Nat := 4983230072969 + 3 ^ 40 * 3673214 * 2
def baseEnd_3673214 : Nat := 1886124328824296767032203

theorem tailTrace_3673214 : CollatzResearch.WordTrace tailWord_3673214 prefixEnd_3673214 1886124328824296767032203 := by
  unfold tailWord_3673214
  simp only [CollatzResearch.WordTrace]
  refine ⟨16746640114322560981452337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89315413943053658567745797 16746640114322560981452337)
  ·
    refine ⟨12559980085741920736089253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16746640114322560981452337 12559980085741920736089253)
    ·
      refine ⟨2354996266076610138016735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12559980085741920736089253 2354996266076610138016735)
      ·
        refine ⟨3532494399114915207025103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2354996266076610138016735 3532494399114915207025103)
        ·
          refine ⟨5298741598672372810537655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3532494399114915207025103 5298741598672372810537655)
          ·
            refine ⟨7948112398008559215806483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5298741598672372810537655 7948112398008559215806483)
            ·
              refine ⟨11922168597012838823709725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7948112398008559215806483 11922168597012838823709725)
              ·
                refine ⟨4470813223879814558891147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11922168597012838823709725 4470813223879814558891147)
                ·
                  refine ⟨6706219835819721838336721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4470813223879814558891147 6706219835819721838336721)
                  ·
                    refine ⟨5029664876864791378752541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6706219835819721838336721 5029664876864791378752541)
                    ·
                      refine ⟨1886124328824296767032203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5029664876864791378752541 1886124328824296767032203)
                      ·
                        rfl

theorem cell23_3673214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_3673214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3673214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3673214 prefixEnd_3673214 := by exact prefixLift 3673214
  have htrace : WordTrace (prefixWord ++ tailWord_3673214) baseStart_3673214 baseEnd_3673214 := by
    simpa [prefixWord, tailWord_3673214, baseEnd_3673214] using wordTrace_append hprefix tailTrace_3673214
  have hstable : (prefixWord ++ tailWord_3673214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3673214).length < 2 ^ (prefixWord ++ tailWord_3673214).sum := by decide
  have hdescent : baseEnd_3673214 < baseStart_3673214 := by decide
  rcases family_descends (prefixWord ++ tailWord_3673214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3673219 : List Nat := [1, 1, 1, 3, 3, 2, 2, 1, 1, 3, 5]
def baseStart_3673219 : Nat := 118140960795 + 3673219 * 2 ^ 59
def prefixEnd_3673219 : Nat := 4983230072969 + 3 ^ 40 * 3673219 * 2
def baseEnd_3673219 : Nat := 1886126896227569247469679

theorem tailTrace_3673219 : CollatzResearch.WordTrace tailWord_3673219 prefixEnd_3673219 1886126896227569247469679 := by
  unfold tailWord_3673219
  simp only [CollatzResearch.WordTrace]
  refine ⟨133973303279562373705550711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89315535519708249137033807 133973303279562373705550711)
  ·
    refine ⟨200959954919343560558326067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133973303279562373705550711 200959954919343560558326067)
    ·
      refine ⟨301439932379015340837489101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200959954919343560558326067 301439932379015340837489101)
      ·
        refine ⟨113039974642130752814058413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 301439932379015340837489101 113039974642130752814058413)
        ·
          refine ⟨42389990490799032305271905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113039974642130752814058413 42389990490799032305271905)
          ·
            refine ⟨31792492868099274228953929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42389990490799032305271905 31792492868099274228953929)
            ·
              refine ⟨23844369651074455671715447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31792492868099274228953929 23844369651074455671715447)
              ·
                refine ⟨35766554476611683507573171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23844369651074455671715447 35766554476611683507573171)
                ·
                  refine ⟨53649831714917525261359757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35766554476611683507573171 53649831714917525261359757)
                  ·
                    refine ⟨20118686893094071973009909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53649831714917525261359757 20118686893094071973009909)
                    ·
                      refine ⟨1886126896227569247469679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20118686893094071973009909 1886126896227569247469679)
                      ·
                        rfl

theorem cell23_3673219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 1, 1, 3, 5].length) (baseStart_3673219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3673219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3673219 prefixEnd_3673219 := by exact prefixLift 3673219
  have htrace : WordTrace (prefixWord ++ tailWord_3673219) baseStart_3673219 baseEnd_3673219 := by
    simpa [prefixWord, tailWord_3673219, baseEnd_3673219] using wordTrace_append hprefix tailTrace_3673219
  have hstable : (prefixWord ++ tailWord_3673219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3673219).length < 2 ^ (prefixWord ++ tailWord_3673219).sum := by decide
  have hdescent : baseEnd_3673219 < baseStart_3673219 := by decide
  rcases family_descends (prefixWord ++ tailWord_3673219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3673220 : List Nat := [2, 3, 2, 1, 2, 3, 1, 3, 1, 3, 2]
def baseStart_3673220 : Nat := 118140960795 + 3673220 * 2 ^ 59
def prefixEnd_3673220 : Nat := 4983230072969 + 3 ^ 40 * 3673220 * 2
def baseEnd_3673220 : Nat := 1886127409708223743557175

theorem tailTrace_3673220 : CollatzResearch.WordTrace tailWord_3673220 prefixEnd_3673220 1886127409708223743557175 := by
  unfold tailWord_3673220
  simp only [CollatzResearch.WordTrace]
  refine ⟨66986669876279375438168557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89315559835039167250891409 66986669876279375438168557)
  ·
    refine ⟨25120001203604765789313209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66986669876279375438168557 25120001203604765789313209)
    ·
      refine ⟨18840000902703574341984907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25120001203604765789313209 18840000902703574341984907)
      ·
        refine ⟨28260001354055361512977361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18840000902703574341984907 28260001354055361512977361)
        ·
          refine ⟨21195001015541521134733021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28260001354055361512977361 21195001015541521134733021)
          ·
            refine ⟨7948125380828070425524883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21195001015541521134733021 7948125380828070425524883)
            ·
              refine ⟨11922188071242105638287325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7948125380828070425524883 11922188071242105638287325)
              ·
                refine ⟨4470820526715789614357747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11922188071242105638287325 4470820526715789614357747)
                ·
                  refine ⟨6706230790073684421536621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4470820526715789614357747 6706230790073684421536621)
                  ·
                    refine ⟨2514836546277631658076233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6706230790073684421536621 2514836546277631658076233)
                    ·
                      refine ⟨1886127409708223743557175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2514836546277631658076233 1886127409708223743557175)
                      ·
                        rfl

theorem cell23_3673220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 3, 1, 3, 2].length) (baseStart_3673220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3673220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3673220 prefixEnd_3673220 := by exact prefixLift 3673220
  have htrace : WordTrace (prefixWord ++ tailWord_3673220) baseStart_3673220 baseEnd_3673220 := by
    simpa [prefixWord, tailWord_3673220, baseEnd_3673220] using wordTrace_append hprefix tailTrace_3673220
  have hstable : (prefixWord ++ tailWord_3673220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3673220).length < 2 ^ (prefixWord ++ tailWord_3673220).sum := by decide
  have hdescent : baseEnd_3673220 < baseStart_3673220 := by decide
  rcases family_descends (prefixWord ++ tailWord_3673220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3673273 : List Nat := [1, 2, 1, 4, 1, 3, 3, 3, 5]
def baseStart_3673273 : Nat := 118140960795 + 3673273 * 2 ^ 59
def prefixEnd_3673273 : Nat := 4983230072969 + 3 ^ 40 * 3673273 * 2
def baseEnd_3673273 : Nat := 209572736020323559577159

theorem tailTrace_3673273 : CollatzResearch.WordTrace tailWord_3673273 prefixEnd_3673273 209572736020323559577159 := by
  unfold tailWord_3673273
  simp only [CollatzResearch.WordTrace]
  refine ⟨133975272821366740928016473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89316848547577827285344315 133975272821366740928016473)
  ·
    refine ⟨100481454616025055696012355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133975272821366740928016473 100481454616025055696012355)
    ·
      refine ⟨150722181924037583544018533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100481454616025055696012355 150722181924037583544018533)
      ·
        refine ⟨28260409110757046914503475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 150722181924037583544018533 28260409110757046914503475)
        ·
          refine ⟨42390613666135570371755213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28260409110757046914503475 42390613666135570371755213)
          ·
            refine ⟨15896480124800838889408205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42390613666135570371755213 15896480124800838889408205)
            ·
              refine ⟨5961180046800314583528077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15896480124800838889408205 5961180046800314583528077)
              ·
                refine ⟨2235442517550117968823029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5961180046800314583528077 2235442517550117968823029)
                ·
                  refine ⟨209572736020323559577159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2235442517550117968823029 209572736020323559577159)
                  ·
                    rfl

theorem cell23_3673273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 3, 3, 5].length) (baseStart_3673273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3673273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3673273 prefixEnd_3673273 := by exact prefixLift 3673273
  have htrace : WordTrace (prefixWord ++ tailWord_3673273) baseStart_3673273 baseEnd_3673273 := by
    simpa [prefixWord, tailWord_3673273, baseEnd_3673273] using wordTrace_append hprefix tailTrace_3673273
  have hstable : (prefixWord ++ tailWord_3673273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3673273).length < 2 ^ (prefixWord ++ tailWord_3673273).sum := by decide
  have hdescent : baseEnd_3673273 < baseStart_3673273 := by decide
  rcases family_descends (prefixWord ++ tailWord_3673273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3673290 : List Nat := [3, 1, 2, 1, 3, 3, 3, 2, 5]
def baseStart_3673290 : Nat := 118140960795 + 3673290 * 2 ^ 59
def prefixEnd_3673290 : Nat := 4983230072969 + 3 ^ 40 * 3673290 * 2
def baseEnd_3673290 : Nat := 209573705928226496631317

theorem tailTrace_3673290 : CollatzResearch.WordTrace tailWord_3673290 prefixEnd_3673290 209573705928226496631317 := by
  unfold tailWord_3673290
  simp only [CollatzResearch.WordTrace]
  refine ⟨33493973215576288207846331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89317261908203435220923549 33493973215576288207846331)
  ·
    refine ⟨50240959823364432311769497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33493973215576288207846331 50240959823364432311769497)
    ·
      refine ⟨37680719867523324233827123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50240959823364432311769497 37680719867523324233827123)
      ·
        refine ⟨56521079801284986350740685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37680719867523324233827123 56521079801284986350740685)
        ·
          refine ⟨21195404925481869881527757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56521079801284986350740685 21195404925481869881527757)
          ·
            refine ⟨7948276847055701205572909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21195404925481869881527757 7948276847055701205572909)
            ·
              refine ⟨2980603817645887952089841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7948276847055701205572909 2980603817645887952089841)
              ·
                refine ⟨2235452863234415964067381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2980603817645887952089841 2235452863234415964067381)
                ·
                  refine ⟨209573705928226496631317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2235452863234415964067381 209573705928226496631317)
                  ·
                    rfl

theorem cell23_3673290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 3, 2, 5].length) (baseStart_3673290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3673290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3673290 prefixEnd_3673290 := by exact prefixLift 3673290
  have htrace : WordTrace (prefixWord ++ tailWord_3673290) baseStart_3673290 baseEnd_3673290 := by
    simpa [prefixWord, tailWord_3673290, baseEnd_3673290] using wordTrace_append hprefix tailTrace_3673290
  have hstable : (prefixWord ++ tailWord_3673290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3673290).length < 2 ^ (prefixWord ++ tailWord_3673290).sum := by decide
  have hdescent : baseEnd_3673290 < baseStart_3673290 := by decide
  rcases family_descends (prefixWord ++ tailWord_3673290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3673306 : List Nat := [3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 4]
def baseStart_3673306 : Nat := 118140960795 + 3673306 * 2 ^ 59
def prefixEnd_3673306 : Nat := 4983230072969 + 3 ^ 40 * 3673306 * 2
def baseEnd_3673306 : Nat := 1886171569044510407081779

theorem tailTrace_3673306 : CollatzResearch.WordTrace tailWord_3673306 prefixEnd_3673306 1886171569044510407081779 := by
  unfold tailWord_3673306
  simp only [CollatzResearch.WordTrace]
  refine ⟨33494119107561796890991943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89317650953498125042645181 33494119107561796890991943)
  ·
    refine ⟨50241178661342695336487915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33494119107561796890991943 50241178661342695336487915)
    ·
      refine ⟨75361767992014043004731873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50241178661342695336487915 75361767992014043004731873)
      ·
        refine ⟨56521325994010532253548905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75361767992014043004731873 56521325994010532253548905)
        ·
          refine ⟨42390994495507899190161679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56521325994010532253548905 42390994495507899190161679)
          ·
            refine ⟨63586491743261848785242519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42390994495507899190161679 63586491743261848785242519)
            ·
              refine ⟨95379737614892773177863779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63586491743261848785242519 95379737614892773177863779)
              ·
                refine ⟨143069606422339159766795669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95379737614892773177863779 143069606422339159766795669)
                ·
                  refine ⟨6706387801047148114068547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 143069606422339159766795669 6706387801047148114068547)
                  ·
                    refine ⟨10059581701570722171102821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6706387801047148114068547 10059581701570722171102821)
                    ·
                      refine ⟨1886171569044510407081779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10059581701570722171102821 1886171569044510407081779)
                      ·
                        rfl

theorem cell23_3673306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 4].length) (baseStart_3673306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3673306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3673306 prefixEnd_3673306 := by exact prefixLift 3673306
  have htrace : WordTrace (prefixWord ++ tailWord_3673306) baseStart_3673306 baseEnd_3673306 := by
    simpa [prefixWord, tailWord_3673306, baseEnd_3673306] using wordTrace_append hprefix tailTrace_3673306
  have hstable : (prefixWord ++ tailWord_3673306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3673306).length < 2 ^ (prefixWord ++ tailWord_3673306).sum := by decide
  have hdescent : baseEnd_3673306 < baseStart_3673306 := by decide
  rcases family_descends (prefixWord ++ tailWord_3673306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3673323 : List Nat := [1, 1, 1, 1, 2, 7, 2, 1, 2, 1, 4]
def baseStart_3673323 : Nat := 118140960795 + 3673323 * 2 ^ 59
def prefixEnd_3673323 : Nat := 4983230072969 + 3 ^ 40 * 3673323 * 2
def baseEnd_3673323 : Nat := 1886180298215636840569201

theorem tailTrace_3673323 : CollatzResearch.WordTrace tailWord_3673323 prefixEnd_3673323 1886180298215636840569201 := by
  unfold tailWord_3673323
  simp only [CollatzResearch.WordTrace]
  refine ⟨133977096471185599467336623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89318064314123732978224415 133977096471185599467336623)
  ·
    refine ⟨200965644706778399201004935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133977096471185599467336623 200965644706778399201004935)
    ·
      refine ⟨301448467060167598801507403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200965644706778399201004935 301448467060167598801507403)
      ·
        refine ⟨452172700590251398202261105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301448467060167598801507403 452172700590251398202261105)
        ·
          refine ⟨339129525442688548651695829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 452172700590251398202261105 339129525442688548651695829)
          ·
            refine ⟨7948348252563012859024121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 339129525442688548651695829 7948348252563012859024121)
            ·
              refine ⟨5961261189422259644268091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7948348252563012859024121 5961261189422259644268091)
              ·
                refine ⟨8941891784133389466402137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5961261189422259644268091 8941891784133389466402137)
                ·
                  refine ⟨6706418838100042099801603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8941891784133389466402137 6706418838100042099801603)
                  ·
                    refine ⟨10059628257150063149702405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6706418838100042099801603 10059628257150063149702405)
                    ·
                      refine ⟨1886180298215636840569201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10059628257150063149702405 1886180298215636840569201)
                      ·
                        rfl

theorem cell23_3673323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 2, 1, 2, 1, 4].length) (baseStart_3673323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3673323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3673323 prefixEnd_3673323 := by exact prefixLift 3673323
  have htrace : WordTrace (prefixWord ++ tailWord_3673323) baseStart_3673323 baseEnd_3673323 := by
    simpa [prefixWord, tailWord_3673323, baseEnd_3673323] using wordTrace_append hprefix tailTrace_3673323
  have hstable : (prefixWord ++ tailWord_3673323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3673323).length < 2 ^ (prefixWord ++ tailWord_3673323).sum := by decide
  have hdescent : baseEnd_3673323 < baseStart_3673323 := by decide
  rcases family_descends (prefixWord ++ tailWord_3673323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3673343 : List Nat := [1, 1, 2, 2, 1, 5, 2, 2, 2, 2, 3]
def baseStart_3673343 : Nat := 118140960795 + 3673343 * 2 ^ 59
def prefixEnd_3673343 : Nat := 4983230072969 + 3 ^ 40 * 3673343 * 2
def baseEnd_3673343 : Nat := 1886190567828726762319109

theorem tailTrace_3673343 : CollatzResearch.WordTrace tailWord_3673343 prefixEnd_3673343 1886190567828726762319109 := by
  unfold tailWord_3673343
  simp only [CollatzResearch.WordTrace]
  refine ⟨133977825931113142883064683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89318550620742095255376455 133977825931113142883064683)
  ·
    refine ⟨200966738896669714324597025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133977825931113142883064683 200966738896669714324597025)
    ·
      refine ⟨150725054172502285743447769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200966738896669714324597025 150725054172502285743447769)
      ·
        refine ⟨113043790629376714307585827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150725054172502285743447769 113043790629376714307585827)
        ·
          refine ⟨169565685944065071461378741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113043790629376714307585827 169565685944065071461378741)
          ·
            refine ⟨15896783057256100449504257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 169565685944065071461378741 15896783057256100449504257)
            ·
              refine ⟨11922587292942075337128193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15896783057256100449504257 11922587292942075337128193)
              ·
                refine ⟨8941940469706556502846145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11922587292942075337128193 8941940469706556502846145)
                ·
                  refine ⟨6706455352279917377134609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8941940469706556502846145 6706455352279917377134609)
                  ·
                    refine ⟨5029841514209938032850957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6706455352279917377134609 5029841514209938032850957)
                    ·
                      refine ⟨1886190567828726762319109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5029841514209938032850957 1886190567828726762319109)
                      ·
                        rfl

theorem cell23_3673343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 2, 2, 2, 3].length) (baseStart_3673343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3673343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3673343 prefixEnd_3673343 := by exact prefixLift 3673343
  have htrace : WordTrace (prefixWord ++ tailWord_3673343) baseStart_3673343 baseEnd_3673343 := by
    simpa [prefixWord, tailWord_3673343, baseEnd_3673343] using wordTrace_append hprefix tailTrace_3673343
  have hstable : (prefixWord ++ tailWord_3673343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3673343).length < 2 ^ (prefixWord ++ tailWord_3673343).sum := by decide
  have hdescent : baseEnd_3673343 < baseStart_3673343 := by decide
  rcases family_descends (prefixWord ++ tailWord_3673343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3673374 : List Nat := [4, 3, 2, 1, 2, 2, 1, 1, 2, 1, 4]
def baseStart_3673374 : Nat := 118140960795 + 3673374 * 2 ^ 59
def prefixEnd_3673374 : Nat := 4983230072969 + 3 ^ 40 * 3673374 * 2
def baseEnd_3673374 : Nat := 1886206485729016141031467

theorem tailTrace_3673374 : CollatzResearch.WordTrace tailWord_3673374 prefixEnd_3673374 1886206485729016141031467 := by
  unfold tailWord_3673374
  simp only [CollatzResearch.WordTrace]
  refine ⟨16747369574250104397180397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89319304396000556784962117 16747369574250104397180397)
  ·
    refine ⟨6280263590343789148942649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16747369574250104397180397 6280263590343789148942649)
    ·
      refine ⟨4710197692757841861706987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6280263590343789148942649 4710197692757841861706987)
      ·
        refine ⟨7065296539136762792560481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4710197692757841861706987 7065296539136762792560481)
        ·
          refine ⟨5298972404352572094420361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7065296539136762792560481 5298972404352572094420361)
          ·
            refine ⟨3974229303264429070815271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5298972404352572094420361 3974229303264429070815271)
            ·
              refine ⟨5961343954896643606222907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3974229303264429070815271 5961343954896643606222907)
              ·
                refine ⟨8942015932344965409334361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5961343954896643606222907 8942015932344965409334361)
                ·
                  refine ⟨6706511949258724057000771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8942015932344965409334361 6706511949258724057000771)
                  ·
                    refine ⟨10059767923888086085501157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6706511949258724057000771 10059767923888086085501157)
                    ·
                      refine ⟨1886206485729016141031467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10059767923888086085501157 1886206485729016141031467)
                      ·
                        rfl

theorem cell23_3673374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_3673374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3673374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3673374 prefixEnd_3673374 := by exact prefixLift 3673374
  have htrace : WordTrace (prefixWord ++ tailWord_3673374) baseStart_3673374 baseEnd_3673374 := by
    simpa [prefixWord, tailWord_3673374, baseEnd_3673374] using wordTrace_append hprefix tailTrace_3673374
  have hstable : (prefixWord ++ tailWord_3673374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3673374).length < 2 ^ (prefixWord ++ tailWord_3673374).sum := by decide
  have hdescent : baseEnd_3673374 < baseStart_3673374 := by decide
  rcases family_descends (prefixWord ++ tailWord_3673374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3673407 : List Nat := [1, 1, 2, 2, 4, 2, 2, 4, 1, 1, 3]
def baseStart_3673407 : Nat := 118140960795 + 3673407 * 2 ^ 59
def prefixEnd_3673407 : Nat := 4983230072969 + 3 ^ 40 * 3673407 * 2
def baseEnd_3673407 : Nat := 1886223430590614511918815

theorem tailTrace_3673407 : CollatzResearch.WordTrace tailWord_3673407 prefixEnd_3673407 1886223430590614511918815 := by
  unfold tailWord_3673407
  simp only [CollatzResearch.WordTrace]
  refine ⟨133980160202881281813394475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89320106801920854542262983 133980160202881281813394475)
  ·
    refine ⟨200970240304321922720091713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133980160202881281813394475 200970240304321922720091713)
    ·
      refine ⟨150727680228241442040068785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200970240304321922720091713 150727680228241442040068785)
      ·
        refine ⟨113045760171181081530051589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150727680228241442040068785 113045760171181081530051589)
        ·
          refine ⟨21196080032096452786884673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 113045760171181081530051589 21196080032096452786884673)
          ·
            refine ⟨15897060024072339590163505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21196080032096452786884673 15897060024072339590163505)
            ·
              refine ⟨11922795018054254692622629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15897060024072339590163505 11922795018054254692622629)
              ·
                refine ⟨2235524065885172754866743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11922795018054254692622629 2235524065885172754866743)
                ·
                  refine ⟨3353286098827759132300115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2235524065885172754866743 3353286098827759132300115)
                  ·
                    refine ⟨5029929148241638698450173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3353286098827759132300115 5029929148241638698450173)
                    ·
                      refine ⟨1886223430590614511918815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5029929148241638698450173 1886223430590614511918815)
                      ·
                        rfl

theorem cell23_3673407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 4, 1, 1, 3].length) (baseStart_3673407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3673407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3673407 prefixEnd_3673407 := by exact prefixLift 3673407
  have htrace : WordTrace (prefixWord ++ tailWord_3673407) baseStart_3673407 baseEnd_3673407 := by
    simpa [prefixWord, tailWord_3673407, baseEnd_3673407] using wordTrace_append hprefix tailTrace_3673407
  have hstable : (prefixWord ++ tailWord_3673407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3673407).length < 2 ^ (prefixWord ++ tailWord_3673407).sum := by decide
  have hdescent : baseEnd_3673407 < baseStart_3673407 := by decide
  rcases family_descends (prefixWord ++ tailWord_3673407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3673433 : List Nat := [1, 2, 1, 2, 2, 2, 2, 3, 3, 2, 3]
def baseStart_3673433 : Nat := 118140960795 + 3673433 * 2 ^ 59
def prefixEnd_3673433 : Nat := 4983230072969 + 3 ^ 40 * 3673433 * 2
def baseEnd_3673433 : Nat := 1886236781087631410193695

theorem tailTrace_3673433 : CollatzResearch.WordTrace tailWord_3673433 prefixEnd_3673433 1886236781087631410193695 := by
  unfold tailWord_3673433
  simp only [CollatzResearch.WordTrace]
  refine ⟨133981108500787088253840953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89320739000524725502560635 133981108500787088253840953)
  ·
    refine ⟨100485831375590316190380715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133981108500787088253840953 100485831375590316190380715)
    ·
      refine ⟨150728747063385474285571073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100485831375590316190380715 150728747063385474285571073)
      ·
        refine ⟨113046560297539105714178305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150728747063385474285571073 113046560297539105714178305)
        ·
          refine ⟨84784920223154329285633729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113046560297539105714178305 84784920223154329285633729)
          ·
            refine ⟨63588690167365746964225297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84784920223154329285633729 63588690167365746964225297)
            ·
              refine ⟨47691517625524310223168973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63588690167365746964225297 47691517625524310223168973)
              ·
                refine ⟨17884319109571616333688365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47691517625524310223168973 17884319109571616333688365)
                ·
                  refine ⟨6706619666089356125133137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17884319109571616333688365 6706619666089356125133137)
                  ·
                    refine ⟨5029964749567017093849853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6706619666089356125133137 5029964749567017093849853)
                    ·
                      refine ⟨1886236781087631410193695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5029964749567017093849853 1886236781087631410193695)
                      ·
                        rfl

theorem cell23_3673433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 3, 3, 2, 3].length) (baseStart_3673433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3673433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3673433 prefixEnd_3673433 := by exact prefixLift 3673433
  have htrace : WordTrace (prefixWord ++ tailWord_3673433) baseStart_3673433 baseEnd_3673433 := by
    simpa [prefixWord, tailWord_3673433, baseEnd_3673433] using wordTrace_append hprefix tailTrace_3673433
  have hstable : (prefixWord ++ tailWord_3673433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3673433).length < 2 ^ (prefixWord ++ tailWord_3673433).sum := by decide
  have hdescent : baseEnd_3673433 < baseStart_3673433 := by decide
  rcases family_descends (prefixWord ++ tailWord_3673433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3673453 : List Nat := [1, 5, 1, 1, 1, 5, 9]
def baseStart_3673453 : Nat := 118140960795 + 3673453 * 2 ^ 59
def prefixEnd_3673453 : Nat := 4983230072969 + 3 ^ 40 * 3673453 * 2
def baseEnd_3673453 : Nat := 23287000625934831258563

theorem tailTrace_3673453 : CollatzResearch.WordTrace tailWord_3673453 prefixEnd_3673453 23287000625934831258563 := by
  unfold tailWord_3673453
  simp only [CollatzResearch.WordTrace]
  refine ⟨133981837960714631669569013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89321225307143087779712675 133981837960714631669569013)
  ·
    refine ⟨12560797308816996719022095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 133981837960714631669569013 12560797308816996719022095)
    ·
      refine ⟨18841195963225495078533143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12560797308816996719022095 18841195963225495078533143)
      ·
        refine ⟨28261793944838242617799715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18841195963225495078533143 28261793944838242617799715)
        ·
          refine ⟨42392690917257363926699573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28261793944838242617799715 42392690917257363926699573)
          ·
            refine ⟨3974314773492877868128085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42392690917257363926699573 3974314773492877868128085)
            ·
              refine ⟨23287000625934831258563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3974314773492877868128085 23287000625934831258563)
              ·
                rfl

theorem cell23_3673453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 9].length) (baseStart_3673453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3673453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3673453 prefixEnd_3673453 := by exact prefixLift 3673453
  have htrace : WordTrace (prefixWord ++ tailWord_3673453) baseStart_3673453 baseEnd_3673453 := by
    simpa [prefixWord, tailWord_3673453, baseEnd_3673453] using wordTrace_append hprefix tailTrace_3673453
  have hstable : (prefixWord ++ tailWord_3673453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3673453).length < 2 ^ (prefixWord ++ tailWord_3673453).sum := by decide
  have hdescent : baseEnd_3673453 < baseStart_3673453 := by decide
  rcases family_descends (prefixWord ++ tailWord_3673453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3673466 : List Nat := [3, 1, 1, 1, 1, 1, 2, 3, 1, 9]
def baseStart_3673466 : Nat := 118140960795 + 3673466 * 2 ^ 59
def prefixEnd_3673466 : Nat := 4983230072969 + 3 ^ 40 * 3673466 * 2
def baseEnd_3673466 : Nat := 628751241983076593693681

theorem tailTrace_3673466 : CollatzResearch.WordTrace tailWord_3673466 prefixEnd_3673466 628751241983076593693681 := by
  unfold tailWord_3673466
  simp only [CollatzResearch.WordTrace]
  refine ⟨33495578027416883722448063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89321541406445023259861501 33495578027416883722448063)
  ·
    refine ⟨50243367041125325583672095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33495578027416883722448063 50243367041125325583672095)
    ·
      refine ⟨75365050561687988375508143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50243367041125325583672095 75365050561687988375508143)
      ·
        refine ⟨113047575842531982563262215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75365050561687988375508143 113047575842531982563262215)
        ·
          refine ⟨169571363763797973844893323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113047575842531982563262215 169571363763797973844893323)
          ·
            refine ⟨254357045645696960767339985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169571363763797973844893323 254357045645696960767339985)
            ·
              refine ⟨190767784234272720575504989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 254357045645696960767339985 190767784234272720575504989)
              ·
                refine ⟨71537919087852270215814371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 190767784234272720575504989 71537919087852270215814371)
                ·
                  refine ⟨107306878631778405323721557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71537919087852270215814371 107306878631778405323721557)
                  ·
                    refine ⟨628751241983076593693681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 107306878631778405323721557 628751241983076593693681)
                    ·
                      rfl

theorem cell23_3673466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 3, 1, 9].length) (baseStart_3673466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3673466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3673466 prefixEnd_3673466 := by exact prefixLift 3673466
  have htrace : WordTrace (prefixWord ++ tailWord_3673466) baseStart_3673466 baseEnd_3673466 := by
    simpa [prefixWord, tailWord_3673466, baseEnd_3673466] using wordTrace_append hprefix tailTrace_3673466
  have hstable : (prefixWord ++ tailWord_3673466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3673466).length < 2 ^ (prefixWord ++ tailWord_3673466).sum := by decide
  have hdescent : baseEnd_3673466 < baseStart_3673466 := by decide
  rcases family_descends (prefixWord ++ tailWord_3673466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3673474 : List Nat := [3, 4, 2, 1, 1, 2, 1, 3, 2, 4]
def baseStart_3673474 : Nat := 118140960795 + 3673474 * 2 ^ 59
def prefixEnd_3673474 : Nat := 4983230072969 + 3 ^ 40 * 3673474 * 2
def baseEnd_3673474 : Nat := 628752611264821916593669

theorem tailTrace_3673474 : CollatzResearch.WordTrace tailWord_3673474 prefixEnd_3673474 628752611264821916593669 := by
  unfold tailWord_3673474
  simp only [CollatzResearch.WordTrace]
  refine ⟨33495650973409638064020869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89321735929092368170722317 33495650973409638064020869)
  ·
    refine ⟨6280434557514307137003913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33495650973409638064020869 6280434557514307137003913)
    ·
      refine ⟨4710325918135730352752935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6280434557514307137003913 4710325918135730352752935)
      ·
        refine ⟨7065488877203595529129403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4710325918135730352752935 7065488877203595529129403)
        ·
          refine ⟨10598233315805393293694105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7065488877203595529129403 10598233315805393293694105)
          ·
            refine ⟨7948674986854044970270579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10598233315805393293694105 7948674986854044970270579)
            ·
              refine ⟨11923012480281067455405869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7948674986854044970270579 11923012480281067455405869)
              ·
                refine ⟨4471129680105400295777201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11923012480281067455405869 4471129680105400295777201)
                ·
                  refine ⟨3353347260079050221832901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4471129680105400295777201 3353347260079050221832901)
                  ·
                    refine ⟨628752611264821916593669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3353347260079050221832901 628752611264821916593669)
                    ·
                      rfl

theorem cell23_3673474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_3673474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3673474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3673474 prefixEnd_3673474 := by exact prefixLift 3673474
  have htrace : WordTrace (prefixWord ++ tailWord_3673474) baseStart_3673474 baseEnd_3673474 := by
    simpa [prefixWord, tailWord_3673474, baseEnd_3673474] using wordTrace_append hprefix tailTrace_3673474
  have hstable : (prefixWord ++ tailWord_3673474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3673474).length < 2 ^ (prefixWord ++ tailWord_3673474).sum := by decide
  have hdescent : baseEnd_3673474 < baseStart_3673474 := by decide
  rcases family_descends (prefixWord ++ tailWord_3673474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3673543 : List Nat := [1, 1, 4, 1, 1, 3, 3, 2, 7]
def baseStart_3673543 : Nat := 118140960795 + 3673543 * 2 ^ 59
def prefixEnd_3673543 : Nat := 4983230072969 + 3 ^ 40 * 3673543 * 2
def baseEnd_3673543 : Nat := 209588140439958442202021

theorem tailTrace_3673543 : CollatzResearch.WordTrace tailWord_3673543 prefixEnd_3673543 209588140439958442202021 := by
  unfold tailWord_3673543
  simp only [CollatzResearch.WordTrace]
  refine ⟨133985120530388577040345283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89323413686925718026896855 133985120530388577040345283)
  ·
    refine ⟨200977680795582865560517925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133985120530388577040345283 200977680795582865560517925)
    ·
      refine ⟨37683315149171787292597111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 200977680795582865560517925 37683315149171787292597111)
      ·
        refine ⟨56524972723757680938895667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37683315149171787292597111 56524972723757680938895667)
        ·
          refine ⟨84787459085636521408343501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56524972723757680938895667 84787459085636521408343501)
          ·
            refine ⟨31795297157113695528128813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84787459085636521408343501 31795297157113695528128813)
            ·
              refine ⟨11923236433917635823048305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31795297157113695528128813 11923236433917635823048305)
              ·
                refine ⟨8942427325438226867286229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11923236433917635823048305 8942427325438226867286229)
                ·
                  refine ⟨209588140439958442202021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8942427325438226867286229 209588140439958442202021)
                  ·
                    rfl

theorem cell23_3673543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 2, 7].length) (baseStart_3673543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3673543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3673543 prefixEnd_3673543 := by exact prefixLift 3673543
  have htrace : WordTrace (prefixWord ++ tailWord_3673543) baseStart_3673543 baseEnd_3673543 := by
    simpa [prefixWord, tailWord_3673543, baseEnd_3673543] using wordTrace_append hprefix tailTrace_3673543
  have hstable : (prefixWord ++ tailWord_3673543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3673543).length < 2 ^ (prefixWord ++ tailWord_3673543).sum := by decide
  have hdescent : baseEnd_3673543 < baseStart_3673543 := by decide
  rcases family_descends (prefixWord ++ tailWord_3673543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3673558 : List Nat := [5, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2]
def baseStart_3673558 : Nat := 118140960795 + 3673558 * 2 ^ 59
def prefixEnd_3673558 : Nat := 4983230072969 + 3 ^ 40 * 3673558 * 2
def baseEnd_3673558 : Nat := 1886300966169443421130621

theorem tailTrace_3673558 : CollatzResearch.WordTrace tailWord_3673558 prefixEnd_3673558 1886300966169443421130621 := by
  unfold tailWord_3673558
  simp only [CollatzResearch.WordTrace]
  refine ⟨8374104226583389662633833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 89323778416889489734760885 8374104226583389662633833)
  ·
    refine ⟨6280578169937542246975375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8374104226583389662633833 6280578169937542246975375)
    ·
      refine ⟨9420867254906313370463063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6280578169937542246975375 9420867254906313370463063)
      ·
        refine ⟨14131300882359470055694595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9420867254906313370463063 14131300882359470055694595)
        ·
          refine ⟨21196951323539205083541893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14131300882359470055694595 21196951323539205083541893)
          ·
            refine ⟨3974428373163600953164105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21196951323539205083541893 3974428373163600953164105)
            ·
              refine ⟨2980821279872700714873079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3974428373163600953164105 2980821279872700714873079)
              ·
                refine ⟨4471231919809051072309619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2980821279872700714873079 4471231919809051072309619)
                ·
                  refine ⟨6706847879713576608464429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4471231919809051072309619 6706847879713576608464429)
                  ·
                    refine ⟨2515067954892591228174161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6706847879713576608464429 2515067954892591228174161)
                    ·
                      refine ⟨1886300966169443421130621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2515067954892591228174161 1886300966169443421130621)
                      ·
                        rfl

theorem cell23_3673558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2].length) (baseStart_3673558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3673558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3673558 prefixEnd_3673558 := by exact prefixLift 3673558
  have htrace : WordTrace (prefixWord ++ tailWord_3673558) baseStart_3673558 baseEnd_3673558 := by
    simpa [prefixWord, tailWord_3673558, baseEnd_3673558] using wordTrace_append hprefix tailTrace_3673558
  have hstable : (prefixWord ++ tailWord_3673558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3673558).length < 2 ^ (prefixWord ++ tailWord_3673558).sum := by decide
  have hdescent : baseEnd_3673558 < baseStart_3673558 := by decide
  rcases family_descends (prefixWord ++ tailWord_3673558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3673560 : List Nat := [2, 1, 2, 2, 2, 1, 3, 5, 5]
def baseStart_3673560 : Nat := 118140960795 + 3673560 * 2 ^ 59
def prefixEnd_3673560 : Nat := 4983230072969 + 3 ^ 40 * 3673560 * 2
def baseEnd_3673560 : Nat := 209589110347861379256179

theorem tailTrace_3673560 : CollatzResearch.WordTrace tailWord_3673560 prefixEnd_3673560 209589110347861379256179 := by
  unfold tailWord_3673560
  simp only [CollatzResearch.WordTrace]
  refine ⟨66992870285663494471857067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89323827047551325962476089 66992870285663494471857067)
  ·
    refine ⟨100489305428495241707785601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66992870285663494471857067 100489305428495241707785601)
    ·
      refine ⟨75366979071371431280839201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100489305428495241707785601 75366979071371431280839201)
      ·
        refine ⟨56525234303528573460629401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75366979071371431280839201 56525234303528573460629401)
        ·
          refine ⟨42393925727646430095472051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56525234303528573460629401 42393925727646430095472051)
          ·
            refine ⟨63590888591469645143208077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42393925727646430095472051 63590888591469645143208077)
            ·
              refine ⟨23846583221801116928703029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63590888591469645143208077 23846583221801116928703029)
              ·
                refine ⟨2235617177043854712065909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23846583221801116928703029 2235617177043854712065909)
                ·
                  refine ⟨209589110347861379256179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2235617177043854712065909 209589110347861379256179)
                  ·
                    rfl

theorem cell23_3673560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 5, 5].length) (baseStart_3673560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3673560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3673560 prefixEnd_3673560 := by exact prefixLift 3673560
  have htrace : WordTrace (prefixWord ++ tailWord_3673560) baseStart_3673560 baseEnd_3673560 := by
    simpa [prefixWord, tailWord_3673560, baseEnd_3673560] using wordTrace_append hprefix tailTrace_3673560
  have hstable : (prefixWord ++ tailWord_3673560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3673560).length < 2 ^ (prefixWord ++ tailWord_3673560).sum := by decide
  have hdescent : baseEnd_3673560 < baseStart_3673560 := by decide
  rcases family_descends (prefixWord ++ tailWord_3673560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3673571 : List Nat := [1, 1, 1, 6, 2, 3, 1, 2, 2, 2, 2]
def baseStart_3673571 : Nat := 118140960795 + 3673571 * 2 ^ 59
def prefixEnd_3673571 : Nat := 4983230072969 + 3 ^ 40 * 3673571 * 2
def baseEnd_3673571 : Nat := 1886307641417951870268061

theorem tailTrace_3673571 : CollatzResearch.WordTrace tailWord_3673571 prefixEnd_3673571 1886307641417951870268061 := by
  unfold tailWord_3673571
  simp only [CollatzResearch.WordTrace]
  refine ⟨133986141774287137822364567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89324094516191425214909711 133986141774287137822364567)
  ·
    refine ⟨200979212661430706733546851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133986141774287137822364567 200979212661430706733546851)
    ·
      refine ⟨301468818992146060100320277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200979212661430706733546851 301468818992146060100320277)
      ·
        refine ⟨14131350890256846567202513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 301468818992146060100320277 14131350890256846567202513)
        ·
          refine ⟨10598513167692634925401885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14131350890256846567202513 10598513167692634925401885)
          ·
            refine ⟨3974442437884738097025707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10598513167692634925401885 3974442437884738097025707)
            ·
              refine ⟨5961663656827107145538561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3974442437884738097025707 5961663656827107145538561)
              ·
                refine ⟨4471247742620330359153921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5961663656827107145538561 4471247742620330359153921)
                ·
                  refine ⟨3353435806965247769365441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4471247742620330359153921 3353435806965247769365441)
                  ·
                    refine ⟨2515076855223935827024081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3353435806965247769365441 2515076855223935827024081)
                    ·
                      refine ⟨1886307641417951870268061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2515076855223935827024081 1886307641417951870268061)
                      ·
                        rfl

theorem cell23_3673571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 1, 2, 2, 2, 2].length) (baseStart_3673571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3673571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3673571 prefixEnd_3673571 := by exact prefixLift 3673571
  have htrace : WordTrace (prefixWord ++ tailWord_3673571) baseStart_3673571 baseEnd_3673571 := by
    simpa [prefixWord, tailWord_3673571, baseEnd_3673571] using wordTrace_append hprefix tailTrace_3673571
  have hstable : (prefixWord ++ tailWord_3673571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3673571).length < 2 ^ (prefixWord ++ tailWord_3673571).sum := by decide
  have hdescent : baseEnd_3673571 < baseStart_3673571 := by decide
  rcases family_descends (prefixWord ++ tailWord_3673571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3673580 : List Nat := [2, 2, 1, 1, 2, 1, 2, 3, 2, 5, 2]
def baseStart_3673580 : Nat := 118140960795 + 3673580 * 2 ^ 59
def prefixEnd_3673580 : Nat := 4983230072969 + 3 ^ 40 * 3673580 * 2
def baseEnd_3673580 : Nat := 1886312262743842335055519

theorem tailTrace_3673580 : CollatzResearch.WordTrace tailWord_3673580 prefixEnd_3673580 1886312262743842335055519 := by
  unfold tailWord_3673580
  simp only [CollatzResearch.WordTrace]
  refine ⟨66993235015627266179721097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89324313354169688239628129 66993235015627266179721097)
  ·
    refine ⟨50244926261720449634790823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66993235015627266179721097 50244926261720449634790823)
    ·
      refine ⟨75367389392580674452186235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50244926261720449634790823 75367389392580674452186235)
      ·
        refine ⟨113051084088871011678279353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75367389392580674452186235 113051084088871011678279353)
        ·
          refine ⟨84788313066653258758709515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113051084088871011678279353 84788313066653258758709515)
          ·
            refine ⟨127182469599979888138064273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84788313066653258758709515 127182469599979888138064273)
            ·
              refine ⟨95386852199984916103548205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127182469599979888138064273 95386852199984916103548205)
              ·
                refine ⟨35770069574994343538830577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95386852199984916103548205 35770069574994343538830577)
                ·
                  refine ⟨26827552181245757654122933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35770069574994343538830577 26827552181245757654122933)
                  ·
                    refine ⟨2515083016991789780074025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26827552181245757654122933 2515083016991789780074025)
                    ·
                      refine ⟨1886312262743842335055519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2515083016991789780074025 1886312262743842335055519)
                      ·
                        rfl

theorem cell23_3673580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 5, 2].length) (baseStart_3673580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3673580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3673580 prefixEnd_3673580 := by exact prefixLift 3673580
  have htrace : WordTrace (prefixWord ++ tailWord_3673580) baseStart_3673580 baseEnd_3673580 := by
    simpa [prefixWord, tailWord_3673580, baseEnd_3673580] using wordTrace_append hprefix tailTrace_3673580
  have hstable : (prefixWord ++ tailWord_3673580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3673580).length < 2 ^ (prefixWord ++ tailWord_3673580).sum := by decide
  have hdescent : baseEnd_3673580 < baseStart_3673580 := by decide
  rcases family_descends (prefixWord ++ tailWord_3673580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3673583 : List Nat := [1, 1, 2, 1, 4, 1, 2, 3, 1, 2, 5]
def baseStart_3673583 : Nat := 118140960795 + 3673583 * 2 ^ 59
def prefixEnd_3673583 : Nat := 4983230072969 + 3 ^ 40 * 3673583 * 2
def baseEnd_3673583 : Nat := 1886313803185805823318005

theorem tailTrace_3673583 : CollatzResearch.WordTrace tailWord_3673583 prefixEnd_3673583 1886313803185805823318005 := by
  unfold tailWord_3673583
  simp only [CollatzResearch.WordTrace]
  refine ⟨133986579450243663871801403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89324386300162442581200935 133986579450243663871801403)
  ·
    refine ⟨200979869175365495807702105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133986579450243663871801403 200979869175365495807702105)
    ·
      refine ⟨150734901881524121855776579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200979869175365495807702105 150734901881524121855776579)
      ·
        refine ⟨226102352822286182783664869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150734901881524121855776579 226102352822286182783664869)
        ·
          refine ⟨42394191154178659271937163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 226102352822286182783664869 42394191154178659271937163)
          ·
            refine ⟨63591286731267988907905745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42394191154178659271937163 63591286731267988907905745)
            ·
              refine ⟨47693465048450991680929309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63591286731267988907905745 47693465048450991680929309)
              ·
                refine ⟨17885049393169121880348491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47693465048450991680929309 17885049393169121880348491)
                ·
                  refine ⟨26827574089753682820522737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17885049393169121880348491 26827574089753682820522737)
                  ·
                    refine ⟨20120680567315262115392053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26827574089753682820522737 20120680567315262115392053)
                    ·
                      refine ⟨1886313803185805823318005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20120680567315262115392053 1886313803185805823318005)
                      ·
                        rfl

theorem cell23_3673583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 3, 1, 2, 5].length) (baseStart_3673583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3673583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3673583 prefixEnd_3673583 := by exact prefixLift 3673583
  have htrace : WordTrace (prefixWord ++ tailWord_3673583) baseStart_3673583 baseEnd_3673583 := by
    simpa [prefixWord, tailWord_3673583, baseEnd_3673583] using wordTrace_append hprefix tailTrace_3673583
  have hstable : (prefixWord ++ tailWord_3673583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3673583).length < 2 ^ (prefixWord ++ tailWord_3673583).sum := by decide
  have hdescent : baseEnd_3673583 < baseStart_3673583 := by decide
  rcases family_descends (prefixWord ++ tailWord_3673583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3673590 : List Nat := [5, 1, 1, 1, 2, 2, 1, 2, 1, 7]
def baseStart_3673590 : Nat := 118140960795 + 3673590 * 2 ^ 59
def prefixEnd_3673590 : Nat := 4983230072969 + 3 ^ 40 * 3673590 * 2
def baseEnd_3673590 : Nat := 628772465850129098643491

theorem tailTrace_3673590 : CollatzResearch.WordTrace tailWord_3673590 prefixEnd_3673590 628772465850129098643491 := by
  unfold tailWord_3673590
  simp only [CollatzResearch.WordTrace]
  refine ⟨8374177172576144004206639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 89324556507478869378204149 8374177172576144004206639)
  ·
    refine ⟨12561265758864216006309959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8374177172576144004206639 12561265758864216006309959)
    ·
      refine ⟨18841898638296324009464939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12561265758864216006309959 18841898638296324009464939)
      ·
        refine ⟨28262847957444486014197409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18841898638296324009464939 28262847957444486014197409)
        ·
          refine ⟨21197135968083364510648057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28262847957444486014197409 21197135968083364510648057)
          ·
            refine ⟨15897851976062523382986043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21197135968083364510648057 15897851976062523382986043)
            ·
              refine ⟨23846777964093785074479065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15897851976062523382986043 23846777964093785074479065)
              ·
                refine ⟨17885083473070338805859299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23846777964093785074479065 17885083473070338805859299)
                ·
                  refine ⟨26827625209605508208788949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17885083473070338805859299 26827625209605508208788949)
                  ·
                    refine ⟨628772465850129098643491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26827625209605508208788949 628772465850129098643491)
                    ·
                      rfl

theorem cell23_3673590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 2, 1, 7].length) (baseStart_3673590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3673590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3673590 prefixEnd_3673590 := by exact prefixLift 3673590
  have htrace : WordTrace (prefixWord ++ tailWord_3673590) baseStart_3673590 baseEnd_3673590 := by
    simpa [prefixWord, tailWord_3673590, baseEnd_3673590] using wordTrace_append hprefix tailTrace_3673590
  have hstable : (prefixWord ++ tailWord_3673590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3673590).length < 2 ^ (prefixWord ++ tailWord_3673590).sum := by decide
  have hdescent : baseEnd_3673590 < baseStart_3673590 := by decide
  rcases family_descends (prefixWord ++ tailWord_3673590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3673610 : List Nat := [3, 1, 2, 2, 2, 2, 2, 1, 1, 3, 4]
def baseStart_3673610 : Nat := 118140960795 + 3673610 * 2 ^ 59
def prefixEnd_3673610 : Nat := 4983230072969 + 3 ^ 40 * 3673610 * 2
def baseEnd_3673610 : Nat := 1886327667163477217680381

theorem tailTrace_3673610 : CollatzResearch.WordTrace tailWord_3673610 prefixEnd_3673610 1886327667163477217680381 := by
  unfold tailWord_3673610
  simp only [CollatzResearch.WordTrace]
  refine ⟨33496891055286461870758571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89325042814097231655356189 33496891055286461870758571)
  ·
    refine ⟨50245336582929692806137857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33496891055286461870758571 50245336582929692806137857)
    ·
      refine ⟨37684002437197269604603393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50245336582929692806137857 37684002437197269604603393)
      ·
        refine ⟨28263001827897952203452545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37684002437197269604603393 28263001827897952203452545)
        ·
          refine ⟨21197251370923464152589409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28263001827897952203452545 21197251370923464152589409)
          ·
            refine ⟨15897938528192598114442057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21197251370923464152589409 15897938528192598114442057)
            ·
              refine ⟨11923453896144448585831543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15897938528192598114442057 11923453896144448585831543)
              ·
                refine ⟨17885180844216672878747315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11923453896144448585831543 17885180844216672878747315)
                ·
                  refine ⟨26827771266325009318120973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17885180844216672878747315 26827771266325009318120973)
                  ·
                    refine ⟨10060414224871878494295365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26827771266325009318120973 10060414224871878494295365)
                    ·
                      refine ⟨1886327667163477217680381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10060414224871878494295365 1886327667163477217680381)
                      ·
                        rfl

theorem cell23_3673610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 1, 1, 3, 4].length) (baseStart_3673610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3673610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3673610 prefixEnd_3673610 := by exact prefixLift 3673610
  have htrace : WordTrace (prefixWord ++ tailWord_3673610) baseStart_3673610 baseEnd_3673610 := by
    simpa [prefixWord, tailWord_3673610, baseEnd_3673610] using wordTrace_append hprefix tailTrace_3673610
  have hstable : (prefixWord ++ tailWord_3673610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3673610).length < 2 ^ (prefixWord ++ tailWord_3673610).sum := by decide
  have hdescent : baseEnd_3673610 < baseStart_3673610 := by decide
  rcases family_descends (prefixWord ++ tailWord_3673610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3673673 : List Nat := [1, 2, 1, 1, 2, 2, 1, 2, 1, 3, 7]
def baseStart_3673673 : Nat := 118140960795 + 3673673 * 2 ^ 59
def prefixEnd_3673673 : Nat := 4983230072969 + 3 ^ 40 * 3673673 * 2
def baseEnd_3673673 : Nat := 1886360016444710471192591

theorem tailTrace_3673673 : CollatzResearch.WordTrace tailWord_3673673 prefixEnd_3673673 1886360016444710471192591 := by
  unfold tailWord_3673673
  simp only [CollatzResearch.WordTrace]
  refine ⟨133989862019917609242577673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89326574679945072828385115 133989862019917609242577673)
  ·
    refine ⟨100492396514938206931933255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133989862019917609242577673 100492396514938206931933255)
    ·
      refine ⟨150738594772407310397899883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100492396514938206931933255 150738594772407310397899883)
      ·
        refine ⟨226107892158610965596849825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150738594772407310397899883 226107892158610965596849825)
        ·
          refine ⟨169580919118958224197637369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226107892158610965596849825 169580919118958224197637369)
          ·
            refine ⟨127185689339218668148228027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169580919118958224197637369 127185689339218668148228027)
            ·
              refine ⟨190778534008828002222342041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127185689339218668148228027 190778534008828002222342041)
              ·
                refine ⟨143083900506621001666756531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 190778534008828002222342041 143083900506621001666756531)
                ·
                  refine ⟨214625850759931502500134797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 143083900506621001666756531 214625850759931502500134797)
                  ·
                    refine ⟨80484694034974313437550549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 214625850759931502500134797 80484694034974313437550549)
                    ·
                      refine ⟨1886360016444710471192591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 80484694034974313437550549 1886360016444710471192591)
                      ·
                        rfl

theorem cell23_3673673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 3, 7].length) (baseStart_3673673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3673673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3673673 prefixEnd_3673673 := by exact prefixLift 3673673
  have htrace : WordTrace (prefixWord ++ tailWord_3673673) baseStart_3673673 baseEnd_3673673 := by
    simpa [prefixWord, tailWord_3673673, baseEnd_3673673] using wordTrace_append hprefix tailTrace_3673673
  have hstable : (prefixWord ++ tailWord_3673673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3673673).length < 2 ^ (prefixWord ++ tailWord_3673673).sum := by decide
  have hdescent : baseEnd_3673673 < baseStart_3673673 := by decide
  rcases family_descends (prefixWord ++ tailWord_3673673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3673751 : List Nat := [1, 1, 3, 3, 2, 3, 2, 1, 3, 2, 2]
def baseStart_3673751 : Nat := 118140960795 + 3673751 * 2 ^ 59
def prefixEnd_3673751 : Nat := 4983230072969 + 3 ^ 40 * 3673751 * 2
def baseEnd_3673751 : Nat := 1886400067935761166017233

theorem tailTrace_3673751 : CollatzResearch.WordTrace tailWord_3673751 prefixEnd_3673751 1886400067935761166017233 := by
  unfold tailWord_3673751
  simp only [CollatzResearch.WordTrace]
  refine ⟨133992706913635028563917107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89328471275756685709278071 133992706913635028563917107)
  ·
    refine ⟨200989060370452542845875661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133992706913635028563917107 200989060370452542845875661)
    ·
      refine ⟨75370897638919703567203373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 200989060370452542845875661 75370897638919703567203373)
      ·
        refine ⟨28264086614594888837701265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75370897638919703567203373 28264086614594888837701265)
        ·
          refine ⟨21198064960946166628275949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28264086614594888837701265 21198064960946166628275949)
          ·
            refine ⟨7949274360354812485603481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21198064960946166628275949 7949274360354812485603481)
            ·
              refine ⟨5961955770266109364202611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7949274360354812485603481 5961955770266109364202611)
              ·
                refine ⟨8942933655399164046303917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5961955770266109364202611 8942933655399164046303917)
                ·
                  refine ⟨3353600120774686517363969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8942933655399164046303917 3353600120774686517363969)
                  ·
                    refine ⟨2515200090581014888022977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3353600120774686517363969 2515200090581014888022977)
                    ·
                      refine ⟨1886400067935761166017233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2515200090581014888022977 1886400067935761166017233)
                      ·
                        rfl

theorem cell23_3673751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 2, 1, 3, 2, 2].length) (baseStart_3673751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3673751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3673751 prefixEnd_3673751 := by exact prefixLift 3673751
  have htrace : WordTrace (prefixWord ++ tailWord_3673751) baseStart_3673751 baseEnd_3673751 := by
    simpa [prefixWord, tailWord_3673751, baseEnd_3673751] using wordTrace_append hprefix tailTrace_3673751
  have hstable : (prefixWord ++ tailWord_3673751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3673751).length < 2 ^ (prefixWord ++ tailWord_3673751).sum := by decide
  have hdescent : baseEnd_3673751 < baseStart_3673751 := by decide
  rcases family_descends (prefixWord ++ tailWord_3673751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3673761 : List Nat := [1, 2, 3, 3, 2, 2, 3, 1, 2, 4]
def baseStart_3673761 : Nat := 118140960795 + 3673761 * 2 ^ 59
def prefixEnd_3673761 : Nat := 4983230072969 + 3 ^ 40 * 3673761 * 2
def baseEnd_3673761 : Nat := 628801734247435375630729

theorem tailTrace_3673761 : CollatzResearch.WordTrace tailWord_3673761 prefixEnd_3673761 628801734247435375630729 := by
  unfold tailWord_3673761
  simp only [CollatzResearch.WordTrace]
  refine ⟨133993071643598800271781137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89328714429065866847854091 133993071643598800271781137)
  ·
    refine ⟨100494803732699100203835853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133993071643598800271781137 100494803732699100203835853)
    ·
      refine ⟨37685551399762162576438445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100494803732699100203835853 37685551399762162576438445)
      ·
        refine ⟨14132081774910810966164417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37685551399762162576438445 14132081774910810966164417)
        ·
          refine ⟨10599061331183108224623313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14132081774910810966164417 10599061331183108224623313)
          ·
            refine ⟨7949295998387331168467485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10599061331183108224623313 7949295998387331168467485)
            ·
              refine ⟨2980985999395249188175307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7949295998387331168467485 2980985999395249188175307)
              ·
                refine ⟨4471478999092873782262961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2980985999395249188175307 4471478999092873782262961)
                ·
                  refine ⟨3353609249319655336697221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4471478999092873782262961 3353609249319655336697221)
                  ·
                    refine ⟨628801734247435375630729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3353609249319655336697221 628801734247435375630729)
                    ·
                      rfl

theorem cell23_3673761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 3, 1, 2, 4].length) (baseStart_3673761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3673761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3673761 prefixEnd_3673761 := by exact prefixLift 3673761
  have htrace : WordTrace (prefixWord ++ tailWord_3673761) baseStart_3673761 baseEnd_3673761 := by
    simpa [prefixWord, tailWord_3673761, baseEnd_3673761] using wordTrace_append hprefix tailTrace_3673761
  have hstable : (prefixWord ++ tailWord_3673761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3673761).length < 2 ^ (prefixWord ++ tailWord_3673761).sum := by decide
  have hdescent : baseEnd_3673761 < baseStart_3673761 := by decide
  rcases family_descends (prefixWord ++ tailWord_3673761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3673764 : List Nat := [2, 3, 1, 2, 2, 4, 1, 1, 1, 2, 4]
def baseStart_3673764 : Nat := 118140960795 + 3673764 * 2 ^ 59
def prefixEnd_3673764 : Nat := 4983230072969 + 3 ^ 40 * 3673764 * 2
def baseEnd_3673764 : Nat := 1886406743184269615154673

theorem tailTrace_3673764 : CollatzResearch.WordTrace tailWord_3673764 prefixEnd_3673764 1886406743184269615154673 := by
  unfold tailWord_3673764
  simp only [CollatzResearch.WordTrace]
  refine ⟨66996590531293965892070173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89328787375058621189426897 66996590531293965892070173)
  ·
    refine ⟨25123721449235237209526315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66996590531293965892070173 25123721449235237209526315)
    ·
      refine ⟨37685582173852855814289473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25123721449235237209526315 37685582173852855814289473)
      ·
        refine ⟨28264186630389641860717105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37685582173852855814289473 28264186630389641860717105)
        ·
          refine ⟨21198139972792231395537829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28264186630389641860717105 21198139972792231395537829)
          ·
            refine ⟨3974651244898543386663343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21198139972792231395537829 3974651244898543386663343)
            ·
              refine ⟨5961976867347815079995015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3974651244898543386663343 5961976867347815079995015)
              ·
                refine ⟨8942965301021722619992523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5961976867347815079995015 8942965301021722619992523)
                ·
                  refine ⟨13414447951532583929988785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8942965301021722619992523 13414447951532583929988785)
                  ·
                    refine ⟨10060835963649437947491589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13414447951532583929988785 10060835963649437947491589)
                    ·
                      refine ⟨1886406743184269615154673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10060835963649437947491589 1886406743184269615154673)
                      ·
                        rfl

theorem cell23_3673764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 1, 1, 1, 2, 4].length) (baseStart_3673764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3673764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3673764 prefixEnd_3673764 := by exact prefixLift 3673764
  have htrace : WordTrace (prefixWord ++ tailWord_3673764) baseStart_3673764 baseEnd_3673764 := by
    simpa [prefixWord, tailWord_3673764, baseEnd_3673764] using wordTrace_append hprefix tailTrace_3673764
  have hstable : (prefixWord ++ tailWord_3673764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3673764).length < 2 ^ (prefixWord ++ tailWord_3673764).sum := by decide
  have hdescent : baseEnd_3673764 < baseStart_3673764 := by decide
  rcases family_descends (prefixWord ++ tailWord_3673764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3673774 : List Nat := [4, 1, 4, 1, 2, 1, 1, 9]
def baseStart_3673774 : Nat := 118140960795 + 3673774 * 2 ^ 59
def prefixEnd_3673774 : Nat := 4983230072969 + 3 ^ 40 * 3673774 * 2
def baseEnd_3673774 : Nat := 69867106592252391704801

theorem tailTrace_3673774 : CollatzResearch.WordTrace tailWord_3673774 prefixEnd_3673774 69867106592252391704801 := by
  unfold tailWord_3673774
  simp only [CollatzResearch.WordTrace]
  refine ⟨16749193224068962936500547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89329030528367802328002917 16749193224068962936500547)
  ·
    refine ⟨25123789836103444404750821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16749193224068962936500547 25123789836103444404750821)
    ·
      refine ⟨4710710594269395825890779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25123789836103444404750821 4710710594269395825890779)
      ·
        refine ⟨7066065891404093738836169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4710710594269395825890779 7066065891404093738836169)
        ·
          refine ⟨5299549418553070304127127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7066065891404093738836169 5299549418553070304127127)
          ·
            refine ⟨7949324127829605456190691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5299549418553070304127127 7949324127829605456190691)
            ·
              refine ⟨11923986191744408184286037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7949324127829605456190691 11923986191744408184286037)
              ·
                refine ⟨69867106592252391704801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11923986191744408184286037 69867106592252391704801)
                ·
                  rfl

theorem cell23_3673774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 9].length) (baseStart_3673774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3673774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3673774 prefixEnd_3673774 := by exact prefixLift 3673774
  have htrace : WordTrace (prefixWord ++ tailWord_3673774) baseStart_3673774 baseEnd_3673774 := by
    simpa [prefixWord, tailWord_3673774, baseEnd_3673774] using wordTrace_append hprefix tailTrace_3673774
  have hstable : (prefixWord ++ tailWord_3673774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3673774).length < 2 ^ (prefixWord ++ tailWord_3673774).sum := by decide
  have hdescent : baseEnd_3673774 < baseStart_3673774 := by decide
  rcases family_descends (prefixWord ++ tailWord_3673774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3673818 : List Nat := [3, 1, 1, 2, 2, 5, 2, 1, 2, 1, 3]
def baseStart_3673818 : Nat := 118140960795 + 3673818 * 2 ^ 59
def prefixEnd_3673818 : Nat := 4983230072969 + 3 ^ 40 * 3673818 * 2
def baseEnd_3673818 : Nat := 1886434471139612403879425

theorem tailTrace_3673818 : CollatzResearch.WordTrace tailWord_3673818 prefixEnd_3673818 1886434471139612403879425 := by
  unfold tailWord_3673818
  simp only [CollatzResearch.WordTrace]
  refine ⟨33498787651098074751651527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89330100402928199337737405 33498787651098074751651527)
  ·
    refine ⟨50248181476647112127477291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33498787651098074751651527 50248181476647112127477291)
    ·
      refine ⟨75372272214970668191215937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50248181476647112127477291 75372272214970668191215937)
      ·
        refine ⟨56529204161228001143411953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75372272214970668191215937 56529204161228001143411953)
        ·
          refine ⟨42396903120921000857558965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56529204161228001143411953 42396903120921000857558965)
          ·
            refine ⟨3974709667586343830396153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42396903120921000857558965 3974709667586343830396153)
            ·
              refine ⟨2981032250689757872797115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3974709667586343830396153 2981032250689757872797115)
              ·
                refine ⟨4471548376034636809195673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2981032250689757872797115 4471548376034636809195673)
                ·
                  refine ⟨3353661282025977606896755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4471548376034636809195673 3353661282025977606896755)
                  ·
                    refine ⟨5030491923038966410345133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3353661282025977606896755 5030491923038966410345133)
                    ·
                      refine ⟨1886434471139612403879425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5030491923038966410345133 1886434471139612403879425)
                      ·
                        rfl

theorem cell23_3673818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 2, 1, 2, 1, 3].length) (baseStart_3673818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3673818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3673818 prefixEnd_3673818 := by exact prefixLift 3673818
  have htrace : WordTrace (prefixWord ++ tailWord_3673818) baseStart_3673818 baseEnd_3673818 := by
    simpa [prefixWord, tailWord_3673818, baseEnd_3673818] using wordTrace_append hprefix tailTrace_3673818
  have hstable : (prefixWord ++ tailWord_3673818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3673818).length < 2 ^ (prefixWord ++ tailWord_3673818).sum := by decide
  have hdescent : baseEnd_3673818 < baseStart_3673818 := by decide
  rcases family_descends (prefixWord ++ tailWord_3673818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3673840 : List Nat := [2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 7]
def baseStart_3673840 : Nat := 118140960795 + 3673840 * 2 ^ 59
def prefixEnd_3673840 : Nat := 4983230072969 + 3 ^ 40 * 3673840 * 2
def baseEnd_3673840 : Nat := 1886445767714011317804323

theorem tailTrace_3673840 : CollatzResearch.WordTrace tailWord_3673840 prefixEnd_3673840 1886445767714011317804323 := by
  unfold tailWord_3673840
  simp only [CollatzResearch.WordTrace]
  refine ⟨66997976505156298381953487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89330635340208397842604649 66997976505156298381953487)
  ·
    refine ⟨100496964757734447572930231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66997976505156298381953487 100496964757734447572930231)
    ·
      refine ⟨150745447136601671359395347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100496964757734447572930231 150745447136601671359395347)
      ·
        refine ⟨226118170704902507039093021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150745447136601671359395347 226118170704902507039093021)
        ·
          refine ⟨84794314014338440139659883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 226118170704902507039093021 84794314014338440139659883)
          ·
            refine ⟨127191471021507660209489825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84794314014338440139659883 127191471021507660209489825)
            ·
              refine ⟨95393603266130745157117369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127191471021507660209489825 95393603266130745157117369)
              ·
                refine ⟨71545202449598058867838027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95393603266130745157117369 71545202449598058867838027)
                ·
                  refine ⟨107317803674397088301757041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71545202449598058867838027 107317803674397088301757041)
                  ·
                    refine ⟨80488352755797816226317781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 107317803674397088301757041 80488352755797816226317781)
                    ·
                      refine ⟨1886445767714011317804323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 80488352755797816226317781 1886445767714011317804323)
                      ·
                        rfl

theorem cell23_3673840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 7].length) (baseStart_3673840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3673840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3673840 prefixEnd_3673840 := by exact prefixLift 3673840
  have htrace : WordTrace (prefixWord ++ tailWord_3673840) baseStart_3673840 baseEnd_3673840 := by
    simpa [prefixWord, tailWord_3673840, baseEnd_3673840] using wordTrace_append hprefix tailTrace_3673840
  have hstable : (prefixWord ++ tailWord_3673840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3673840).length < 2 ^ (prefixWord ++ tailWord_3673840).sum := by decide
  have hdescent : baseEnd_3673840 < baseStart_3673840 := by decide
  rcases family_descends (prefixWord ++ tailWord_3673840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3673864 : List Nat := [2, 1, 3, 2, 2, 1, 3, 4, 5]
def baseStart_3673864 : Nat := 118140960795 + 3673864 * 2 ^ 59
def prefixEnd_3673864 : Nat := 4983230072969 + 3 ^ 40 * 3673864 * 2
def baseEnd_3673864 : Nat := 209606454583302135989357

theorem tailTrace_3673864 : CollatzResearch.WordTrace tailWord_3673864 prefixEnd_3673864 209606454583302135989357 := by
  unfold tailWord_3673864
  simp only [CollatzResearch.WordTrace]
  refine ⟨66998414181112824431390323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89331218908150432575187097 66998414181112824431390323)
  ·
    refine ⟨100497621271669236647085485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66998414181112824431390323 100497621271669236647085485)
    ·
      refine ⟨37686607976875963742657057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100497621271669236647085485 37686607976875963742657057)
      ·
        refine ⟨28264955982656972806992793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37686607976875963742657057 28264955982656972806992793)
        ·
          refine ⟨21198716986992729605244595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28264955982656972806992793 21198716986992729605244595)
          ·
            refine ⟨31798075480489094407866893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21198716986992729605244595 31798075480489094407866893)
            ·
              refine ⟨11924278305183410402950085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31798075480489094407866893 11924278305183410402950085)
              ·
                refine ⟨2235802182221889450553141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11924278305183410402950085 2235802182221889450553141)
                ·
                  refine ⟨209606454583302135989357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2235802182221889450553141 209606454583302135989357)
                  ·
                    rfl

theorem cell23_3673864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 4, 5].length) (baseStart_3673864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3673864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3673864 prefixEnd_3673864 := by exact prefixLift 3673864
  have htrace : WordTrace (prefixWord ++ tailWord_3673864) baseStart_3673864 baseEnd_3673864 := by
    simpa [prefixWord, tailWord_3673864, baseEnd_3673864] using wordTrace_append hprefix tailTrace_3673864
  have hstable : (prefixWord ++ tailWord_3673864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3673864).length < 2 ^ (prefixWord ++ tailWord_3673864).sum := by decide
  have hdescent : baseEnd_3673864 < baseStart_3673864 := by decide
  rcases family_descends (prefixWord ++ tailWord_3673864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3673884 : List Nat := [2, 2, 3, 1, 1, 2, 1, 2, 2, 5, 2]
def baseStart_3673884 : Nat := 118140960795 + 3673884 * 2 ^ 59
def prefixEnd_3673884 : Nat := 4983230072969 + 3 ^ 40 * 3673884 * 2
def baseEnd_3673884 : Nat := 1886468360862809145654121

theorem tailTrace_3673884 : CollatzResearch.WordTrace tailWord_3673884 prefixEnd_3673884 1886468360862809145654121 := by
  unfold tailWord_3673884
  simp only [CollatzResearch.WordTrace]
  refine ⟨66998778911076596139254353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89331705214768794852339137 66998778911076596139254353)
  ·
    refine ⟨50249084183307447104440765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66998778911076596139254353 50249084183307447104440765)
    ·
      refine ⟨18843406568740292664165287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50249084183307447104440765 18843406568740292664165287)
      ·
        refine ⟨28265109853110438996247931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18843406568740292664165287 28265109853110438996247931)
        ·
          refine ⟨42397664779665658494371897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28265109853110438996247931 42397664779665658494371897)
          ·
            refine ⟨31798248584749243870778923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42397664779665658494371897 31798248584749243870778923)
            ·
              refine ⟨47697372877123865806168385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31798248584749243870778923 47697372877123865806168385)
              ·
                refine ⟨35773029657842899354626289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47697372877123865806168385 35773029657842899354626289)
                ·
                  refine ⟨26829772243382174515969717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35773029657842899354626289 26829772243382174515969717)
                  ·
                    refine ⟨2515291147817078860872161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26829772243382174515969717 2515291147817078860872161)
                    ·
                      refine ⟨1886468360862809145654121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2515291147817078860872161 1886468360862809145654121)
                      ·
                        rfl

theorem cell23_3673884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 2, 2, 5, 2].length) (baseStart_3673884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3673884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3673884 prefixEnd_3673884 := by exact prefixLift 3673884
  have htrace : WordTrace (prefixWord ++ tailWord_3673884) baseStart_3673884 baseEnd_3673884 := by
    simpa [prefixWord, tailWord_3673884, baseEnd_3673884] using wordTrace_append hprefix tailTrace_3673884
  have hstable : (prefixWord ++ tailWord_3673884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3673884).length < 2 ^ (prefixWord ++ tailWord_3673884).sum := by decide
  have hdescent : baseEnd_3673884 < baseStart_3673884 := by decide
  rcases family_descends (prefixWord ++ tailWord_3673884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3673954 : List Nat := [3, 3, 2, 1, 2, 1, 1, 2, 8]
def baseStart_3673954 : Nat := 118140960795 + 3673954 * 2 ^ 59
def prefixEnd_3673954 : Nat := 4983230072969 + 3 ^ 40 * 3673954 * 2
def baseEnd_3673954 : Nat := 209611589389847096864311

theorem tailTrace_3673954 : CollatzResearch.WordTrace tailWord_3673954 prefixEnd_3673954 209611589389847096864311 := by
  unfold tailWord_3673954
  simp only [CollatzResearch.WordTrace]
  refine ⟨33500027732974898558389229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89333407287933062822371277 33500027732974898558389229)
  ·
    refine ⟨12562510399865586959395961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33500027732974898558389229 12562510399865586959395961)
    ·
      refine ⟨9421882799899190219546971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12562510399865586959395961 9421882799899190219546971)
      ·
        refine ⟨14132824199848785329320457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9421882799899190219546971 14132824199848785329320457)
        ·
          refine ⟨10599618149886588996990343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14132824199848785329320457 10599618149886588996990343)
          ·
            refine ⟨15899427224829883495485515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10599618149886588996990343 15899427224829883495485515)
            ·
              refine ⟨23849140837244825243228273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15899427224829883495485515 23849140837244825243228273)
              ·
                refine ⟨17886855627933618932421205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23849140837244825243228273 17886855627933618932421205)
                ·
                  refine ⟨209611589389847096864311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17886855627933618932421205 209611589389847096864311)
                  ·
                    rfl

theorem cell23_3673954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 2, 8].length) (baseStart_3673954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3673954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3673954 prefixEnd_3673954 := by exact prefixLift 3673954
  have htrace : WordTrace (prefixWord ++ tailWord_3673954) baseStart_3673954 baseEnd_3673954 := by
    simpa [prefixWord, tailWord_3673954, baseEnd_3673954] using wordTrace_append hprefix tailTrace_3673954
  have hstable : (prefixWord ++ tailWord_3673954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3673954).length < 2 ^ (prefixWord ++ tailWord_3673954).sum := by decide
  have hdescent : baseEnd_3673954 < baseStart_3673954 := by decide
  rcases family_descends (prefixWord ++ tailWord_3673954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3673967 : List Nat := [1, 1, 2, 1, 3, 1, 1, 1, 7, 5]
def baseStart_3673967 : Nat := 118140960795 + 3673967 * 2 ^ 59
def prefixEnd_3673967 : Nat := 4983230072969 + 3 ^ 40 * 3673967 * 2
def baseEnd_3673967 : Nat := 628836993252377440305413

theorem tailTrace_3673967 : CollatzResearch.WordTrace tailWord_3673967 prefixEnd_3673967 628836993252377440305413 := by
  unfold tailWord_3673967
  simp only [CollatzResearch.WordTrace]
  refine ⟨134000585080852497453780155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89333723387234998302520103 134000585080852497453780155)
  ·
    refine ⟨201000877621278746180670233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134000585080852497453780155 201000877621278746180670233)
    ·
      refine ⟨150750658215959059635502675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201000877621278746180670233 150750658215959059635502675)
      ·
        refine ⟨226125987323938589453254013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150750658215959059635502675 226125987323938589453254013)
        ·
          refine ⟨84797245246476971044970255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 226125987323938589453254013 84797245246476971044970255)
          ·
            refine ⟨127195867869715456567455383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84797245246476971044970255 127195867869715456567455383)
            ·
              refine ⟨190793801804573184851183075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127195867869715456567455383 190793801804573184851183075)
              ·
                refine ⟨286190702706859777276774613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 190793801804573184851183075 286190702706859777276774613)
                ·
                  refine ⟨6707594594692026029924405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 286190702706859777276774613 6707594594692026029924405)
                  ·
                    refine ⟨628836993252377440305413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6707594594692026029924405 628836993252377440305413)
                    ·
                      rfl

theorem cell23_3673967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 7, 5].length) (baseStart_3673967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3673967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3673967 prefixEnd_3673967 := by exact prefixLift 3673967
  have htrace : WordTrace (prefixWord ++ tailWord_3673967) baseStart_3673967 baseEnd_3673967 := by
    simpa [prefixWord, tailWord_3673967, baseEnd_3673967] using wordTrace_append hprefix tailTrace_3673967
  have hstable : (prefixWord ++ tailWord_3673967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3673967).length < 2 ^ (prefixWord ++ tailWord_3673967).sum := by decide
  have hdescent : baseEnd_3673967 < baseStart_3673967 := by decide
  rcases family_descends (prefixWord ++ tailWord_3673967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3674031 : List Nat := [1, 1, 2, 1, 2, 2, 6, 2, 2, 4]
def baseStart_3674031 : Nat := 118140960795 + 3674031 * 2 ^ 59
def prefixEnd_3674031 : Nat := 4983230072969 + 3 ^ 40 * 3674031 * 2
def baseEnd_3674031 : Nat := 628847947506340023505315

theorem tailTrace_3674031 : CollatzResearch.WordTrace tailWord_3674031 prefixEnd_3674031 628847947506340023505315 := by
  unfold tailWord_3674031
  simp only [CollatzResearch.WordTrace]
  refine ⟨134002919352620636384109947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89335279568413757589406631 134002919352620636384109947)
  ·
    refine ⟨201004379028930954576164921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134002919352620636384109947 201004379028930954576164921)
    ·
      refine ⟨150753284271698215932123691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201004379028930954576164921 150753284271698215932123691)
      ·
        refine ⟨226129926407547323898185537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150753284271698215932123691 226129926407547323898185537)
        ·
          refine ⟨169597444805660492923639153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226129926407547323898185537 169597444805660492923639153)
          ·
            refine ⟨127198083604245369692729365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169597444805660492923639153 127198083604245369692729365)
            ·
              refine ⟨5962410168949001704346689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 127198083604245369692729365 5962410168949001704346689)
              ·
                refine ⟨4471807626711751278260017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5962410168949001704346689 4471807626711751278260017)
                ·
                  refine ⟨3353855720033813458695013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4471807626711751278260017 3353855720033813458695013)
                  ·
                    refine ⟨628847947506340023505315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3353855720033813458695013 628847947506340023505315)
                    ·
                      rfl

theorem cell23_3674031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 6, 2, 2, 4].length) (baseStart_3674031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3674031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3674031 prefixEnd_3674031 := by exact prefixLift 3674031
  have htrace : WordTrace (prefixWord ++ tailWord_3674031) baseStart_3674031 baseEnd_3674031 := by
    simpa [prefixWord, tailWord_3674031, baseEnd_3674031] using wordTrace_append hprefix tailTrace_3674031
  have hstable : (prefixWord ++ tailWord_3674031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3674031).length < 2 ^ (prefixWord ++ tailWord_3674031).sum := by decide
  have hdescent : baseEnd_3674031 < baseStart_3674031 := by decide
  rcases family_descends (prefixWord ++ tailWord_3674031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3674067 : List Nat := [1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 11]
def baseStart_3674067 : Nat := 118140960795 + 3674067 * 2 ^ 59
def prefixEnd_3674067 : Nat := 4983230072969 + 3 ^ 40 * 3674067 * 2
def baseEnd_3674067 : Nat := 1886562327822581929665779

theorem tailTrace_3674067 : CollatzResearch.WordTrace tailWord_3674067 prefixEnd_3674067 1886562327822581929665779 := by
  unfold tailWord_3674067
  simp only [CollatzResearch.WordTrace]
  refine ⟨134004232380490214532420455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89336154920326809688280303 134004232380490214532420455)
  ·
    refine ⟨201006348570735321798630683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134004232380490214532420455 201006348570735321798630683)
    ·
      refine ⟨301509522856102982697946025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201006348570735321798630683 301509522856102982697946025)
      ·
        refine ⟨226132142142077237023459519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 301509522856102982697946025 226132142142077237023459519)
        ·
          refine ⟨339198213213115855535189279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226132142142077237023459519 339198213213115855535189279)
          ·
            refine ⟨508797319819673783302783919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 339198213213115855535189279 508797319819673783302783919)
            ·
              refine ⟨763195979729510674954175879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 508797319819673783302783919 763195979729510674954175879)
              ·
                refine ⟨1144793969594266012431263819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 763195979729510674954175879 1144793969594266012431263819)
                ·
                  refine ⟨1717190954391399018646895729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1144793969594266012431263819 1717190954391399018646895729)
                  ·
                    refine ⟨1287893215793549263985171797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1717190954391399018646895729 1287893215793549263985171797)
                    ·
                      refine ⟨1886562327822581929665779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 11 1287893215793549263985171797 1886562327822581929665779)
                      ·
                        rfl

theorem cell23_3674067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 11].length) (baseStart_3674067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3674067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3674067 prefixEnd_3674067 := by exact prefixLift 3674067
  have htrace : WordTrace (prefixWord ++ tailWord_3674067) baseStart_3674067 baseEnd_3674067 := by
    simpa [prefixWord, tailWord_3674067, baseEnd_3674067] using wordTrace_append hprefix tailTrace_3674067
  have hstable : (prefixWord ++ tailWord_3674067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3674067).length < 2 ^ (prefixWord ++ tailWord_3674067).sum := by decide
  have hdescent : baseEnd_3674067 < baseStart_3674067 := by decide
  rcases family_descends (prefixWord ++ tailWord_3674067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3674071 : List Nat := [1, 1, 3, 2, 1, 1, 4, 2, 4, 1, 3]
def baseStart_3674071 : Nat := 118140960795 + 3674071 * 2 ^ 59
def prefixEnd_3674071 : Nat := 4983230072969 + 3 ^ 40 * 3674071 * 2
def baseEnd_3674071 : Nat := 1886564381745199914015761

theorem tailTrace_3674071 : CollatzResearch.WordTrace tailWord_3674071 prefixEnd_3674071 1886564381745199914015761 := by
  unfold tailWord_3674071
  simp only [CollatzResearch.WordTrace]
  refine ⟨134004378272475723215566067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89336252181650482143710711 134004378272475723215566067)
  ·
    refine ⟨201006567408713584823349101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134004378272475723215566067 201006567408713584823349101)
    ·
      refine ⟨75377462778267594308755913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201006567408713584823349101 75377462778267594308755913)
      ·
        refine ⟨56533097083700695731566935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75377462778267594308755913 56533097083700695731566935)
        ·
          refine ⟨84799645625551043597350403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56533097083700695731566935 84799645625551043597350403)
          ·
            refine ⟨127199468438326565396025605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84799645625551043597350403 127199468438326565396025605)
            ·
              refine ⟨23849900332186231011754801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 127199468438326565396025605 23849900332186231011754801)
              ·
                refine ⟨17887425249139673258816101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23849900332186231011754801 17887425249139673258816101)
                ·
                  refine ⟨3353892234213688736028019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17887425249139673258816101 3353892234213688736028019)
                  ·
                    refine ⟨5030838351320533104042029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3353892234213688736028019 5030838351320533104042029)
                    ·
                      refine ⟨1886564381745199914015761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5030838351320533104042029 1886564381745199914015761)
                      ·
                        rfl

theorem cell23_3674071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 2, 4, 1, 3].length) (baseStart_3674071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3674071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3674071 prefixEnd_3674071 := by exact prefixLift 3674071
  have htrace : WordTrace (prefixWord ++ tailWord_3674071) baseStart_3674071 baseEnd_3674071 := by
    simpa [prefixWord, tailWord_3674071, baseEnd_3674071] using wordTrace_append hprefix tailTrace_3674071
  have hstable : (prefixWord ++ tailWord_3674071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3674071).length < 2 ^ (prefixWord ++ tailWord_3674071).sum := by decide
  have hdescent : baseEnd_3674071 < baseStart_3674071 := by decide
  rcases family_descends (prefixWord ++ tailWord_3674071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3674082 : List Nat := [3, 3, 3, 1, 2, 2, 1, 2, 2, 4]
def baseStart_3674082 : Nat := 118140960795 + 3674082 * 2 ^ 59
def prefixEnd_3674082 : Nat := 4983230072969 + 3 ^ 40 * 3674082 * 2
def baseEnd_3674082 : Nat := 628856676677466456992737

theorem tailTrace_3674082 : CollatzResearch.WordTrace tailWord_3674082 prefixEnd_3674082 628856676677466456992737 := by
  unfold tailWord_3674082
  simp only [CollatzResearch.WordTrace]
  refine ⟨33501194868858968023554125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89336519650290581396144333 33501194868858968023554125)
  ·
    refine ⟨12562948075822113008832797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33501194868858968023554125 12562948075822113008832797)
    ·
      refine ⟨4711105528433292378312299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12562948075822113008832797 4711105528433292378312299)
      ·
        refine ⟨7066658292649938567468449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4711105528433292378312299 7066658292649938567468449)
        ·
          refine ⟨5299993719487453925601337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7066658292649938567468449 5299993719487453925601337)
          ·
            refine ⟨3974995289615590444201003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5299993719487453925601337 3974995289615590444201003)
            ·
              refine ⟨5962492934423385666301505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3974995289615590444201003 5962492934423385666301505)
              ·
                refine ⟨4471869700817539249726129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5962492934423385666301505 4471869700817539249726129)
                ·
                  refine ⟨3353902275613154437294597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4471869700817539249726129 3353902275613154437294597)
                  ·
                    refine ⟨628856676677466456992737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3353902275613154437294597 628856676677466456992737)
                    ·
                      rfl

theorem cell23_3674082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_3674082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3674082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3674082 prefixEnd_3674082 := by exact prefixLift 3674082
  have htrace : WordTrace (prefixWord ++ tailWord_3674082) baseStart_3674082 baseEnd_3674082 := by
    simpa [prefixWord, tailWord_3674082, baseEnd_3674082] using wordTrace_append hprefix tailTrace_3674082
  have hstable : (prefixWord ++ tailWord_3674082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3674082).length < 2 ^ (prefixWord ++ tailWord_3674082).sum := by decide
  have hdescent : baseEnd_3674082 < baseStart_3674082 := by decide
  rcases family_descends (prefixWord ++ tailWord_3674082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3674104 : List Nat := [2, 1, 2, 1, 1, 3, 4, 1, 2, 6]
def baseStart_3674104 : Nat := 118140960795 + 3674104 * 2 ^ 59
def prefixEnd_3674104 : Nat := 4983230072969 + 3 ^ 40 * 3674104 * 2
def baseEnd_3674104 : Nat := 628860442202266094967703

theorem tailTrace_3674104 : CollatzResearch.WordTrace tailWord_3674104 prefixEnd_3674104 628860442202266094967703 := by
  unfold tailWord_3674104
  simp only [CollatzResearch.WordTrace]
  refine ⟨67002790940678084925758683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89337054587570779901011577 67002790940678084925758683)
  ·
    refine ⟨100504186411017127388638025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67002790940678084925758683 100504186411017127388638025)
    ·
      refine ⟨75378139808262845541478519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100504186411017127388638025 75378139808262845541478519)
      ·
        refine ⟨113067209712394268312217779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75378139808262845541478519 113067209712394268312217779)
        ·
          refine ⟨169600814568591402468326669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113067209712394268312217779 169600814568591402468326669)
          ·
            refine ⟨63600305463221775925622501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 169600814568591402468326669 63600305463221775925622501)
            ·
              refine ⟨11925057274354082986054219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63600305463221775925622501 11925057274354082986054219)
              ·
                refine ⟨17887585911531124479081329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11925057274354082986054219 17887585911531124479081329)
                ·
                  refine ⟨13415689433648343359310997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17887585911531124479081329 13415689433648343359310997)
                  ·
                    refine ⟨628860442202266094967703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13415689433648343359310997 628860442202266094967703)
                    ·
                      rfl

theorem cell23_3674104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 1, 2, 6].length) (baseStart_3674104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3674104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3674104 prefixEnd_3674104 := by exact prefixLift 3674104
  have htrace : WordTrace (prefixWord ++ tailWord_3674104) baseStart_3674104 baseEnd_3674104 := by
    simpa [prefixWord, tailWord_3674104, baseEnd_3674104] using wordTrace_append hprefix tailTrace_3674104
  have hstable : (prefixWord ++ tailWord_3674104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3674104).length < 2 ^ (prefixWord ++ tailWord_3674104).sum := by decide
  have hdescent : baseEnd_3674104 < baseStart_3674104 := by decide
  rcases family_descends (prefixWord ++ tailWord_3674104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3674105 : List Nat := [1, 2, 1, 3, 1, 5, 3, 1, 2, 1, 3]
def baseStart_3674105 : Nat := 118140960795 + 3674105 * 2 ^ 59
def prefixEnd_3674105 : Nat := 4983230072969 + 3 ^ 40 * 3674105 * 2
def baseEnd_3674105 : Nat := 1886581840087452780990605

theorem tailTrace_3674105 : CollatzResearch.WordTrace tailWord_3674105 prefixEnd_3674105 1886581840087452780990605 := by
  unfold tailWord_3674105
  simp only [CollatzResearch.WordTrace]
  refine ⟨134005618354352547022303769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89337078902901698014869179 134005618354352547022303769)
  ·
    refine ⟨100504213765764410266727827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134005618354352547022303769 100504213765764410266727827)
    ·
      refine ⟨150756320648646615400091741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100504213765764410266727827 150756320648646615400091741)
      ·
        refine ⟨56533620243242480775034403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150756320648646615400091741 56533620243242480775034403)
        ·
          refine ⟨84800430364863721162551605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56533620243242480775034403 84800430364863721162551605)
          ·
            refine ⟨7950040346705973858989213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 84800430364863721162551605 7950040346705973858989213)
            ·
              refine ⟨2981265130014740197120955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7950040346705973858989213 2981265130014740197120955)
              ·
                refine ⟨4471897695022110295681433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2981265130014740197120955 4471897695022110295681433)
                ·
                  refine ⟨3353923271266582721761075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4471897695022110295681433 3353923271266582721761075)
                  ·
                    refine ⟨5030884906899874082641613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3353923271266582721761075 5030884906899874082641613)
                    ·
                      refine ⟨1886581840087452780990605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5030884906899874082641613 1886581840087452780990605)
                      ·
                        rfl

theorem cell23_3674105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 3, 1, 2, 1, 3].length) (baseStart_3674105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3674105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3674105 prefixEnd_3674105 := by exact prefixLift 3674105
  have htrace : WordTrace (prefixWord ++ tailWord_3674105) baseStart_3674105 baseEnd_3674105 := by
    simpa [prefixWord, tailWord_3674105, baseEnd_3674105] using wordTrace_append hprefix tailTrace_3674105
  have hstable : (prefixWord ++ tailWord_3674105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3674105).length < 2 ^ (prefixWord ++ tailWord_3674105).sum := by decide
  have hdescent : baseEnd_3674105 < baseStart_3674105 := by decide
  rcases family_descends (prefixWord ++ tailWord_3674105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3674162 : List Nat := [3, 2, 1, 1, 2, 3, 4, 1, 2, 2, 2]
def baseStart_3674162 : Nat := 118140960795 + 3674162 * 2 ^ 59
def prefixEnd_3674162 : Nat := 4983230072969 + 3 ^ 40 * 3674162 * 2
def baseEnd_3674162 : Nat := 1886611108484759057977843

theorem tailTrace_3674162 : CollatzResearch.WordTrace tailWord_3674162 prefixEnd_3674162 1886611108484759057977843 := by
  unfold tailWord_3674162
  simp only [CollatzResearch.WordTrace]
  refine ⟨33501924328786511439282185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89338464876764030504752493 33501924328786511439282185)
  ·
    refine ⟨25126443246589883579461639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33501924328786511439282185 25126443246589883579461639)
    ·
      refine ⟨37689664869884825369192459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25126443246589883579461639 37689664869884825369192459)
      ·
        refine ⟨56534497304827238053788689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37689664869884825369192459 56534497304827238053788689)
        ·
          refine ⟨42400872978620428540341517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56534497304827238053788689 42400872978620428540341517)
          ·
            refine ⟨15900327366982660702628069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42400872978620428540341517 15900327366982660702628069)
            ·
              refine ⟨2981311381309248881742763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15900327366982660702628069 2981311381309248881742763)
              ·
                refine ⟨4471967071963873322614145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2981311381309248881742763 4471967071963873322614145)
                ·
                  refine ⟨3353975303972904991960609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4471967071963873322614145 3353975303972904991960609)
                  ·
                    refine ⟨2515481477979678743970457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3353975303972904991960609 2515481477979678743970457)
                    ·
                      refine ⟨1886611108484759057977843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2515481477979678743970457 1886611108484759057977843)
                      ·
                        rfl

theorem cell23_3674162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 4, 1, 2, 2, 2].length) (baseStart_3674162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3674162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3674162 prefixEnd_3674162 := by exact prefixLift 3674162
  have htrace : WordTrace (prefixWord ++ tailWord_3674162) baseStart_3674162 baseEnd_3674162 := by
    simpa [prefixWord, tailWord_3674162, baseEnd_3674162] using wordTrace_append hprefix tailTrace_3674162
  have hstable : (prefixWord ++ tailWord_3674162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3674162).length < 2 ^ (prefixWord ++ tailWord_3674162).sum := by decide
  have hdescent : baseEnd_3674162 < baseStart_3674162 := by decide
  rcases family_descends (prefixWord ++ tailWord_3674162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3674171 : List Nat := [1, 1, 1, 1, 1, 2, 1, 6, 2, 5, 2]
def baseStart_3674171 : Nat := 118140960795 + 3674171 * 2 ^ 59
def prefixEnd_3674171 : Nat := 4983230072969 + 3 ^ 40 * 3674171 * 2
def baseEnd_3674171 : Nat := 1886615729810649522765301

theorem tailTrace_3674171 : CollatzResearch.WordTrace tailWord_3674171 prefixEnd_3674171 1886615729810649522765301 := by
  unfold tailWord_3674171
  simp only [CollatzResearch.WordTrace]
  refine ⟨134008025572113440294206367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89338683714742293529470911 134008025572113440294206367)
  ·
    refine ⟨201012038358170160441309551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134008025572113440294206367 201012038358170160441309551)
    ·
      refine ⟨301518057537255240661964327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201012038358170160441309551 301518057537255240661964327)
      ·
        refine ⟨452277086305882860992946491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301518057537255240661964327 452277086305882860992946491)
        ·
          refine ⟨678415629458824291489419737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 452277086305882860992946491 678415629458824291489419737)
          ·
            refine ⟨508811722094118218617064803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 678415629458824291489419737 508811722094118218617064803)
            ·
              refine ⟨763217583141177327925597205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 508811722094118218617064803 763217583141177327925597205)
              ·
                refine ⟨35775824209742687246512369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 763217583141177327925597205 35775824209742687246512369)
                ·
                  refine ⟨26831868157307015434884277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35775824209742687246512369 26831868157307015434884277)
                  ·
                    refine ⟨2515487639747532697020401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26831868157307015434884277 2515487639747532697020401)
                    ·
                      refine ⟨1886615729810649522765301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2515487639747532697020401 1886615729810649522765301)
                      ·
                        rfl

theorem cell23_3674171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 6, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 6, 2, 5, 2].length) (baseStart_3674171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3674171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3674171 prefixEnd_3674171 := by exact prefixLift 3674171
  have htrace : WordTrace (prefixWord ++ tailWord_3674171) baseStart_3674171 baseEnd_3674171 := by
    simpa [prefixWord, tailWord_3674171, baseEnd_3674171] using wordTrace_append hprefix tailTrace_3674171
  have hstable : (prefixWord ++ tailWord_3674171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3674171).length < 2 ^ (prefixWord ++ tailWord_3674171).sum := by decide
  have hdescent : baseEnd_3674171 < baseStart_3674171 := by decide
  rcases family_descends (prefixWord ++ tailWord_3674171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3674201 : List Nat := [1, 2, 1, 2, 2, 1, 3, 4, 2, 1, 4]
def baseStart_3674201 : Nat := 118140960795 + 3674201 * 2 ^ 59
def prefixEnd_3674201 : Nat := 4983230072969 + 3 ^ 40 * 3674201 * 2
def baseEnd_3674201 : Nat := 1886631134230284405390163

theorem tailTrace_3674201 : CollatzResearch.WordTrace tailWord_3674201 prefixEnd_3674201 1886631134230284405390163 := by
  unfold tailWord_3674201
  simp only [CollatzResearch.WordTrace]
  refine ⟨134009119762004755417798457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89339413174669836945198971 134009119762004755417798457)
  ·
    refine ⟨100506839821503566563348843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134009119762004755417798457 100506839821503566563348843)
    ·
      refine ⟨150760259732255349845023265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100506839821503566563348843 150760259732255349845023265)
      ·
        refine ⟨113070194799191512383767449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150760259732255349845023265 113070194799191512383767449)
        ·
          refine ⟨84802646099393634287825587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113070194799191512383767449 84802646099393634287825587)
          ·
            refine ⟨127203969149090451431738381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84802646099393634287825587 127203969149090451431738381)
            ·
              refine ⟨47701488430908919286901893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127203969149090451431738381 47701488430908919286901893)
              ·
                refine ⟨8944029080795422366294105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47701488430908919286901893 8944029080795422366294105)
                ·
                  refine ⟨6708021810596566774720579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8944029080795422366294105 6708021810596566774720579)
                  ·
                    refine ⟨10062032715894850162080869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6708021810596566774720579 10062032715894850162080869)
                    ·
                      refine ⟨1886631134230284405390163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10062032715894850162080869 1886631134230284405390163)
                      ·
                        rfl

theorem cell23_3674201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 4, 2, 1, 4].length) (baseStart_3674201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3674201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3674201 prefixEnd_3674201 := by exact prefixLift 3674201
  have htrace : WordTrace (prefixWord ++ tailWord_3674201) baseStart_3674201 baseEnd_3674201 := by
    simpa [prefixWord, tailWord_3674201, baseEnd_3674201] using wordTrace_append hprefix tailTrace_3674201
  have hstable : (prefixWord ++ tailWord_3674201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3674201).length < 2 ^ (prefixWord ++ tailWord_3674201).sum := by decide
  have hdescent : baseEnd_3674201 < baseStart_3674201 := by decide
  rcases family_descends (prefixWord ++ tailWord_3674201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3674205 : List Nat := [1, 4, 4, 1, 1, 1, 1, 1, 2, 5, 2]
def baseStart_3674205 : Nat := 118140960795 + 3674205 * 2 ^ 59
def prefixEnd_3674205 : Nat := 4983230072969 + 3 ^ 40 * 3674205 * 2
def baseEnd_3674205 : Nat := 1886633188152902389740145

theorem tailTrace_3674205 : CollatzResearch.WordTrace tailWord_3674205 prefixEnd_3674205 1886633188152902389740145 := by
  unfold tailWord_3674205
  simp only [CollatzResearch.WordTrace]
  refine ⟨134009265653990264100944069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89339510435993509400629379 134009265653990264100944069)
  ·
    refine ⟨25126737310123174518927013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134009265653990264100944069 25126737310123174518927013)
    ·
      refine ⟨4711263245648095222298815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25126737310123174518927013 4711263245648095222298815)
      ·
        refine ⟨7066894868472142833448223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4711263245648095222298815 7066894868472142833448223)
        ·
          refine ⟨10600342302708214250172335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7066894868472142833448223 10600342302708214250172335)
          ·
            refine ⟨15900513454062321375258503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10600342302708214250172335 15900513454062321375258503)
            ·
              refine ⟨23850770181093482062887755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15900513454062321375258503 23850770181093482062887755)
              ·
                refine ⟨35776155271640223094331633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23850770181093482062887755 35776155271640223094331633)
                ·
                  refine ⟨26832116453730167320748725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35776155271640223094331633 26832116453730167320748725)
                  ·
                    refine ⟨2515510917537203186320193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26832116453730167320748725 2515510917537203186320193)
                    ·
                      refine ⟨1886633188152902389740145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2515510917537203186320193 1886633188152902389740145)
                      ·
                        rfl

theorem cell23_3674205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 1, 2, 5, 2].length) (baseStart_3674205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3674205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3674205 prefixEnd_3674205 := by exact prefixLift 3674205
  have htrace : WordTrace (prefixWord ++ tailWord_3674205) baseStart_3674205 baseEnd_3674205 := by
    simpa [prefixWord, tailWord_3674205, baseEnd_3674205] using wordTrace_append hprefix tailTrace_3674205
  have hstable : (prefixWord ++ tailWord_3674205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3674205).length < 2 ^ (prefixWord ++ tailWord_3674205).sum := by decide
  have hdescent : baseEnd_3674205 < baseStart_3674205 := by decide
  rcases family_descends (prefixWord ++ tailWord_3674205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3674245 : List Nat := [1, 3, 1, 1, 5, 1, 1, 5, 1, 4]
def baseStart_3674245 : Nat := 118140960795 + 3674245 * 2 ^ 59
def prefixEnd_3674245 : Nat := 4983230072969 + 3 ^ 40 * 3674245 * 2
def baseEnd_3674245 : Nat := 628884575793027411079987

theorem tailTrace_3674245 : CollatzResearch.WordTrace tailWord_3674245 prefixEnd_3674245 628884575793027411079987 := by
  unfold tailWord_3674245
  simp only [CollatzResearch.WordTrace]
  refine ⟨134010724573845350932400189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89340483049230233954933459 134010724573845350932400189)
  ·
    refine ⟨50254021715192006599650071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134010724573845350932400189 50254021715192006599650071)
    ·
      refine ⟨75381032572788009899475107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50254021715192006599650071 75381032572788009899475107)
      ·
        refine ⟨113071548859182014849212661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75381032572788009899475107 113071548859182014849212661)
        ·
          refine ⟨10600457705548313892113687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 113071548859182014849212661 10600457705548313892113687)
          ·
            refine ⟨15900686558322470838170531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10600457705548313892113687 15900686558322470838170531)
            ·
              refine ⟨23851029837483706257255797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15900686558322470838170531 23851029837483706257255797)
              ·
                refine ⟨2236034047264097461617731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23851029837483706257255797 2236034047264097461617731)
                ·
                  refine ⟨3354051070896146192426597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2236034047264097461617731 3354051070896146192426597)
                  ·
                    refine ⟨628884575793027411079987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3354051070896146192426597 628884575793027411079987)
                    ·
                      rfl

theorem cell23_3674245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 5, 1, 4].length) (baseStart_3674245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3674245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3674245 prefixEnd_3674245 := by exact prefixLift 3674245
  have htrace : WordTrace (prefixWord ++ tailWord_3674245) baseStart_3674245 baseEnd_3674245 := by
    simpa [prefixWord, tailWord_3674245, baseEnd_3674245] using wordTrace_append hprefix tailTrace_3674245
  have hstable : (prefixWord ++ tailWord_3674245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3674245).length < 2 ^ (prefixWord ++ tailWord_3674245).sum := by decide
  have hdescent : baseEnd_3674245 < baseStart_3674245 := by decide
  rcases family_descends (prefixWord ++ tailWord_3674245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3674301 : List Nat := [1, 4, 1, 2, 1, 1, 1, 3, 3, 6]
def baseStart_3674301 : Nat := 118140960795 + 3674301 * 2 ^ 59
def prefixEnd_3674301 : Nat := 4983230072969 + 3 ^ 40 * 3674301 * 2
def baseEnd_3674301 : Nat := 628894160765244671379901

theorem tailTrace_3674301 : CollatzResearch.WordTrace tailWord_3674301 prefixEnd_3674301 628894160765244671379901 := by
  unfold tailWord_3674301
  simp only [CollatzResearch.WordTrace]
  refine ⟨134012767061642472496438757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89341844707761648330959171 134012767061642472496438757)
  ·
    refine ⟨25127393824057963593082267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134012767061642472496438757 25127393824057963593082267)
    ·
      refine ⟨37691090736086945389623401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25127393824057963593082267 37691090736086945389623401)
      ·
        refine ⟨28268318052065209042217551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37691090736086945389623401 28268318052065209042217551)
        ·
          refine ⟨42402477078097813563326327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28268318052065209042217551 42402477078097813563326327)
          ·
            refine ⟨63603715617146720344989491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42402477078097813563326327 63603715617146720344989491)
            ·
              refine ⟨95405573425720080517484237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63603715617146720344989491 95405573425720080517484237)
              ·
                refine ⟨35777090034645030194056589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95405573425720080517484237 35777090034645030194056589)
                ·
                  refine ⟨13416408762991886322771221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35777090034645030194056589 13416408762991886322771221)
                  ·
                    refine ⟨628894160765244671379901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13416408762991886322771221 628894160765244671379901)
                    ·
                      rfl

theorem cell23_3674301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 3, 3, 6].length) (baseStart_3674301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3674301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3674301 prefixEnd_3674301 := by exact prefixLift 3674301
  have htrace : WordTrace (prefixWord ++ tailWord_3674301) baseStart_3674301 baseEnd_3674301 := by
    simpa [prefixWord, tailWord_3674301, baseEnd_3674301] using wordTrace_append hprefix tailTrace_3674301
  have hstable : (prefixWord ++ tailWord_3674301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3674301).length < 2 ^ (prefixWord ++ tailWord_3674301).sum := by decide
  have hdescent : baseEnd_3674301 < baseStart_3674301 := by decide
  rcases family_descends (prefixWord ++ tailWord_3674301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3674321 : List Nat := [1, 2, 2, 1, 2, 2, 3, 2, 1, 1, 6]
def baseStart_3674321 : Nat := 118140960795 + 3674321 * 2 ^ 59
def prefixEnd_3674321 : Nat := 4983230072969 + 3 ^ 40 * 3674321 * 2
def baseEnd_3674321 : Nat := 1886692751908823935889611

theorem tailTrace_3674321 : CollatzResearch.WordTrace tailWord_3674321 prefixEnd_3674321 1886692751908823935889611 := by
  unfold tailWord_3674321
  simp only [CollatzResearch.WordTrace]
  refine ⟨134013496521570015912166817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89342331014380010608111211 134013496521570015912166817)
  ·
    refine ⟨100510122391177511934125113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134013496521570015912166817 100510122391177511934125113)
    ·
      refine ⟨75382591793383133950593835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100510122391177511934125113 75382591793383133950593835)
      ·
        refine ⟨113073887690074700925890753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75382591793383133950593835 113073887690074700925890753)
        ·
          refine ⟨84805415767556025694418065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113073887690074700925890753 84805415767556025694418065)
          ·
            refine ⟨63604061825667019270813549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84805415767556025694418065 63604061825667019270813549)
            ·
              refine ⟨23851523184625132226555081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63604061825667019270813549 23851523184625132226555081)
              ·
                refine ⟨17888642388468849169916311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23851523184625132226555081 17888642388468849169916311)
                ·
                  refine ⟨26832963582703273754874467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17888642388468849169916311 26832963582703273754874467)
                  ·
                    refine ⟨40249445374054910632311701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26832963582703273754874467 40249445374054910632311701)
                    ·
                      refine ⟨1886692751908823935889611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40249445374054910632311701 1886692751908823935889611)
                      ·
                        rfl

theorem cell23_3674321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 2, 1, 1, 6].length) (baseStart_3674321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3674321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3674321 prefixEnd_3674321 := by exact prefixLift 3674321
  have htrace : WordTrace (prefixWord ++ tailWord_3674321) baseStart_3674321 baseEnd_3674321 := by
    simpa [prefixWord, tailWord_3674321, baseEnd_3674321] using wordTrace_append hprefix tailTrace_3674321
  have hstable : (prefixWord ++ tailWord_3674321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3674321).length < 2 ^ (prefixWord ++ tailWord_3674321).sum := by decide
  have hdescent : baseEnd_3674321 < baseStart_3674321 := by decide
  rcases family_descends (prefixWord ++ tailWord_3674321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3674328 : List Nat := [2, 1, 2, 2, 4, 1, 2, 2, 1, 1, 5]
def baseStart_3674328 : Nat := 118140960795 + 3674328 * 2 ^ 59
def prefixEnd_3674328 : Nat := 4983230072969 + 3 ^ 40 * 3674328 * 2
def baseEnd_3674328 : Nat := 1886696346273405408502079

theorem tailTrace_3674328 : CollatzResearch.WordTrace tailWord_3674328 prefixEnd_3674328 1886696346273405408502079 := by
  unfold tailWord_3674328
  simp only [CollatzResearch.WordTrace]
  refine ⟨67006875916272328053835819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89342501221696437405114425 67006875916272328053835819)
  ·
    refine ⟨100510313874408492080753729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67006875916272328053835819 100510313874408492080753729)
    ·
      refine ⟨75382735405806369060565297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100510313874408492080753729 75382735405806369060565297)
      ·
        refine ⟨56537051554354776795423973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75382735405806369060565297 56537051554354776795423973)
        ·
          refine ⟨10600697166441520649141995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56537051554354776795423973 10600697166441520649141995)
          ·
            refine ⟨15901045749662280973712993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10600697166441520649141995 15901045749662280973712993)
            ·
              refine ⟨11925784312246710730284745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15901045749662280973712993 11925784312246710730284745)
              ·
                refine ⟨8944338234185033047713559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11925784312246710730284745 8944338234185033047713559)
                ·
                  refine ⟨13416507351277549571570339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8944338234185033047713559 13416507351277549571570339)
                  ·
                    refine ⟨20124761026916324357355509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13416507351277549571570339 20124761026916324357355509)
                    ·
                      refine ⟨1886696346273405408502079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20124761026916324357355509 1886696346273405408502079)
                      ·
                        rfl

theorem cell23_3674328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 2, 1, 1, 5].length) (baseStart_3674328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3674328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3674328 prefixEnd_3674328 := by exact prefixLift 3674328
  have htrace : WordTrace (prefixWord ++ tailWord_3674328) baseStart_3674328 baseEnd_3674328 := by
    simpa [prefixWord, tailWord_3674328, baseEnd_3674328] using wordTrace_append hprefix tailTrace_3674328
  have hstable : (prefixWord ++ tailWord_3674328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3674328).length < 2 ^ (prefixWord ++ tailWord_3674328).sum := by decide
  have hdescent : baseEnd_3674328 < baseStart_3674328 := by decide
  rcases family_descends (prefixWord ++ tailWord_3674328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3674339 : List Nat := [1, 1, 1, 8, 2, 1, 1, 2, 1, 5]
def baseStart_3674339 : Nat := 118140960795 + 3674339 * 2 ^ 59
def prefixEnd_3674339 : Nat := 4983230072969 + 3 ^ 40 * 3674339 * 2
def baseEnd_3674339 : Nat := 628900664853534955154843

theorem tailTrace_3674339 : CollatzResearch.WordTrace tailWord_3674339 prefixEnd_3674339 628900664853534955154843 := by
  unfold tailWord_3674339
  simp only [CollatzResearch.WordTrace]
  refine ⟨134014153035504804986322071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89342768690336536657548047 134014153035504804986322071)
  ·
    refine ⟨201021229553257207479483107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134014153035504804986322071 201021229553257207479483107)
    ·
      refine ⟨301531844329885811219224661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201021229553257207479483107 301531844329885811219224661)
      ·
        refine ⟨3533576300740849350225289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 301531844329885811219224661 3533576300740849350225289)
        ·
          refine ⟨2650182225555637012668967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3533576300740849350225289 2650182225555637012668967)
          ·
            refine ⟨3975273338333455519003451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2650182225555637012668967 3975273338333455519003451)
            ·
              refine ⟨5962910007500183278505177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3975273338333455519003451 5962910007500183278505177)
              ·
                refine ⟨4472182505625137458878883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5962910007500183278505177 4472182505625137458878883)
                ·
                  refine ⟨6708273758437706188318325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4472182505625137458878883 6708273758437706188318325)
                  ·
                    refine ⟨628900664853534955154843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6708273758437706188318325 628900664853534955154843)
                    ·
                      rfl

theorem cell23_3674339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 1, 2, 1, 5].length) (baseStart_3674339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3674339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3674339 prefixEnd_3674339 := by exact prefixLift 3674339
  have htrace : WordTrace (prefixWord ++ tailWord_3674339) baseStart_3674339 baseEnd_3674339 := by
    simpa [prefixWord, tailWord_3674339, baseEnd_3674339] using wordTrace_append hprefix tailTrace_3674339
  have hstable : (prefixWord ++ tailWord_3674339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3674339).length < 2 ^ (prefixWord ++ tailWord_3674339).sum := by decide
  have hdescent : baseEnd_3674339 < baseStart_3674339 := by decide
  rcases family_descends (prefixWord ++ tailWord_3674339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3674362 : List Nat := [3, 1, 1, 1, 1, 6, 3, 1, 1, 2, 3]
def baseStart_3674362 : Nat := 118140960795 + 3674362 * 2 ^ 59
def prefixEnd_3674362 : Nat := 4983230072969 + 3 ^ 40 * 3674362 * 2
def baseEnd_3674362 : Nat := 1886713804615658275476923

theorem tailTrace_3674362 : CollatzResearch.WordTrace tailWord_3674362 prefixEnd_3674362 1886713804615658275476923 := by
  unfold tailWord_3674362
  simp only [CollatzResearch.WordTrace]
  refine ⟨33503747978605369978602335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89343327942947653276272893 33503747978605369978602335)
  ·
    refine ⟨50255621967908054967903503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33503747978605369978602335 50255621967908054967903503)
    ·
      refine ⟨75383432951862082451855255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50255621967908054967903503 75383432951862082451855255)
      ·
        refine ⟨113075149427793123677782883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75383432951862082451855255 113075149427793123677782883)
        ·
          refine ⟨169612724141689685516674325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113075149427793123677782883 169612724141689685516674325)
          ·
            refine ⟨7950596444141704008594109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 169612724141689685516674325 7950596444141704008594109)
            ·
              refine ⟨2981473666553139003222791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7950596444141704008594109 2981473666553139003222791)
              ·
                refine ⟨4472210499829708504834187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2981473666553139003222791 4472210499829708504834187)
                ·
                  refine ⟨6708315749744562757251281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4472210499829708504834187 6708315749744562757251281)
                  ·
                    refine ⟨5031236812308422067938461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6708315749744562757251281 5031236812308422067938461)
                    ·
                      refine ⟨1886713804615658275476923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5031236812308422067938461 1886713804615658275476923)
                      ·
                        rfl

theorem cell23_3674362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 3, 1, 1, 2, 3].length) (baseStart_3674362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3674362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3674362 prefixEnd_3674362 := by exact prefixLift 3674362
  have htrace : WordTrace (prefixWord ++ tailWord_3674362) baseStart_3674362 baseEnd_3674362 := by
    simpa [prefixWord, tailWord_3674362, baseEnd_3674362] using wordTrace_append hprefix tailTrace_3674362
  have hstable : (prefixWord ++ tailWord_3674362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3674362).length < 2 ^ (prefixWord ++ tailWord_3674362).sum := by decide
  have hdescent : baseEnd_3674362 < baseStart_3674362 := by decide
  rcases family_descends (prefixWord ++ tailWord_3674362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3674376 : List Nat := [2, 1, 3, 2, 3, 1, 4, 2, 1, 2, 2]
def baseStart_3674376 : Nat := 118140960795 + 3674376 * 2 ^ 59
def prefixEnd_3674376 : Nat := 4983230072969 + 3 ^ 40 * 3674376 * 2
def baseEnd_3674376 : Nat := 1886720993344821220701859

theorem tailTrace_3674376 : CollatzResearch.WordTrace tailWord_3674376 prefixEnd_3674376 1886720993344821220701859 := by
  unfold tailWord_3674376
  simp only [CollatzResearch.WordTrace]
  refine ⟨67007751268185380152709491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89343668357580506870279321 67007751268185380152709491)
  ·
    refine ⟨100511626902278070229064237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67007751268185380152709491 100511626902278070229064237)
    ·
      refine ⟨37691860088354276335899089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100511626902278070229064237 37691860088354276335899089)
      ·
        refine ⟨28268895066265707251924317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37691860088354276335899089 28268895066265707251924317)
        ·
          refine ⟨10600835649849640219471619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28268895066265707251924317 10600835649849640219471619)
          ·
            refine ⟨15901253474774460329207429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10600835649849640219471619 15901253474774460329207429)
            ·
              refine ⟨2981485026520211311726393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15901253474774460329207429 2981485026520211311726393)
              ·
                refine ⟨2236113769890158483794795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2981485026520211311726393 2236113769890158483794795)
                ·
                  refine ⟨3354170654835237725692193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2236113769890158483794795 3354170654835237725692193)
                  ·
                    refine ⟨2515627991126428294269145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3354170654835237725692193 2515627991126428294269145)
                    ·
                      refine ⟨1886720993344821220701859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2515627991126428294269145 1886720993344821220701859)
                      ·
                        rfl

theorem cell23_3674376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 4, 2, 1, 2, 2].length) (baseStart_3674376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3674376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3674376 prefixEnd_3674376 := by exact prefixLift 3674376
  have htrace : WordTrace (prefixWord ++ tailWord_3674376) baseStart_3674376 baseEnd_3674376 := by
    simpa [prefixWord, tailWord_3674376, baseEnd_3674376] using wordTrace_append hprefix tailTrace_3674376
  have hstable : (prefixWord ++ tailWord_3674376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3674376).length < 2 ^ (prefixWord ++ tailWord_3674376).sum := by decide
  have hdescent : baseEnd_3674376 < baseStart_3674376 := by decide
  rcases family_descends (prefixWord ++ tailWord_3674376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3674385 : List Nat := [1, 2, 2, 1, 1, 5, 1, 2, 3, 3, 2]
def baseStart_3674385 : Nat := 118140960795 + 3674385 * 2 ^ 59
def prefixEnd_3674385 : Nat := 4983230072969 + 3 ^ 40 * 3674385 * 2
def baseEnd_3674385 : Nat := 1886725614670711685489317

theorem tailTrace_3674385 : CollatzResearch.WordTrace tailWord_3674385 prefixEnd_3674385 1886725614670711685489317 := by
  unfold tailWord_3674385
  simp only [CollatzResearch.WordTrace]
  refine ⟨134015830793338154842496609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89343887195558769894997739 134015830793338154842496609)
  ·
    refine ⟨100511873095003616131872457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134015830793338154842496609 100511873095003616131872457)
    ·
      refine ⟨75383904821252712098904343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100511873095003616131872457 75383904821252712098904343)
      ·
        refine ⟨113075857231879068148356515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75383904821252712098904343 113075857231879068148356515)
        ·
          refine ⟨169613785847818602222534773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113075857231879068148356515 169613785847818602222534773)
          ·
            refine ⟨15901292423232993958362635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 169613785847818602222534773 15901292423232993958362635)
            ·
              refine ⟨23851938634849490937543953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15901292423232993958362635 23851938634849490937543953)
              ·
                refine ⟨17888953976137118203157965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23851938634849490937543953 17888953976137118203157965)
                ·
                  refine ⟨6708357741051419326184237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17888953976137118203157965 6708357741051419326184237)
                  ·
                    refine ⟨2515634152894282247319089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6708357741051419326184237 2515634152894282247319089)
                    ·
                      refine ⟨1886725614670711685489317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2515634152894282247319089 1886725614670711685489317)
                      ·
                        rfl

theorem cell23_3674385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 3, 2].length) (baseStart_3674385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3674385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3674385 prefixEnd_3674385 := by exact prefixLift 3674385
  have htrace : WordTrace (prefixWord ++ tailWord_3674385) baseStart_3674385 baseEnd_3674385 := by
    simpa [prefixWord, tailWord_3674385, baseEnd_3674385] using wordTrace_append hprefix tailTrace_3674385
  have hstable : (prefixWord ++ tailWord_3674385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3674385).length < 2 ^ (prefixWord ++ tailWord_3674385).sum := by decide
  have hdescent : baseEnd_3674385 < baseStart_3674385 := by decide
  rcases family_descends (prefixWord ++ tailWord_3674385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3674402 : List Nat := [3, 3, 1, 1, 3, 1, 2, 1, 3, 3, 2]
def baseStart_3674402 : Nat := 118140960795 + 3674402 * 2 ^ 59
def prefixEnd_3674402 : Nat := 4983230072969 + 3 ^ 40 * 3674402 * 2
def baseEnd_3674402 : Nat := 1886734343841838118976739

theorem tailTrace_3674402 : CollatzResearch.WordTrace tailWord_3674402 prefixEnd_3674402 1886734343841838118976739 := by
  unfold tailWord_3674402
  simp only [CollatzResearch.WordTrace]
  refine ⟨33504112708569141686466365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89344300556184377830576973 33504112708569141686466365)
  ·
    refine ⟨12564042265713428132424887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33504112708569141686466365 12564042265713428132424887)
    ·
      refine ⟨18846063398570142198637331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12564042265713428132424887 18846063398570142198637331)
      ·
        refine ⟨28269095097855213297955997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18846063398570142198637331 28269095097855213297955997)
        ·
          refine ⟨10600910661695704986733499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28269095097855213297955997 10600910661695704986733499)
          ·
            refine ⟨15901365992543557480100249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10600910661695704986733499 15901365992543557480100249)
            ·
              refine ⟨11926024494407668110075187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15901365992543557480100249 11926024494407668110075187)
              ·
                refine ⟨17889036741611502165112781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11926024494407668110075187 17889036741611502165112781)
                ·
                  refine ⟨6708388778104313311917293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17889036741611502165112781 6708388778104313311917293)
                  ·
                    refine ⟨2515645791789117491968985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6708388778104313311917293 2515645791789117491968985)
                    ·
                      refine ⟨1886734343841838118976739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2515645791789117491968985 1886734343841838118976739)
                      ·
                        rfl

theorem cell23_3674402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 1, 3, 3, 2].length) (baseStart_3674402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3674402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3674402 prefixEnd_3674402 := by exact prefixLift 3674402
  have htrace : WordTrace (prefixWord ++ tailWord_3674402) baseStart_3674402 baseEnd_3674402 := by
    simpa [prefixWord, tailWord_3674402, baseEnd_3674402] using wordTrace_append hprefix tailTrace_3674402
  have hstable : (prefixWord ++ tailWord_3674402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3674402).length < 2 ^ (prefixWord ++ tailWord_3674402).sum := by decide
  have hdescent : baseEnd_3674402 < baseStart_3674402 := by decide
  rcases family_descends (prefixWord ++ tailWord_3674402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3674413 : List Nat := [1, 5, 3, 1, 3, 1, 2, 1, 1, 2, 3]
def baseStart_3674413 : Nat := 118140960795 + 3674413 * 2 ^ 59
def prefixEnd_3674413 : Nat := 4983230072969 + 3 ^ 40 * 3674413 * 2
def baseEnd_3674413 : Nat := 1886739992129037575939189

theorem tailTrace_3674413 : CollatzResearch.WordTrace tailWord_3674413 prefixEnd_3674413 1886739992129037575939189 := by
  unfold tailWord_3674413
  simp only [CollatzResearch.WordTrace]
  refine ⟨134016852037236715624515893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89344568024824477083010595 134016852037236715624515893)
  ·
    refine ⟨12564079878490942089798365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 134016852037236715624515893 12564079878490942089798365)
    ·
      refine ⟨4711529954434103283674387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12564079878490942089798365 4711529954434103283674387)
      ·
        refine ⟨7067294931651154925511581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4711529954434103283674387 7067294931651154925511581)
        ·
          refine ⟨2650235599369183097066843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7067294931651154925511581 2650235599369183097066843)
          ·
            refine ⟨3975353399053774645600265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2650235599369183097066843 3975353399053774645600265)
            ·
              refine ⟨2981515049290330984200199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3975353399053774645600265 2981515049290330984200199)
              ·
                refine ⟨4472272573935496476300299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2981515049290330984200199 4472272573935496476300299)
                ·
                  refine ⟨6708408860903244714450449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4472272573935496476300299 6708408860903244714450449)
                  ·
                    refine ⟨5031306645677433535837837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6708408860903244714450449 5031306645677433535837837)
                    ·
                      refine ⟨1886739992129037575939189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5031306645677433535837837 1886739992129037575939189)
                      ·
                        rfl

theorem cell23_3674413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 2, 1, 1, 2, 3].length) (baseStart_3674413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3674413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3674413 prefixEnd_3674413 := by exact prefixLift 3674413
  have htrace : WordTrace (prefixWord ++ tailWord_3674413) baseStart_3674413 baseEnd_3674413 := by
    simpa [prefixWord, tailWord_3674413, baseEnd_3674413] using wordTrace_append hprefix tailTrace_3674413
  have hstable : (prefixWord ++ tailWord_3674413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3674413).length < 2 ^ (prefixWord ++ tailWord_3674413).sum := by decide
  have hdescent : baseEnd_3674413 < baseStart_3674413 := by decide
  rcases family_descends (prefixWord ++ tailWord_3674413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3674415 : List Nat := [1, 1, 2, 1, 2, 1, 6, 2, 1, 4, 2]
def baseStart_3674415 : Nat := 118140960795 + 3674415 * 2 ^ 59
def prefixEnd_3674415 : Nat := 4983230072969 + 3 ^ 40 * 3674415 * 2
def baseEnd_3674415 : Nat := 1886741019090346568114179

theorem tailTrace_3674415 : CollatzResearch.WordTrace tailWord_3674415 prefixEnd_3674415 1886741019090346568114179 := by
  unfold tailWord_3674415
  simp only [CollatzResearch.WordTrace]
  refine ⟨134016924983229469966088699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89344616655486313310725799 134016924983229469966088699)
  ·
    refine ⟨201025387474844204949133049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134016924983229469966088699 201025387474844204949133049)
    ·
      refine ⟨150769040606133153711849787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201025387474844204949133049 150769040606133153711849787)
      ·
        refine ⟨226153560909199730567774681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150769040606133153711849787 226153560909199730567774681)
        ·
          refine ⟨169615170681899797925831011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226153560909199730567774681 169615170681899797925831011)
          ·
            refine ⟨254422756022849696888746517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169615170681899797925831011 254422756022849696888746517)
            ·
              refine ⟨11926066688571079541659993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 254422756022849696888746517 11926066688571079541659993)
              ·
                refine ⟨8944550016428309656244995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11926066688571079541659993 8944550016428309656244995)
                ·
                  refine ⟨13416825024642464484367493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8944550016428309656244995 13416825024642464484367493)
                  ·
                    refine ⟨2515654692120462090818905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13416825024642464484367493 2515654692120462090818905)
                    ·
                      refine ⟨1886741019090346568114179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2515654692120462090818905 1886741019090346568114179)
                      ·
                        rfl

theorem cell23_3674415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 2, 1, 4, 2].length) (baseStart_3674415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3674415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3674415 prefixEnd_3674415 := by exact prefixLift 3674415
  have htrace : WordTrace (prefixWord ++ tailWord_3674415) baseStart_3674415 baseEnd_3674415 := by
    simpa [prefixWord, tailWord_3674415, baseEnd_3674415] using wordTrace_append hprefix tailTrace_3674415
  have hstable : (prefixWord ++ tailWord_3674415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3674415).length < 2 ^ (prefixWord ++ tailWord_3674415).sum := by decide
  have hdescent : baseEnd_3674415 < baseStart_3674415 := by decide
  rcases family_descends (prefixWord ++ tailWord_3674415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3674428 : List Nat := [2, 2, 2, 2, 1, 2, 1, 1, 4, 2, 4]
def baseStart_3674428 : Nat := 118140960795 + 3674428 * 2 ^ 59
def prefixEnd_3674428 : Nat := 4983230072969 + 3 ^ 40 * 3674428 * 2
def baseEnd_3674428 : Nat := 1886747694338855017251619

theorem tailTrace_3674428 : CollatzResearch.WordTrace tailWord_3674428 prefixEnd_3674428 1886747694338855017251619 := by
  unfold tailWord_3674428
  simp only [CollatzResearch.WordTrace]
  refine ⟨67008699566091186593155969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89344932754788248790874625 67008699566091186593155969)
  ·
    refine ⟨50256524674568389944866977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67008699566091186593155969 50256524674568389944866977)
    ·
      refine ⟨37692393505926292458650233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50256524674568389944866977 37692393505926292458650233)
      ·
        refine ⟨28269295129444719343987675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37692393505926292458650233 28269295129444719343987675)
        ·
          refine ⟨42403942694167079015981513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28269295129444719343987675 42403942694167079015981513)
          ·
            refine ⟨31802957020625309261986135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42403942694167079015981513 31802957020625309261986135)
            ·
              refine ⟨47704435530937963892979203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31802957020625309261986135 47704435530937963892979203)
              ·
                refine ⟨71556653296406945839468805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47704435530937963892979203 71556653296406945839468805)
                ·
                  refine ⟨13416872493076302344900401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71556653296406945839468805 13416872493076302344900401)
                  ·
                    refine ⟨10062654369807226758675301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13416872493076302344900401 10062654369807226758675301)
                    ·
                      refine ⟨1886747694338855017251619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10062654369807226758675301 1886747694338855017251619)
                      ·
                        rfl

theorem cell23_3674428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 4, 2, 4].length) (baseStart_3674428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3674428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3674428 prefixEnd_3674428 := by exact prefixLift 3674428
  have htrace : WordTrace (prefixWord ++ tailWord_3674428) baseStart_3674428 baseEnd_3674428 := by
    simpa [prefixWord, tailWord_3674428, baseEnd_3674428] using wordTrace_append hprefix tailTrace_3674428
  have hstable : (prefixWord ++ tailWord_3674428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3674428).length < 2 ^ (prefixWord ++ tailWord_3674428).sum := by decide
  have hdescent : baseEnd_3674428 < baseStart_3674428 := by decide
  rcases family_descends (prefixWord ++ tailWord_3674428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3674432 : List Nat := [2, 1, 1, 2, 2, 1, 2, 6, 2, 2, 2]
def baseStart_3674432 : Nat := 118140960795 + 3674432 * 2 ^ 59
def prefixEnd_3674432 : Nat := 4983230072969 + 3 ^ 40 * 3674432 * 2
def baseEnd_3674432 : Nat := 1886749748261473001601601

theorem tailTrace_3674432 : CollatzResearch.WordTrace tailWord_3674432 prefixEnd_3674432 1886749748261473001601601 := by
  unfold tailWord_3674432
  simp only [CollatzResearch.WordTrace]
  refine ⟨67008772512083940934728775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89345030016111921246305033 67008772512083940934728775)
  ·
    refine ⟨100513158768125911402093163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67008772512083940934728775 100513158768125911402093163)
    ·
      refine ⟨150769738152188867103139745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100513158768125911402093163 150769738152188867103139745)
      ·
        refine ⟨113077303614141650327354809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150769738152188867103139745 113077303614141650327354809)
        ·
          refine ⟨84807977710606237745516107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113077303614141650327354809 84807977710606237745516107)
          ·
            refine ⟨127211966565909356618274161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84807977710606237745516107 127211966565909356618274161)
            ·
              refine ⟨95408974924432017463705621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127211966565909356618274161 95408974924432017463705621)
              ·
                refine ⟨4472295699582750818611201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 95408974924432017463705621 4472295699582750818611201)
                ·
                  refine ⟨3354221774687063113958401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4472295699582750818611201 3354221774687063113958401)
                  ·
                    refine ⟨2515666331015297335468801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3354221774687063113958401 2515666331015297335468801)
                    ·
                      refine ⟨1886749748261473001601601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2515666331015297335468801 1886749748261473001601601)
                      ·
                        rfl

theorem cell23_3674432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 6, 2, 2, 2].length) (baseStart_3674432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3674432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3674432 prefixEnd_3674432 := by exact prefixLift 3674432
  have htrace : WordTrace (prefixWord ++ tailWord_3674432) baseStart_3674432 baseEnd_3674432 := by
    simpa [prefixWord, tailWord_3674432, baseEnd_3674432] using wordTrace_append hprefix tailTrace_3674432
  have hstable : (prefixWord ++ tailWord_3674432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3674432).length < 2 ^ (prefixWord ++ tailWord_3674432).sum := by decide
  have hdescent : baseEnd_3674432 < baseStart_3674432 := by decide
  rcases family_descends (prefixWord ++ tailWord_3674432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3674468 : List Nat := [2, 3, 1, 1, 3, 1, 1, 3, 1, 7]
def baseStart_3674468 : Nat := 118140960795 + 3674468 * 2 ^ 59
def prefixEnd_3674468 : Nat := 4983230072969 + 3 ^ 40 * 3674468 * 2
def baseEnd_3674468 : Nat := 628922744521678286917145

theorem tailTrace_3674468 : CollatzResearch.WordTrace tailWord_3674468 prefixEnd_3674468 628922744521678286917145 := by
  unfold tailWord_3674468
  simp only [CollatzResearch.WordTrace]
  refine ⟨67009429026018730008884029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89345905368024973345178705 67009429026018730008884029)
  ·
    refine ⟨25128535884757023753331511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67009429026018730008884029 25128535884757023753331511)
    ·
      refine ⟨37692803827135535629997267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25128535884757023753331511 37692803827135535629997267)
      ·
        refine ⟨56539205740703303444995901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37692803827135535629997267 56539205740703303444995901)
        ·
          refine ⟨21202202152763738791873463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56539205740703303444995901 21202202152763738791873463)
          ·
            refine ⟨31803303229145608187810195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21202202152763738791873463 31803303229145608187810195)
            ·
              refine ⟨47704954843718412281715293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31803303229145608187810195 47704954843718412281715293)
              ·
                refine ⟨17889358066394404605643235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47704954843718412281715293 17889358066394404605643235)
                ·
                  refine ⟨26834037099591606908464853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17889358066394404605643235 26834037099591606908464853)
                  ·
                    refine ⟨628922744521678286917145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26834037099591606908464853 628922744521678286917145)
                    ·
                      rfl

theorem cell23_3674468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 3, 1, 7].length) (baseStart_3674468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3674468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3674468 prefixEnd_3674468 := by exact prefixLift 3674468
  have htrace : WordTrace (prefixWord ++ tailWord_3674468) baseStart_3674468 baseEnd_3674468 := by
    simpa [prefixWord, tailWord_3674468, baseEnd_3674468] using wordTrace_append hprefix tailTrace_3674468
  have hstable : (prefixWord ++ tailWord_3674468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3674468).length < 2 ^ (prefixWord ++ tailWord_3674468).sum := by decide
  have hdescent : baseEnd_3674468 < baseStart_3674468 := by decide
  rcases family_descends (prefixWord ++ tailWord_3674468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3674472 : List Nat := [2, 1, 4, 2, 2, 1, 3, 3, 5]
def baseStart_3674472 : Nat := 118140960795 + 3674472 * 2 ^ 59
def prefixEnd_3674472 : Nat := 4983230072969 + 3 ^ 40 * 3674472 * 2
def baseEnd_3674472 : Nat := 209641143054183649455713

theorem tailTrace_3674472 : CollatzResearch.WordTrace tailWord_3674472 prefixEnd_3674472 209641143054183649455713 := by
  unfold tailWord_3674472
  simp only [CollatzResearch.WordTrace]
  refine ⟨67009501972011484350456835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89346002629348645800609113 67009501972011484350456835)
  ·
    refine ⟨100514252958017226525685253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67009501972011484350456835 100514252958017226525685253)
    ·
      refine ⟨18846422429628229973565985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100514252958017226525685253 18846422429628229973565985)
      ·
        refine ⟨14134816822221172480174489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18846422429628229973565985 14134816822221172480174489)
        ·
          refine ⟨10601112616665879360130867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14134816822221172480174489 10601112616665879360130867)
          ·
            refine ⟨15901668924998819040196301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10601112616665879360130867 15901668924998819040196301)
            ·
              refine ⟨5963125846874557140073613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15901668924998819040196301 5963125846874557140073613)
              ·
                refine ⟨2236172192577958927527605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5963125846874557140073613 2236172192577958927527605)
                ·
                  refine ⟨209641143054183649455713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2236172192577958927527605 209641143054183649455713)
                  ·
                    rfl

theorem cell23_3674472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 3, 3, 5].length) (baseStart_3674472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3674472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3674472 prefixEnd_3674472 := by exact prefixLift 3674472
  have htrace : WordTrace (prefixWord ++ tailWord_3674472) baseStart_3674472 baseEnd_3674472 := by
    simpa [prefixWord, tailWord_3674472, baseEnd_3674472] using wordTrace_append hprefix tailTrace_3674472
  have hstable : (prefixWord ++ tailWord_3674472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3674472).length < 2 ^ (prefixWord ++ tailWord_3674472).sum := by decide
  have hdescent : baseEnd_3674472 < baseStart_3674472 := by decide
  rcases family_descends (prefixWord ++ tailWord_3674472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3674485 : List Nat := [1, 3, 4, 1, 2, 1, 1, 1, 4, 5]
def baseStart_3674485 : Nat := 118140960795 + 3674485 * 2 ^ 59
def prefixEnd_3674485 : Nat := 4983230072969 + 3 ^ 40 * 3674485 * 2
def baseEnd_3674485 : Nat := 628925654245387098079619

theorem tailTrace_3674485 : CollatzResearch.WordTrace tailWord_3674485 prefixEnd_3674485 628925654245387098079619 := by
  unfold tailWord_3674485
  simp only [CollatzResearch.WordTrace]
  refine ⟨134019478092975871921136909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89346318728650581280757939 134019478092975871921136909)
  ·
    refine ⟨50257304284865951970426341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134019478092975871921136909 50257304284865951970426341)
    ·
      refine ⟨9423244553412365994454939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50257304284865951970426341 9423244553412365994454939)
      ·
        refine ⟨14134866830118548991682409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9423244553412365994454939 14134866830118548991682409)
        ·
          refine ⟨10601150122588911743761807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14134866830118548991682409 10601150122588911743761807)
          ·
            refine ⟨15901725183883367615642711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10601150122588911743761807 15901725183883367615642711)
            ·
              refine ⟨23852587775825051423464067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15901725183883367615642711 23852587775825051423464067)
              ·
                refine ⟨35778881663737577135196101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23852587775825051423464067 35778881663737577135196101)
                ·
                  refine ⟨6708540311950795712849269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35778881663737577135196101 6708540311950795712849269)
                  ·
                    refine ⟨628925654245387098079619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6708540311950795712849269 628925654245387098079619)
                    ·
                      rfl

theorem cell23_3674485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 1, 4, 5].length) (baseStart_3674485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3674485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3674485 prefixEnd_3674485 := by exact prefixLift 3674485
  have htrace : WordTrace (prefixWord ++ tailWord_3674485) baseStart_3674485 baseEnd_3674485 := by
    simpa [prefixWord, tailWord_3674485, baseEnd_3674485] using wordTrace_append hprefix tailTrace_3674485
  have hstable : (prefixWord ++ tailWord_3674485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3674485).length < 2 ^ (prefixWord ++ tailWord_3674485).sum := by decide
  have hdescent : baseEnd_3674485 < baseStart_3674485 := by decide
  rcases family_descends (prefixWord ++ tailWord_3674485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3674522 : List Nat := [3, 1, 1, 4, 1, 3, 2, 1, 2, 1, 4]
def baseStart_3674522 : Nat := 118140960795 + 3674522 * 2 ^ 59
def prefixEnd_3674522 : Nat := 4983230072969 + 3 ^ 40 * 3674522 * 2
def baseEnd_3674522 : Nat := 1886795961520377649476187

theorem tailTrace_3674522 : CollatzResearch.WordTrace tailWord_3674522 prefixEnd_3674522 1886795961520377649476187 := by
  unfold tailWord_3674522
  simp only [CollatzResearch.WordTrace]
  refine ⟨33505206898460456810058455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89347218395894551493489213 33505206898460456810058455)
  ·
    refine ⟨50257810347690685215087683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33505206898460456810058455 50257810347690685215087683)
    ·
      refine ⟨75386715521536027822631525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50257810347690685215087683 75386715521536027822631525)
      ·
        refine ⟨14135009160288005216743411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75386715521536027822631525 14135009160288005216743411)
        ·
          refine ⟨21202513740432007825115117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14135009160288005216743411 21202513740432007825115117)
          ·
            refine ⟨7950942652662002934418169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21202513740432007825115117 7950942652662002934418169)
            ·
              refine ⟨5963206989496502200813627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7950942652662002934418169 5963206989496502200813627)
              ·
                refine ⟨8944810484244753301220441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5963206989496502200813627 8944810484244753301220441)
                ·
                  refine ⟨6708607863183564975915331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8944810484244753301220441 6708607863183564975915331)
                  ·
                    refine ⟨10062911794775347463872997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6708607863183564975915331 10062911794775347463872997)
                    ·
                      refine ⟨1886795961520377649476187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10062911794775347463872997 1886795961520377649476187)
                      ·
                        rfl

theorem cell23_3674522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 2, 1, 2, 1, 4].length) (baseStart_3674522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3674522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3674522 prefixEnd_3674522 := by exact prefixLift 3674522
  have htrace : WordTrace (prefixWord ++ tailWord_3674522) baseStart_3674522 baseEnd_3674522 := by
    simpa [prefixWord, tailWord_3674522, baseEnd_3674522] using wordTrace_append hprefix tailTrace_3674522
  have hstable : (prefixWord ++ tailWord_3674522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3674522).length < 2 ^ (prefixWord ++ tailWord_3674522).sum := by decide
  have hdescent : baseEnd_3674522 < baseStart_3674522 := by decide
  rcases family_descends (prefixWord ++ tailWord_3674522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3674545 : List Nat := [1, 2, 2, 4, 1, 2, 1, 4, 6]
def baseStart_3674545 : Nat := 118140960795 + 3674545 * 2 ^ 59
def prefixEnd_3674545 : Nat := 4983230072969 + 3 ^ 40 * 3674545 * 2
def baseEnd_3674545 : Nat := 209645307952825673276509

theorem tailTrace_3674545 : CollatzResearch.WordTrace tailWord_3674545 prefixEnd_3674545 209645307952825673276509 := by
  unfold tailWord_3674545
  simp only [CollatzResearch.WordTrace]
  refine ⟨134021666472758502168321089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89347777648505668112214059 134021666472758502168321089)
  ·
    refine ⟨100516249854568876626240817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134021666472758502168321089 100516249854568876626240817)
    ·
      refine ⟨75387187390926657469680613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100516249854568876626240817 75387187390926657469680613)
      ·
        refine ⟨14135097635798748275565115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75387187390926657469680613 14135097635798748275565115)
        ·
          refine ⟨21202646453698122413347673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14135097635798748275565115 21202646453698122413347673)
          ·
            refine ⟨15901984840273591810010755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21202646453698122413347673 15901984840273591810010755)
            ·
              refine ⟨23852977260410387715016133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15901984840273591810010755 23852977260410387715016133)
              ·
                refine ⟨4472433236326947696565525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23852977260410387715016133 4472433236326947696565525)
                ·
                  refine ⟨209645307952825673276509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4472433236326947696565525 209645307952825673276509)
                  ·
                    rfl

theorem cell23_3674545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 4, 6].length) (baseStart_3674545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3674545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3674545 prefixEnd_3674545 := by exact prefixLift 3674545
  have htrace : WordTrace (prefixWord ++ tailWord_3674545) baseStart_3674545 baseEnd_3674545 := by
    simpa [prefixWord, tailWord_3674545, baseEnd_3674545] using wordTrace_append hprefix tailTrace_3674545
  have hstable : (prefixWord ++ tailWord_3674545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3674545).length < 2 ^ (prefixWord ++ tailWord_3674545).sum := by decide
  have hdescent : baseEnd_3674545 < baseStart_3674545 := by decide
  rcases family_descends (prefixWord ++ tailWord_3674545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3674575 : List Nat := [1, 1, 2, 1, 1, 4, 1, 6, 1, 5]
def baseStart_3674575 : Nat := 118140960795 + 3674575 * 2 ^ 59
def prefixEnd_3674575 : Nat := 4983230072969 + 3 ^ 40 * 3674575 * 2
def baseEnd_3674575 : Nat := 628941058665021980704481

theorem tailTrace_3674575 : CollatzResearch.WordTrace tailWord_3674575 prefixEnd_3674575 628941058665021980704481 := by
  unfold tailWord_3674575
  simp only [CollatzResearch.WordTrace]
  refine ⟨134022760662649817291913179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89348507108433211527942119 134022760662649817291913179)
  ·
    refine ⟨201034140993974725937869769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134022760662649817291913179 201034140993974725937869769)
    ·
      refine ⟨150775605745481044453402327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201034140993974725937869769 150775605745481044453402327)
      ·
        refine ⟨226163408618221566680103491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150775605745481044453402327 226163408618221566680103491)
        ·
          refine ⟨339245112927332350020155237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226163408618221566680103491 339245112927332350020155237)
          ·
            refine ⟨63608458673874815628779107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 339245112927332350020155237 63608458673874815628779107)
            ·
              refine ⟨95412688010812223443168661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63608458673874815628779107 95412688010812223443168661)
              ·
                refine ⟨4472469750506822973898531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 95412688010812223443168661 4472469750506822973898531)
                ·
                  refine ⟨6708704625760234460847797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4472469750506822973898531 6708704625760234460847797)
                  ·
                    refine ⟨628941058665021980704481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6708704625760234460847797 628941058665021980704481)
                    ·
                      rfl

theorem cell23_3674575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 6, 1, 5].length) (baseStart_3674575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3674575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3674575 prefixEnd_3674575 := by exact prefixLift 3674575
  have htrace : WordTrace (prefixWord ++ tailWord_3674575) baseStart_3674575 baseEnd_3674575 := by
    simpa [prefixWord, tailWord_3674575, baseEnd_3674575] using wordTrace_append hprefix tailTrace_3674575
  have hstable : (prefixWord ++ tailWord_3674575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3674575).length < 2 ^ (prefixWord ++ tailWord_3674575).sum := by decide
  have hdescent : baseEnd_3674575 < baseStart_3674575 := by decide
  rcases family_descends (prefixWord ++ tailWord_3674575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3674606 : List Nat := [4, 1, 2, 1, 2, 2, 2, 4, 1, 1, 3]
def baseStart_3674606 : Nat := 118140960795 + 3674606 * 2 ^ 59
def prefixEnd_3674606 : Nat := 4983230072969 + 3 ^ 40 * 3674606 * 2
def baseEnd_3674606 : Nat := 1886839093895355320825801

theorem tailTrace_3674606 : CollatzResearch.WordTrace tailWord_3674606 prefixEnd_3674606 1886839093895355320825801 := by
  unfold tailWord_3674606
  simp only [CollatzResearch.WordTrace]
  refine ⟨16752986415692188698286459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89349260883691673057527781 16752986415692188698286459)
  ·
    refine ⟨25129479623538283047429689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16752986415692188698286459 25129479623538283047429689)
    ·
      refine ⟨18847109717653712285572267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25129479623538283047429689 18847109717653712285572267)
      ·
        refine ⟨28270664576480568428358401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18847109717653712285572267 28270664576480568428358401)
        ·
          refine ⟨21202998432360426321268801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28270664576480568428358401 21202998432360426321268801)
          ·
            refine ⟨15902248824270319740951601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21202998432360426321268801 15902248824270319740951601)
            ·
              refine ⟨11926686618202739805713701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15902248824270319740951601 11926686618202739805713701)
              ·
                refine ⟨2236253740913013713571319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11926686618202739805713701 2236253740913013713571319)
                ·
                  refine ⟨3354380611369520570356979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2236253740913013713571319 3354380611369520570356979)
                  ·
                    refine ⟨5031570917054280855535469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3354380611369520570356979 5031570917054280855535469)
                    ·
                      refine ⟨1886839093895355320825801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5031570917054280855535469 1886839093895355320825801)
                      ·
                        rfl

theorem cell23_3674606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 4, 1, 1, 3].length) (baseStart_3674606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3674606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3674606 prefixEnd_3674606 := by exact prefixLift 3674606
  have htrace : WordTrace (prefixWord ++ tailWord_3674606) baseStart_3674606 baseEnd_3674606 := by
    simpa [prefixWord, tailWord_3674606, baseEnd_3674606] using wordTrace_append hprefix tailTrace_3674606
  have hstable : (prefixWord ++ tailWord_3674606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3674606).length < 2 ^ (prefixWord ++ tailWord_3674606).sum := by decide
  have hdescent : baseEnd_3674606 < baseStart_3674606 := by decide
  rcases family_descends (prefixWord ++ tailWord_3674606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3674626 : List Nat := [3, 4, 1, 2, 2, 1, 2, 2, 1, 5]
def baseStart_3674626 : Nat := 118140960795 + 3674626 * 2 ^ 59
def prefixEnd_3674626 : Nat := 4983230072969 + 3 ^ 40 * 3674626 * 2
def baseEnd_3674626 : Nat := 628949787836148414191903

theorem tailTrace_3674626 : CollatzResearch.WordTrace tailWord_3674626 prefixEnd_3674626 628949787836148414191903 := by
  unfold tailWord_3674626
  simp only [CollatzResearch.WordTrace]
  refine ⟨33506155196366263250504933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89349747190310035334679821 33506155196366263250504933)
  ·
    refine ⟨6282404099318674359469675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33506155196366263250504933 6282404099318674359469675)
    ·
      refine ⟨9423606148978011539204513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6282404099318674359469675 9423606148978011539204513)
      ·
        refine ⟨7067704611733508654403385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9423606148978011539204513 7067704611733508654403385)
        ·
          refine ⟨5300778458800131490802539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7067704611733508654403385 5300778458800131490802539)
          ·
            refine ⟨7951167688200197236203809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5300778458800131490802539 7951167688200197236203809)
            ·
              refine ⟨5963375766150147927152857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7951167688200197236203809 5963375766150147927152857)
              ·
                refine ⟨4472531824612610945364643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5963375766150147927152857 4472531824612610945364643)
                ·
                  refine ⟨6708797736918916418046965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4472531824612610945364643 6708797736918916418046965)
                  ·
                    refine ⟨628949787836148414191903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6708797736918916418046965 628949787836148414191903)
                    ·
                      rfl

theorem cell23_3674626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 2, 2, 1, 5].length) (baseStart_3674626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3674626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3674626 prefixEnd_3674626 := by exact prefixLift 3674626
  have htrace : WordTrace (prefixWord ++ tailWord_3674626) baseStart_3674626 baseEnd_3674626 := by
    simpa [prefixWord, tailWord_3674626, baseEnd_3674626] using wordTrace_append hprefix tailTrace_3674626
  have hstable : (prefixWord ++ tailWord_3674626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3674626).length < 2 ^ (prefixWord ++ tailWord_3674626).sum := by decide
  have hdescent : baseEnd_3674626 < baseStart_3674626 := by decide
  rcases family_descends (prefixWord ++ tailWord_3674626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3674629 : List Nat := [1, 3, 1, 1, 2, 2, 4, 2, 3, 2, 2]
def baseStart_3674629 : Nat := 118140960795 + 3674629 * 2 ^ 59
def prefixEnd_3674629 : Nat := 4983230072969 + 3 ^ 40 * 3674629 * 2
def baseEnd_3674629 : Nat := 1886850903950408730838195

theorem tailTrace_3674629 : CollatzResearch.WordTrace tailWord_3674629 prefixEnd_3674629 1886850903950408730838195 := by
  unfold tailWord_3674629
  simp only [CollatzResearch.WordTrace]
  refine ⟨134024730204454184514378941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89349820136302789676252627 134024730204454184514378941)
  ·
    refine ⟨50259273826670319192892103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134024730204454184514378941 50259273826670319192892103)
    ·
      refine ⟨75388910740005478789338155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50259273826670319192892103 75388910740005478789338155)
      ·
        refine ⟨113083366110008218184007233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75388910740005478789338155 113083366110008218184007233)
        ·
          refine ⟨84812524582506163638005425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113083366110008218184007233 84812524582506163638005425)
          ·
            refine ⟨63609393436879622728504069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84812524582506163638005425 63609393436879622728504069)
            ·
              refine ⟨11926761269414929261594513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63609393436879622728504069 11926761269414929261594513)
              ·
                refine ⟨8945070952061196946195885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11926761269414929261594513 8945070952061196946195885)
                ·
                  refine ⟨3354401607022948854823457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8945070952061196946195885 3354401607022948854823457)
                  ·
                    refine ⟨2515801205267211641117593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3354401607022948854823457 2515801205267211641117593)
                    ·
                      refine ⟨1886850903950408730838195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2515801205267211641117593 1886850903950408730838195)
                      ·
                        rfl

theorem cell23_3674629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 2, 3, 2, 2].length) (baseStart_3674629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3674629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3674629 prefixEnd_3674629 := by exact prefixLift 3674629
  have htrace : WordTrace (prefixWord ++ tailWord_3674629) baseStart_3674629 baseEnd_3674629 := by
    simpa [prefixWord, tailWord_3674629, baseEnd_3674629] using wordTrace_append hprefix tailTrace_3674629
  have hstable : (prefixWord ++ tailWord_3674629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3674629).length < 2 ^ (prefixWord ++ tailWord_3674629).sum := by decide
  have hdescent : baseEnd_3674629 < baseStart_3674629 := by decide
  rcases family_descends (prefixWord ++ tailWord_3674629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3674635 : List Nat := [1, 1, 1, 1, 7, 2, 1, 9]
def baseStart_3674635 : Nat := 118140960795 + 3674635 * 2 ^ 59
def prefixEnd_3674635 : Nat := 4983230072969 + 3 ^ 40 * 3674635 * 2
def baseEnd_3674635 : Nat := 69883480919790211383821

theorem tailTrace_3674635 : CollatzResearch.WordTrace tailWord_3674635 prefixEnd_3674635 69883480919790211383821 := by
  unfold tailWord_3674635
  simp only [CollatzResearch.WordTrace]
  refine ⟨134024949042432447539097359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89349966028288298359398239 134024949042432447539097359)
  ·
    refine ⟨201037423563648671308646039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134024949042432447539097359 201037423563648671308646039)
    ·
      refine ⟨301556135345473006962969059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201037423563648671308646039 301556135345473006962969059)
      ·
        refine ⟨452334203018209510444453589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301556135345473006962969059 452334203018209510444453589)
        ·
          refine ⟨10601582883239285401041881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 452334203018209510444453589 10601582883239285401041881)
          ·
            refine ⟨7951187162429464050781411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10601582883239285401041881 7951187162429464050781411)
            ·
              refine ⟨11926780743644196076172117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7951187162429464050781411 11926780743644196076172117)
              ·
                refine ⟨69883480919790211383821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11926780743644196076172117 69883480919790211383821)
                ·
                  rfl

theorem cell23_3674635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 9].length) (baseStart_3674635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3674635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3674635 prefixEnd_3674635 := by exact prefixLift 3674635
  have htrace : WordTrace (prefixWord ++ tailWord_3674635) baseStart_3674635 baseEnd_3674635 := by
    simpa [prefixWord, tailWord_3674635, baseEnd_3674635] using wordTrace_append hprefix tailTrace_3674635
  have hstable : (prefixWord ++ tailWord_3674635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3674635).length < 2 ^ (prefixWord ++ tailWord_3674635).sum := by decide
  have hdescent : baseEnd_3674635 < baseStart_3674635 := by decide
  rcases family_descends (prefixWord ++ tailWord_3674635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3674679 : List Nat := [1, 1, 3, 1, 2, 3, 3, 3, 2, 1, 3]
def baseStart_3674679 : Nat := 118140960795 + 3674679 * 2 ^ 59
def prefixEnd_3674679 : Nat := 4983230072969 + 3 ^ 40 * 3674679 * 2
def baseEnd_3674679 : Nat := 1886876577983133535212965

theorem tailTrace_3674679 : CollatzResearch.WordTrace tailWord_3674679 prefixEnd_3674679 1886876577983133535212965 := by
  unfold tailWord_3674679
  simp only [CollatzResearch.WordTrace]
  refine ⟨134026553854273043053699091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89351035902848695369132727 134026553854273043053699091)
  ·
    refine ⟨201039830781409564580548637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134026553854273043053699091 201039830781409564580548637)
    ·
      refine ⟨75389936543028586717705739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201039830781409564580548637 75389936543028586717705739)
      ·
        refine ⟨113084904814542880076558609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75389936543028586717705739 113084904814542880076558609)
        ·
          refine ⟨84813678610907160057418957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113084904814542880076558609 84813678610907160057418957)
          ·
            refine ⟨31805129479090185021532109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84813678610907160057418957 31805129479090185021532109)
            ·
              refine ⟨11926923554658819383074541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31805129479090185021532109 11926923554658819383074541)
              ·
                refine ⟨4472596332997057268652953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11926923554658819383074541 4472596332997057268652953)
                ·
                  refine ⟨3354447249747792951489715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4472596332997057268652953 3354447249747792951489715)
                  ·
                    refine ⟨5031670874621689427234573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3354447249747792951489715 5031670874621689427234573)
                    ·
                      refine ⟨1886876577983133535212965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5031670874621689427234573 1886876577983133535212965)
                      ·
                        rfl

theorem cell23_3674679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 3, 2, 1, 3].length) (baseStart_3674679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3674679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3674679 prefixEnd_3674679 := by exact prefixLift 3674679
  have htrace : WordTrace (prefixWord ++ tailWord_3674679) baseStart_3674679 baseEnd_3674679 := by
    simpa [prefixWord, tailWord_3674679, baseEnd_3674679] using wordTrace_append hprefix tailTrace_3674679
  have hstable : (prefixWord ++ tailWord_3674679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3674679).length < 2 ^ (prefixWord ++ tailWord_3674679).sum := by decide
  have hdescent : baseEnd_3674679 < baseStart_3674679 := by decide
  rcases family_descends (prefixWord ++ tailWord_3674679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3674719 : List Nat := [1, 1, 2, 3, 1, 1, 1, 5, 4, 2, 2]
def baseStart_3674719 : Nat := 118140960795 + 3674719 * 2 ^ 59
def prefixEnd_3674719 : Nat := 4983230072969 + 3 ^ 40 * 3674719 * 2
def baseEnd_3674719 : Nat := 1886897117209313378712781

theorem tailTrace_3674719 : CollatzResearch.WordTrace tailWord_3674719 prefixEnd_3674719 1886897117209313378712781 := by
  unfold tailWord_3674719
  simp only [CollatzResearch.WordTrace]
  refine ⟨134028012774128129885155211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89352008516085419923436807 134028012774128129885155211)
  ·
    refine ⟨201042019161192194827732817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134028012774128129885155211 201042019161192194827732817)
    ·
      refine ⟨150781514370894146120799613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201042019161192194827732817 150781514370894146120799613)
      ·
        refine ⟨56543067889085304795299855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150781514370894146120799613 56543067889085304795299855)
        ·
          refine ⟨84814601833627957192949783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56543067889085304795299855 84814601833627957192949783)
          ·
            refine ⟨127221902750441935789424675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84814601833627957192949783 127221902750441935789424675)
            ·
              refine ⟨190832854125662903684137013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127221902750441935789424675 190832854125662903684137013)
              ·
                refine ⟨17890580074280897220387845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 190832854125662903684137013 17890580074280897220387845)
                ·
                  refine ⟨3354483763927668228822721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17890580074280897220387845 3354483763927668228822721)
                  ·
                    refine ⟨2515862822945751171617041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3354483763927668228822721 2515862822945751171617041)
                    ·
                      refine ⟨1886897117209313378712781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2515862822945751171617041 1886897117209313378712781)
                      ·
                        rfl

theorem cell23_3674719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 5, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 5, 4, 2, 2].length) (baseStart_3674719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3674719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3674719 prefixEnd_3674719 := by exact prefixLift 3674719
  have htrace : WordTrace (prefixWord ++ tailWord_3674719) baseStart_3674719 baseEnd_3674719 := by
    simpa [prefixWord, tailWord_3674719, baseEnd_3674719] using wordTrace_append hprefix tailTrace_3674719
  have hstable : (prefixWord ++ tailWord_3674719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3674719).length < 2 ^ (prefixWord ++ tailWord_3674719).sum := by decide
  have hdescent : baseEnd_3674719 < baseStart_3674719 := by decide
  rcases family_descends (prefixWord ++ tailWord_3674719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3674736 : List Nat := [2, 1, 1, 1, 7, 1, 2, 1, 1, 4, 2]
def baseStart_3674736 : Nat := 118140960795 + 3674736 * 2 ^ 59
def prefixEnd_3674736 : Nat := 4983230072969 + 3 ^ 40 * 3674736 * 2
def baseEnd_3674736 : Nat := 1886905846380439812200203

theorem tailTrace_3674736 : CollatzResearch.WordTrace tailWord_3674736 prefixEnd_3674736 1886905846380439812200203 := by
  unfold tailWord_3674736
  simp only [CollatzResearch.WordTrace]
  refine ⟨67014316407533270894262031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89352421876711027859016041 67014316407533270894262031)
  ·
    refine ⟨100521474611299906341393047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67014316407533270894262031 100521474611299906341393047)
    ·
      refine ⟨150782211916949859512089571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100521474611299906341393047 150782211916949859512089571)
      ·
        refine ⟨226173317875424789268134357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150782211916949859512089571 226173317875424789268134357)
        ·
          refine ⟨5300937137705268498471899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 226173317875424789268134357 5300937137705268498471899)
          ·
            refine ⟨7951405706557902747707849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5300937137705268498471899 7951405706557902747707849)
            ·
              refine ⟨5963554279918427060780887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7951405706557902747707849 5963554279918427060780887)
              ·
                refine ⟨8945331419877640591171331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5963554279918427060780887 8945331419877640591171331)
                ·
                  refine ⟨13417997129816460886756997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8945331419877640591171331 13417997129816460886756997)
                  ·
                    refine ⟨2515874461840586416266937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13417997129816460886756997 2515874461840586416266937)
                    ·
                      refine ⟨1886905846380439812200203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2515874461840586416266937 1886905846380439812200203)
                      ·
                        rfl

theorem cell23_3674736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 2, 1, 1, 4, 2].length) (baseStart_3674736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3674736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3674736 prefixEnd_3674736 := by exact prefixLift 3674736
  have htrace : WordTrace (prefixWord ++ tailWord_3674736) baseStart_3674736 baseEnd_3674736 := by
    simpa [prefixWord, tailWord_3674736, baseEnd_3674736] using wordTrace_append hprefix tailTrace_3674736
  have hstable : (prefixWord ++ tailWord_3674736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3674736).length < 2 ^ (prefixWord ++ tailWord_3674736).sum := by decide
  have hdescent : baseEnd_3674736 < baseStart_3674736 := by decide
  rcases family_descends (prefixWord ++ tailWord_3674736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3674759 : List Nat := [1, 1, 4, 2, 1, 2, 4, 3, 5]
def baseStart_3674759 : Nat := 118140960795 + 3674759 * 2 ^ 59
def prefixEnd_3674759 : Nat := 4983230072969 + 3 ^ 40 * 3674759 * 2
def baseEnd_3674759 : Nat := 209657517381721469134733

theorem tailTrace_3674759 : CollatzResearch.WordTrace tailWord_3674759 prefixEnd_3674759 209657517381721469134733 := by
  unfold tailWord_3674759
  simp only [CollatzResearch.WordTrace]
  refine ⟨134029471693983216716611331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89352981129322144477740887 134029471693983216716611331)
  ·
    refine ⟨201044207540974825074916997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134029471693983216716611331 201044207540974825074916997)
    ·
      refine ⟨37695788913932779701546937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 201044207540974825074916997 37695788913932779701546937)
      ·
        refine ⟨28271841685449584776160203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37695788913932779701546937 28271841685449584776160203)
        ·
          refine ⟨42407762528174377164240305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28271841685449584776160203 42407762528174377164240305)
          ·
            refine ⟨31805821896130782873180229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42407762528174377164240305 31805821896130782873180229)
            ·
              refine ⟨5963591605524521788721293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31805821896130782873180229 5963591605524521788721293)
              ·
                refine ⟨2236346852071695670770485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5963591605524521788721293 2236346852071695670770485)
                ·
                  refine ⟨209657517381721469134733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2236346852071695670770485 209657517381721469134733)
                  ·
                    rfl

theorem cell23_3674759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 4, 3, 5].length) (baseStart_3674759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3674759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3674759 prefixEnd_3674759 := by exact prefixLift 3674759
  have htrace : WordTrace (prefixWord ++ tailWord_3674759) baseStart_3674759 baseEnd_3674759 := by
    simpa [prefixWord, tailWord_3674759, baseEnd_3674759] using wordTrace_append hprefix tailTrace_3674759
  have hstable : (prefixWord ++ tailWord_3674759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3674759).length < 2 ^ (prefixWord ++ tailWord_3674759).sum := by decide
  have hdescent : baseEnd_3674759 < baseStart_3674759 := by decide
  rcases family_descends (prefixWord ++ tailWord_3674759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3674770 : List Nat := [3, 2, 3, 1, 2, 3, 1, 2, 2, 2, 2]
def baseStart_3674770 : Nat := 118140960795 + 3674770 * 2 ^ 59
def prefixEnd_3674770 : Nat := 4983230072969 + 3 ^ 40 * 3674770 * 2
def baseEnd_3674770 : Nat := 1886923304722692679175047

theorem tailTrace_3674770 : CollatzResearch.WordTrace tailWord_3674770 prefixEnd_3674770 1886923304722692679175047 := by
  unfold tailWord_3674770
  simp only [CollatzResearch.WordTrace]
  refine ⟨33507468224235841398815441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89353248597962243730174509 33507468224235841398815441)
  ·
    refine ⟨25130601168176881049111581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33507468224235841398815441 25130601168176881049111581)
    ·
      refine ⟨9423975438066330393416843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25130601168176881049111581 9423975438066330393416843)
      ·
        refine ⟨14135963157099495590125265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9423975438066330393416843 14135963157099495590125265)
        ·
          refine ⟨10601972367824621692593949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14135963157099495590125265 10601972367824621692593949)
          ·
            refine ⟨3975739637934233134722731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10601972367824621692593949 3975739637934233134722731)
            ·
              refine ⟨5963609456901349702084097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3975739637934233134722731 5963609456901349702084097)
              ·
                refine ⟨4472707092676012276563073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5963609456901349702084097 4472707092676012276563073)
                ·
                  refine ⟨3354530319507009207422305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4472707092676012276563073 3354530319507009207422305)
                  ·
                    refine ⟨2515897739630256905566729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3354530319507009207422305 2515897739630256905566729)
                    ·
                      refine ⟨1886923304722692679175047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2515897739630256905566729 1886923304722692679175047)
                      ·
                        rfl

theorem cell23_3674770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 1, 2, 2, 2, 2].length) (baseStart_3674770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3674770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3674770 prefixEnd_3674770 := by exact prefixLift 3674770
  have htrace : WordTrace (prefixWord ++ tailWord_3674770) baseStart_3674770 baseEnd_3674770 := by
    simpa [prefixWord, tailWord_3674770, baseEnd_3674770] using wordTrace_append hprefix tailTrace_3674770
  have hstable : (prefixWord ++ tailWord_3674770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3674770).length < 2 ^ (prefixWord ++ tailWord_3674770).sum := by decide
  have hdescent : baseEnd_3674770 < baseStart_3674770 := by decide
  rcases family_descends (prefixWord ++ tailWord_3674770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3674849 : List Nat := [1, 2, 3, 1, 4, 2, 1, 3, 6]
def baseStart_3674849 : Nat := 118140960795 + 3674849 * 2 ^ 59
def prefixEnd_3674849 : Nat := 4983230072969 + 3 ^ 40 * 3674849 * 2
def baseEnd_3674849 : Nat := 209662652188266430009687

theorem tailTrace_3674849 : CollatzResearch.WordTrace tailWord_3674849 prefixEnd_3674849 209662652188266430009687 := by
  unfold tailWord_3674849
  simp only [CollatzResearch.WordTrace]
  refine ⟨134032754263657162087387601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89355169509104774724925067 134032754263657162087387601)
  ·
    refine ⟨100524565697742871565540701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134032754263657162087387601 100524565697742871565540701)
    ·
      refine ⟨37696712136653576837077763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100524565697742871565540701 37696712136653576837077763)
      ·
        refine ⟨56545068204980365255616645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37696712136653576837077763 56545068204980365255616645)
        ·
          refine ⟨10602200288433818485428121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56545068204980365255616645 10602200288433818485428121)
          ·
            refine ⟨7951650216325363864071091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10602200288433818485428121 7951650216325363864071091)
            ·
              refine ⟨11927475324488045796106637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7951650216325363864071091 11927475324488045796106637)
              ·
                refine ⟨4472803246683017173539989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11927475324488045796106637 4472803246683017173539989)
                ·
                  refine ⟨209662652188266430009687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4472803246683017173539989 209662652188266430009687)
                  ·
                    rfl

theorem cell23_3674849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 3, 6].length) (baseStart_3674849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3674849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3674849 prefixEnd_3674849 := by exact prefixLift 3674849
  have htrace : WordTrace (prefixWord ++ tailWord_3674849) baseStart_3674849 baseEnd_3674849 := by
    simpa [prefixWord, tailWord_3674849, baseEnd_3674849] using wordTrace_append hprefix tailTrace_3674849
  have hstable : (prefixWord ++ tailWord_3674849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3674849).length < 2 ^ (prefixWord ++ tailWord_3674849).sum := by decide
  have hdescent : baseEnd_3674849 < baseStart_3674849 := by decide
  rcases family_descends (prefixWord ++ tailWord_3674849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3674859 : List Nat := [1, 1, 1, 1, 2, 4, 1, 3, 5, 1, 3]
def baseStart_3674859 : Nat := 118140960795 + 3674859 * 2 ^ 59
def prefixEnd_3674859 : Nat := 4983230072969 + 3 ^ 40 * 3674859 * 2
def baseEnd_3674859 : Nat := 1886969004500942830962137

theorem tailTrace_3674859 : CollatzResearch.WordTrace tailWord_3674859 prefixEnd_3674859 1886969004500942830962137 := by
  unfold tailWord_3674859
  simp only [CollatzResearch.WordTrace]
  refine ⟨134033118993620933795251631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89355412662413955863501087 134033118993620933795251631)
  ·
    refine ⟨201049678490431400692877447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134033118993620933795251631 201049678490431400692877447)
    ·
      refine ⟨301574517735647101039316171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201049678490431400692877447 301574517735647101039316171)
      ·
        refine ⟨452361776603470651558974257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301574517735647101039316171 452361776603470651558974257)
        ·
          refine ⟨339271332452602988669230693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 452361776603470651558974257 339271332452602988669230693)
          ·
            refine ⟨63613374834863060375480755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 339271332452602988669230693 63613374834863060375480755)
            ·
              refine ⟨95420062252294590563221133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63613374834863060375480755 95420062252294590563221133)
              ·
                refine ⟨35782523344610471461207925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95420062252294590563221133 35782523344610471461207925)
                ·
                  refine ⟨3354611563557231699488243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35782523344610471461207925 3354611563557231699488243)
                  ·
                    refine ⟨5031917345335847549232365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3354611563557231699488243 5031917345335847549232365)
                    ·
                      refine ⟨1886969004500942830962137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5031917345335847549232365 1886969004500942830962137)
                      ·
                        rfl

theorem cell23_3674859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 3, 5, 1, 3].length) (baseStart_3674859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3674859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3674859 prefixEnd_3674859 := by exact prefixLift 3674859
  have htrace : WordTrace (prefixWord ++ tailWord_3674859) baseStart_3674859 baseEnd_3674859 := by
    simpa [prefixWord, tailWord_3674859, baseEnd_3674859] using wordTrace_append hprefix tailTrace_3674859
  have hstable : (prefixWord ++ tailWord_3674859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3674859).length < 2 ^ (prefixWord ++ tailWord_3674859).sum := by decide
  have hdescent : baseEnd_3674859 < baseStart_3674859 := by decide
  rcases family_descends (prefixWord ++ tailWord_3674859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3674892 : List Nat := [2, 2, 1, 2, 2, 1, 1, 1, 5, 6]
def baseStart_3674892 : Nat := 118140960795 + 3674892 * 2 ^ 59
def prefixEnd_3674892 : Nat := 4983230072969 + 3 ^ 40 * 3674892 * 2
def baseEnd_3674892 : Nat := 628995316454180400616495

theorem tailTrace_3674892 : CollatzResearch.WordTrace tailWord_3674892 prefixEnd_3674892 628995316454180400616495 := by
  unfold tailWord_3674892
  simp only [CollatzResearch.WordTrace]
  refine ⟨67017161301250690215601465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89356215068334253620801953 67017161301250690215601465)
  ·
    refine ⟨50262870975938017661701099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67017161301250690215601465 50262870975938017661701099)
    ·
      refine ⟨75394306463907026492551649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50262870975938017661701099 75394306463907026492551649)
      ·
        refine ⟨56545729847930269869413737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75394306463907026492551649 56545729847930269869413737)
        ·
          refine ⟨42409297385947702402060303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56545729847930269869413737 42409297385947702402060303)
          ·
            refine ⟨63613946078921553603090455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42409297385947702402060303 63613946078921553603090455)
            ·
              refine ⟨95420919118382330404635683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63613946078921553603090455 95420919118382330404635683)
              ·
                refine ⟨143131378677573495606953525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95420919118382330404635683 143131378677573495606953525)
                ·
                  refine ⟨13418566751022515213151893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 143131378677573495606953525 13418566751022515213151893)
                  ·
                    refine ⟨628995316454180400616495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13418566751022515213151893 628995316454180400616495)
                    ·
                      rfl

theorem cell23_3674892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 5, 6].length) (baseStart_3674892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3674892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3674892 prefixEnd_3674892 := by exact prefixLift 3674892
  have htrace : WordTrace (prefixWord ++ tailWord_3674892) baseStart_3674892 baseEnd_3674892 := by
    simpa [prefixWord, tailWord_3674892, baseEnd_3674892] using wordTrace_append hprefix tailTrace_3674892
  have hstable : (prefixWord ++ tailWord_3674892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3674892).length < 2 ^ (prefixWord ++ tailWord_3674892).sum := by decide
  have hdescent : baseEnd_3674892 < baseStart_3674892 := by decide
  rcases family_descends (prefixWord ++ tailWord_3674892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3674926 : List Nat := [4, 1, 3, 2, 1, 1, 2, 2, 1, 6]
def baseStart_3674926 : Nat := 118140960795 + 3674926 * 2 ^ 59
def prefixEnd_3674926 : Nat := 4983230072969 + 3 ^ 40 * 3674926 * 2
def baseEnd_3674926 : Nat := 629001135901598022941443

theorem tailTrace_3674926 : CollatzResearch.WordTrace tailWord_3674926 prefixEnd_3674926 629001135901598022941443 := by
  unfold tailWord_3674926
  simp only [CollatzResearch.WordTrace]
  refine ⟨16754445335547275529742579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89357041789585469491960421 16754445335547275529742579)
  ·
    refine ⟨25131668003320913294613869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16754445335547275529742579 25131668003320913294613869)
    ·
      refine ⟨9424375501245342485480201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25131668003320913294613869 9424375501245342485480201)
      ·
        refine ⟨7068281625934006864110151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9424375501245342485480201 7068281625934006864110151)
        ·
          refine ⟨10602422438901010296165227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7068281625934006864110151 10602422438901010296165227)
          ·
            refine ⟨15903633658351515444247841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10602422438901010296165227 15903633658351515444247841)
            ·
              refine ⟨11927725243763636583185881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15903633658351515444247841 11927725243763636583185881)
              ·
                refine ⟨8945793932822727437389411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11927725243763636583185881 8945793932822727437389411)
                ·
                  refine ⟨13418690899234091156084117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8945793932822727437389411 13418690899234091156084117)
                  ·
                    refine ⟨629001135901598022941443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13418690899234091156084117 629001135901598022941443)
                    ·
                      rfl

theorem cell23_3674926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 2, 1, 6].length) (baseStart_3674926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3674926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3674926 prefixEnd_3674926 := by exact prefixLift 3674926
  have htrace : WordTrace (prefixWord ++ tailWord_3674926) baseStart_3674926 baseEnd_3674926 := by
    simpa [prefixWord, tailWord_3674926, baseEnd_3674926] using wordTrace_append hprefix tailTrace_3674926
  have hstable : (prefixWord ++ tailWord_3674926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3674926).length < 2 ^ (prefixWord ++ tailWord_3674926).sum := by decide
  have hdescent : baseEnd_3674926 < baseStart_3674926 := by decide
  rcases family_descends (prefixWord ++ tailWord_3674926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3674929 : List Nat := [1, 2, 2, 3, 2, 1, 1, 4, 1, 2, 4]
def baseStart_3674929 : Nat := 118140960795 + 3674929 * 2 ^ 59
def prefixEnd_3674929 : Nat := 4983230072969 + 3 ^ 40 * 3674929 * 2
def baseEnd_3674929 : Nat := 1887004948146757557086815

theorem tailTrace_3674929 : CollatzResearch.WordTrace tailWord_3674929 prefixEnd_3674929 1887004948146757557086815 := by
  unfold tailWord_3674929
  simp only [CollatzResearch.WordTrace]
  refine ⟨134035672103367335750299841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89357114735578223833533227 134035672103367335750299841)
  ·
    refine ⟨100526754077525501812724881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134035672103367335750299841 100526754077525501812724881)
    ·
      refine ⟨75395065558144126359543661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100526754077525501812724881 75395065558144126359543661)
      ·
        refine ⟨28273149584304047384828873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75395065558144126359543661 28273149584304047384828873)
        ·
          refine ⟨21204862188228035538621655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28273149584304047384828873 21204862188228035538621655)
          ·
            refine ⟨31807293282342053307932483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21204862188228035538621655 31807293282342053307932483)
            ·
              refine ⟨47710939923513079961898725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31807293282342053307932483 47710939923513079961898725)
              ·
                refine ⟨8945801235658702492856011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47710939923513079961898725 8945801235658702492856011)
                ·
                  refine ⟨13418701853488053739284017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8945801235658702492856011 13418701853488053739284017)
                  ·
                    refine ⟨10064026390116040304463013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13418701853488053739284017 10064026390116040304463013)
                    ·
                      refine ⟨1887004948146757557086815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10064026390116040304463013 1887004948146757557086815)
                      ·
                        rfl

theorem cell23_3674929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 4, 1, 2, 4].length) (baseStart_3674929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3674929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3674929 prefixEnd_3674929 := by exact prefixLift 3674929
  have htrace : WordTrace (prefixWord ++ tailWord_3674929) baseStart_3674929 baseEnd_3674929 := by
    simpa [prefixWord, tailWord_3674929, baseEnd_3674929] using wordTrace_append hprefix tailTrace_3674929
  have hstable : (prefixWord ++ tailWord_3674929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3674929).length < 2 ^ (prefixWord ++ tailWord_3674929).sum := by decide
  have hdescent : baseEnd_3674929 < baseStart_3674929 := by decide
  rcases family_descends (prefixWord ++ tailWord_3674929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3674933 : List Nat := [1, 3, 3, 1, 3, 1, 4, 1, 1, 1, 4]
def baseStart_3674933 : Nat := 118140960795 + 3674933 * 2 ^ 59
def prefixEnd_3674933 : Nat := 4983230072969 + 3 ^ 40 * 3674933 * 2
def baseEnd_3674933 : Nat := 1887007002069375541436797

theorem tailTrace_3674933 : CollatzResearch.WordTrace tailWord_3674933 prefixEnd_3674933 1887007002069375541436797 := by
  unfold tailWord_3674933
  simp only [CollatzResearch.WordTrace]
  refine ⟨134035817995352844433445453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89357211996901896288963635 134035817995352844433445453)
  ·
    refine ⟨50263431748257316662542045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134035817995352844433445453 50263431748257316662542045)
    ·
      refine ⟨18848786905596493748453267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50263431748257316662542045 18848786905596493748453267)
      ·
        refine ⟨28273180358394740622679901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18848786905596493748453267 28273180358394740622679901)
        ·
          refine ⟨10602442634398027733504963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28273180358394740622679901 10602442634398027733504963)
          ·
            refine ⟨15903663951597041600257445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10602442634398027733504963 15903663951597041600257445)
            ·
              refine ⟨2981936990924445300048271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15903663951597041600257445 2981936990924445300048271)
              ·
                refine ⟨4472905486386667950072407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2981936990924445300048271 4472905486386667950072407)
                ·
                  refine ⟨6709358229580001925108611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4472905486386667950072407 6709358229580001925108611)
                  ·
                    refine ⟨10064037344370002887662917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6709358229580001925108611 10064037344370002887662917)
                    ·
                      refine ⟨1887007002069375541436797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10064037344370002887662917 1887007002069375541436797)
                      ·
                        rfl

theorem cell23_3674933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 4, 1, 1, 1, 4].length) (baseStart_3674933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3674933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3674933 prefixEnd_3674933 := by exact prefixLift 3674933
  have htrace : WordTrace (prefixWord ++ tailWord_3674933) baseStart_3674933 baseEnd_3674933 := by
    simpa [prefixWord, tailWord_3674933, baseEnd_3674933] using wordTrace_append hprefix tailTrace_3674933
  have hstable : (prefixWord ++ tailWord_3674933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3674933).length < 2 ^ (prefixWord ++ tailWord_3674933).sum := by decide
  have hdescent : baseEnd_3674933 < baseStart_3674933 := by decide
  rcases family_descends (prefixWord ++ tailWord_3674933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3674936 : List Nat := [2, 1, 2, 1, 3, 2, 3, 3, 1, 2, 3]
def baseStart_3674936 : Nat := 118140960795 + 3674936 * 2 ^ 59
def prefixEnd_3674936 : Nat := 4983230072969 + 3 ^ 40 * 3674936 * 2
def baseEnd_3674936 : Nat := 1887008542511339029699283

theorem tailTrace_3674936 : CollatzResearch.WordTrace tailWord_3674936 prefixEnd_3674936 1887008542511339029699283 := by
  unfold tailWord_3674936
  simp only [CollatzResearch.WordTrace]
  refine ⟨67017963707170987972902331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89357284942894650630536441 67017963707170987972902331)
  ·
    refine ⟨100526945560756481959353497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67017963707170987972902331 100526945560756481959353497)
    ·
      refine ⟨75395209170567361469515123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100526945560756481959353497 75395209170567361469515123)
      ·
        refine ⟨113092813755851042204272685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75395209170567361469515123 113092813755851042204272685)
        ·
          refine ⟨42409805158444140826602257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113092813755851042204272685 42409805158444140826602257)
          ·
            refine ⟨31807353868833105619951693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42409805158444140826602257 31807353868833105619951693)
            ·
              refine ⟨11927757700812414607481885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31807353868833105619951693 11927757700812414607481885)
              ·
                refine ⟨4472909137804655477805707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11927757700812414607481885 4472909137804655477805707)
                ·
                  refine ⟨6709363706706983216708561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4472909137804655477805707 6709363706706983216708561)
                  ·
                    refine ⟨5032022780030237412531421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6709363706706983216708561 5032022780030237412531421)
                    ·
                      refine ⟨1887008542511339029699283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5032022780030237412531421 1887008542511339029699283)
                      ·
                        rfl

theorem cell23_3674936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 3, 1, 2, 3].length) (baseStart_3674936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3674936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3674936 prefixEnd_3674936 := by exact prefixLift 3674936
  have htrace : WordTrace (prefixWord ++ tailWord_3674936) baseStart_3674936 baseEnd_3674936 := by
    simpa [prefixWord, tailWord_3674936, baseEnd_3674936] using wordTrace_append hprefix tailTrace_3674936
  have hstable : (prefixWord ++ tailWord_3674936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3674936).length < 2 ^ (prefixWord ++ tailWord_3674936).sum := by decide
  have hdescent : baseEnd_3674936 < baseStart_3674936 := by decide
  rcases family_descends (prefixWord ++ tailWord_3674936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3674943 : List Nat := [1, 1, 2, 2, 5, 3, 1, 2, 2, 4]
def baseStart_3674943 : Nat := 118140960795 + 3674943 * 2 ^ 59
def prefixEnd_3674943 : Nat := 4983230072969 + 3 ^ 40 * 3674943 * 2
def baseEnd_3674943 : Nat := 629004045625306834103917

theorem tailTrace_3674943 : CollatzResearch.WordTrace tailWord_3674943 prefixEnd_3674943 629004045625306834103917 := by
  unfold tailWord_3674943
  simp only [CollatzResearch.WordTrace]
  refine ⟨134036182725316616141309483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89357455150211077427539655 134036182725316616141309483)
  ·
    refine ⟨201054274087974924211964225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134036182725316616141309483 201054274087974924211964225)
    ·
      refine ⟨150790705565981193158973169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201054274087974924211964225 150790705565981193158973169)
      ·
        refine ⟨113093029174485894869229877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150790705565981193158973169 113093029174485894869229877)
        ·
          refine ⟨10602471485108052643990301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 113093029174485894869229877 10602471485108052643990301)
          ·
            refine ⟨3975926806915519741496363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10602471485108052643990301 3975926806915519741496363)
            ·
              refine ⟨5963890210373279612244545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3975926806915519741496363 5963890210373279612244545)
              ·
                refine ⟨4472917657779959709183409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5963890210373279612244545 4472917657779959709183409)
                ·
                  refine ⟨3354688243334969781887557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4472917657779959709183409 3354688243334969781887557)
                  ·
                    refine ⟨629004045625306834103917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3354688243334969781887557 629004045625306834103917)
                    ·
                      rfl

theorem cell23_3674943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 1, 2, 2, 4].length) (baseStart_3674943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3674943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3674943 prefixEnd_3674943 := by exact prefixLift 3674943
  have htrace : WordTrace (prefixWord ++ tailWord_3674943) baseStart_3674943 baseEnd_3674943 := by
    simpa [prefixWord, tailWord_3674943, baseEnd_3674943] using wordTrace_append hprefix tailTrace_3674943
  have hstable : (prefixWord ++ tailWord_3674943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3674943).length < 2 ^ (prefixWord ++ tailWord_3674943).sum := by decide
  have hdescent : baseEnd_3674943 < baseStart_3674943 := by decide
  rcases family_descends (prefixWord ++ tailWord_3674943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3674979 : List Nat := [1, 1, 1, 5, 3, 1, 1, 1, 2, 2, 5]
def baseStart_3674979 : Nat := 118140960795 + 3674979 * 2 ^ 59
def prefixEnd_3674979 : Nat := 4983230072969 + 3 ^ 40 * 3674979 * 2
def baseEnd_3674979 : Nat := 1887030622179482361461585

theorem tailTrace_3674979 : CollatzResearch.WordTrace tailWord_3674979 prefixEnd_3674979 1887030622179482361461585 := by
  unfold tailWord_3674979
  simp only [CollatzResearch.WordTrace]
  refine ⟨134037495753186194289619991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89358330502124129526413327 134037495753186194289619991)
  ·
    refine ⟨201056243629779291434429987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134037495753186194289619991 201056243629779291434429987)
    ·
      refine ⟨301584365444668937151644981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201056243629779291434429987 301584365444668937151644981)
      ·
        refine ⟨28273534260437712857966717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 301584365444668937151644981 28273534260437712857966717)
        ·
          refine ⟨10602575347664142321737519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28273534260437712857966717 10602575347664142321737519)
          ·
            refine ⟨15903863021496213482606279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10602575347664142321737519 15903863021496213482606279)
            ·
              refine ⟨23855794532244320223909419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15903863021496213482606279 23855794532244320223909419)
              ·
                refine ⟨35783691798366480335864129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23855794532244320223909419 35783691798366480335864129)
                ·
                  refine ⟨26837768848774860251898097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35783691798366480335864129 26837768848774860251898097)
                  ·
                    refine ⟨20128326636581145188923573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26837768848774860251898097 20128326636581145188923573)
                    ·
                      refine ⟨1887030622179482361461585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20128326636581145188923573 1887030622179482361461585)
                      ·
                        rfl

theorem cell23_3674979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 1, 2, 2, 5].length) (baseStart_3674979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3674979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3674979 prefixEnd_3674979 := by exact prefixLift 3674979
  have htrace : WordTrace (prefixWord ++ tailWord_3674979) baseStart_3674979 baseEnd_3674979 := by
    simpa [prefixWord, tailWord_3674979, baseEnd_3674979] using wordTrace_append hprefix tailTrace_3674979
  have hstable : (prefixWord ++ tailWord_3674979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3674979).length < 2 ^ (prefixWord ++ tailWord_3674979).sum := by decide
  have hdescent : baseEnd_3674979 < baseStart_3674979 := by decide
  rcases family_descends (prefixWord ++ tailWord_3674979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3674989 : List Nat := [1, 5, 1, 1, 1, 1, 1, 2, 1, 5, 4]
def baseStart_3674989 : Nat := 118140960795 + 3674989 * 2 ^ 59
def prefixEnd_3674989 : Nat := 4983230072969 + 3 ^ 40 * 3674989 * 2
def baseEnd_3674989 : Nat := 1887035756986027322336539

theorem tailTrace_3674989 : CollatzResearch.WordTrace tailWord_3674989 prefixEnd_3674989 1887035756986027322336539 := by
  unfold tailWord_3674989
  simp only [CollatzResearch.WordTrace]
  refine ⟨134037860483149965997484021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89358573655433310664989347 134037860483149965997484021)
  ·
    refine ⟨12566049420295309312264127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 134037860483149965997484021 12566049420295309312264127)
    ·
      refine ⟨18849074130442963968396191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12566049420295309312264127 18849074130442963968396191)
      ·
        refine ⟨28273611195664445952594287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18849074130442963968396191 28273611195664445952594287)
        ·
          refine ⟨42410416793496668928891431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28273611195664445952594287 42410416793496668928891431)
          ·
            refine ⟨63615625190245003393337147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42410416793496668928891431 63615625190245003393337147)
            ·
              refine ⟨95423437785367505090005721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63615625190245003393337147 95423437785367505090005721)
              ·
                refine ⟨71567578339025628817504291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95423437785367505090005721 71567578339025628817504291)
                ·
                  refine ⟨107351367508538443226256437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71567578339025628817504291 107351367508538443226256437)
                  ·
                    refine ⟨10064190703925479052461541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 107351367508538443226256437 10064190703925479052461541)
                    ·
                      refine ⟨1887035756986027322336539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10064190703925479052461541 1887035756986027322336539)
                      ·
                        rfl

theorem cell23_3674989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 2, 1, 5, 4].length) (baseStart_3674989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3674989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3674989 prefixEnd_3674989 := by exact prefixLift 3674989
  have htrace : WordTrace (prefixWord ++ tailWord_3674989) baseStart_3674989 baseEnd_3674989 := by
    simpa [prefixWord, tailWord_3674989, baseEnd_3674989] using wordTrace_append hprefix tailTrace_3674989
  have hstable : (prefixWord ++ tailWord_3674989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3674989).length < 2 ^ (prefixWord ++ tailWord_3674989).sum := by decide
  have hdescent : baseEnd_3674989 < baseStart_3674989 := by decide
  rcases family_descends (prefixWord ++ tailWord_3674989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3674993 : List Nat := [1, 2, 2, 2, 1, 4, 2, 3, 1, 3, 2]
def baseStart_3674993 : Nat := 118140960795 + 3674993 * 2 ^ 59
def prefixEnd_3674993 : Nat := 4983230072969 + 3 ^ 40 * 3674993 * 2
def baseEnd_3674993 : Nat := 1887037810908645306686521

theorem tailTrace_3674993 : CollatzResearch.WordTrace tailWord_3674993 prefixEnd_3674993 1887037810908645306686521 := by
  unfold tailWord_3674993
  simp only [CollatzResearch.WordTrace]
  refine ⟨134038006375135474680629633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89358670916756983120419755 134038006375135474680629633)
  ·
    refine ⟨100528504781351606010472225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134038006375135474680629633 100528504781351606010472225)
    ·
      refine ⟨75396378586013704507854169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100528504781351606010472225 75396378586013704507854169)
      ·
        refine ⟨56547283939510278380890627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75396378586013704507854169 56547283939510278380890627)
        ·
          refine ⟨84820925909265417571335941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56547283939510278380890627 84820925909265417571335941)
          ·
            refine ⟨15903923607987265794625489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84820925909265417571335941 15903923607987265794625489)
            ·
              refine ⟨11927942705990449345969117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15903923607987265794625489 11927942705990449345969117)
              ·
                refine ⟨4472978514746418504738419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11927942705990449345969117 4472978514746418504738419)
                ·
                  refine ⟨6709467772119627757107629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4472978514746418504738419 6709467772119627757107629)
                  ·
                    refine ⟨2516050414544860408915361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6709467772119627757107629 2516050414544860408915361)
                    ·
                      refine ⟨1887037810908645306686521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2516050414544860408915361 1887037810908645306686521)
                      ·
                        rfl

theorem cell23_3674993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 3, 1, 3, 2].length) (baseStart_3674993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3674993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3674993 prefixEnd_3674993 := by exact prefixLift 3674993
  have htrace : WordTrace (prefixWord ++ tailWord_3674993) baseStart_3674993 baseEnd_3674993 := by
    simpa [prefixWord, tailWord_3674993, baseEnd_3674993] using wordTrace_append hprefix tailTrace_3674993
  have hstable : (prefixWord ++ tailWord_3674993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3674993).length < 2 ^ (prefixWord ++ tailWord_3674993).sum := by decide
  have hdescent : baseEnd_3674993 < baseStart_3674993 := by decide
  rcases family_descends (prefixWord ++ tailWord_3674993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3675019 : List Nat := [1, 1, 1, 1, 4, 2, 2, 3, 2, 2, 4]
def baseStart_3675019 : Nat := 118140960795 + 3675019 * 2 ^ 59
def prefixEnd_3675019 : Nat := 4983230072969 + 3 ^ 40 * 3675019 * 2
def baseEnd_3675019 : Nat := 1887051161405662204961401

theorem tailTrace_3675019 : CollatzResearch.WordTrace tailWord_3675019 prefixEnd_3675019 1887051161405662204961401 := by
  unfold tailWord_3675019
  simp only [CollatzResearch.WordTrace]
  refine ⟨134038954673041281121076111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89359303115360854080717407 134038954673041281121076111)
  ·
    refine ⟨201058432009561921681614167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134038954673041281121076111 201058432009561921681614167)
    ·
      refine ⟨301587648014342882522421251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201058432009561921681614167 301587648014342882522421251)
      ·
        refine ⟨452381472021514323783631877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301587648014342882522421251 452381472021514323783631877)
        ·
          refine ⟨84821526004033935709430977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 452381472021514323783631877 84821526004033935709430977)
          ·
            refine ⟨63616144503025451782073233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84821526004033935709430977 63616144503025451782073233)
            ·
              refine ⟨47712108377269088836554925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63616144503025451782073233 47712108377269088836554925)
              ·
                refine ⟨17892040641475908313708097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47712108377269088836554925 17892040641475908313708097)
                ·
                  refine ⟨13419030481106931235281073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17892040641475908313708097 13419030481106931235281073)
                  ·
                    refine ⟨10064272860830198426460805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13419030481106931235281073 10064272860830198426460805)
                    ·
                      refine ⟨1887051161405662204961401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10064272860830198426460805 1887051161405662204961401)
                      ·
                        rfl

theorem cell23_3675019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 3, 2, 2, 4].length) (baseStart_3675019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3675019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3675019 prefixEnd_3675019 := by exact prefixLift 3675019
  have htrace : WordTrace (prefixWord ++ tailWord_3675019) baseStart_3675019 baseEnd_3675019 := by
    simpa [prefixWord, tailWord_3675019, baseEnd_3675019] using wordTrace_append hprefix tailTrace_3675019
  have hstable : (prefixWord ++ tailWord_3675019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3675019).length < 2 ^ (prefixWord ++ tailWord_3675019).sum := by decide
  have hdescent : baseEnd_3675019 < baseStart_3675019 := by decide
  rcases family_descends (prefixWord ++ tailWord_3675019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3675057 : List Nat := [1, 2, 2, 4, 3, 1, 2, 2, 2, 2, 2]
def baseStart_3675057 : Nat := 118140960795 + 3675057 * 2 ^ 59
def prefixEnd_3675057 : Nat := 4983230072969 + 3 ^ 40 * 3675057 * 2
def baseEnd_3675057 : Nat := 1887070673670533056286227

theorem tailTrace_3675057 : CollatzResearch.WordTrace tailWord_3675057 prefixEnd_3675057 1887070673670533056286227 := by
  unfold tailWord_3675057
  simp only [CollatzResearch.WordTrace]
  refine ⟨134040340646903613610959425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89360227097935742407306283 134040340646903613610959425)
  ·
    refine ⟨100530255485177710208219569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134040340646903613610959425 100530255485177710208219569)
    ·
      refine ⟨75397691613883282656164677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100530255485177710208219569 75397691613883282656164677)
      ·
        refine ⟨14137067177603115498030877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75397691613883282656164677 14137067177603115498030877)
        ·
          refine ⟨5301400191601168311761579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14137067177603115498030877 5301400191601168311761579)
          ·
            refine ⟨7952100287401752467642369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5301400191601168311761579 7952100287401752467642369)
            ·
              refine ⟨5964075215551314350731777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7952100287401752467642369 5964075215551314350731777)
              ·
                refine ⟨4473056411663485763048833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5964075215551314350731777 4473056411663485763048833)
                ·
                  refine ⟨3354792308747614322286625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4473056411663485763048833 3354792308747614322286625)
                  ·
                    refine ⟨2516094231560710741714969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3354792308747614322286625 2516094231560710741714969)
                    ·
                      refine ⟨1887070673670533056286227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2516094231560710741714969 1887070673670533056286227)
                      ·
                        rfl

theorem cell23_3675057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 2, 2, 2, 2, 2].length) (baseStart_3675057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3675057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3675057 prefixEnd_3675057 := by exact prefixLift 3675057
  have htrace : WordTrace (prefixWord ++ tailWord_3675057) baseStart_3675057 baseEnd_3675057 := by
    simpa [prefixWord, tailWord_3675057, baseEnd_3675057] using wordTrace_append hprefix tailTrace_3675057
  have hstable : (prefixWord ++ tailWord_3675057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3675057).length < 2 ^ (prefixWord ++ tailWord_3675057).sum := by decide
  have hdescent : baseEnd_3675057 < baseStart_3675057 := by decide
  rcases family_descends (prefixWord ++ tailWord_3675057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3675059 : List Nat := [1, 1, 1, 2, 3, 1, 2, 3, 4, 5]
def baseStart_3675059 : Nat := 118140960795 + 3675059 * 2 ^ 59
def prefixEnd_3675059 : Nat := 4983230072969 + 3 ^ 40 * 3675059 * 2
def baseEnd_3675059 : Nat := 629023900210614016153739

theorem tailTrace_3675059 : CollatzResearch.WordTrace tailWord_3675059 prefixEnd_3675059 629023900210614016153739 := by
  unfold tailWord_3675059
  simp only [CollatzResearch.WordTrace]
  refine ⟨134040413592896367952532231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89360275728597578635021487 134040413592896367952532231)
  ·
    refine ⟨201060620389344551928798347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134040413592896367952532231 201060620389344551928798347)
    ·
      refine ⟨301590930584016827893197521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201060620389344551928798347 301590930584016827893197521)
      ·
        refine ⟨226193197938012620919898141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 301590930584016827893197521 226193197938012620919898141)
        ·
          refine ⟨84822449226754732844961803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 226193197938012620919898141 84822449226754732844961803)
          ·
            refine ⟨127233673840132099267442705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84822449226754732844961803 127233673840132099267442705)
            ·
              refine ⟨95425255380099074450582029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127233673840132099267442705 95425255380099074450582029)
              ·
                refine ⟨35784470767537152918968261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95425255380099074450582029 35784470767537152918968261)
                ·
                  refine ⟨6709588268913216172306549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35784470767537152918968261 6709588268913216172306549)
                  ·
                    refine ⟨629023900210614016153739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6709588268913216172306549 629023900210614016153739)
                    ·
                      rfl

theorem cell23_3675059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 3, 4, 5].length) (baseStart_3675059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3675059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3675059 prefixEnd_3675059 := by exact prefixLift 3675059
  have htrace : WordTrace (prefixWord ++ tailWord_3675059) baseStart_3675059 baseEnd_3675059 := by
    simpa [prefixWord, tailWord_3675059, baseEnd_3675059] using wordTrace_append hprefix tailTrace_3675059
  have hstable : (prefixWord ++ tailWord_3675059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3675059).length < 2 ^ (prefixWord ++ tailWord_3675059).sum := by decide
  have hdescent : baseEnd_3675059 < baseStart_3675059 := by decide
  rcases family_descends (prefixWord ++ tailWord_3675059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3675063 : List Nat := [1, 1, 3, 1, 3, 1, 6, 2, 5]
def baseStart_3675063 : Nat := 118140960795 + 3675063 * 2 ^ 59
def prefixEnd_3675063 : Nat := 4983230072969 + 3 ^ 40 * 3675063 * 2
def baseEnd_3675063 : Nat := 209674861617162225867911

theorem tailTrace_3675063 : CollatzResearch.WordTrace tailWord_3675063 prefixEnd_3675063 209674861617162225867911 := by
  unfold tailWord_3675063
  simp only [CollatzResearch.WordTrace]
  refine ⟨134040559484881876635677843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89360372989921251090451895 134040559484881876635677843)
  ·
    refine ⟨201060839227322814953516765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134040559484881876635677843 201060839227322814953516765)
    ·
      refine ⟨75397814710246055607568787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201060839227322814953516765 75397814710246055607568787)
      ·
        refine ⟨113096722065369083411353181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75397814710246055607568787 113096722065369083411353181)
        ·
          refine ⟨42411270774513406279257443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113096722065369083411353181 42411270774513406279257443)
          ·
            refine ⟨63616906161770109418886165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42411270774513406279257443 63616906161770109418886165)
            ·
              refine ⟨2982042476332973879010289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 63616906161770109418886165 2982042476332973879010289)
              ·
                refine ⟨2236531857249730409257717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2982042476332973879010289 2236531857249730409257717)
                ·
                  refine ⟨209674861617162225867911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2236531857249730409257717 209674861617162225867911)
                  ·
                    rfl

theorem cell23_3675063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 6, 2, 5].length) (baseStart_3675063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3675063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3675063 prefixEnd_3675063 := by exact prefixLift 3675063
  have htrace : WordTrace (prefixWord ++ tailWord_3675063) baseStart_3675063 baseEnd_3675063 := by
    simpa [prefixWord, tailWord_3675063, baseEnd_3675063] using wordTrace_append hprefix tailTrace_3675063
  have hstable : (prefixWord ++ tailWord_3675063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3675063).length < 2 ^ (prefixWord ++ tailWord_3675063).sum := by decide
  have hdescent : baseEnd_3675063 < baseStart_3675063 := by decide
  rcases family_descends (prefixWord ++ tailWord_3675063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3675066 : List Nat := [3, 1, 1, 1, 2, 1, 3, 1, 1, 7, 2]
def baseStart_3675066 : Nat := 118140960795 + 3675066 * 2 ^ 59
def prefixEnd_3675066 : Nat := 4983230072969 + 3 ^ 40 * 3675066 * 2
def baseEnd_3675066 : Nat := 1887075294996423521073685

theorem tailTrace_3675066 : CollatzResearch.WordTrace tailWord_3675066 prefixEnd_3675066 1887075294996423521073685 := by
  unfold tailWord_3675066
  simp only [CollatzResearch.WordTrace]
  refine ⟨33510167225967752037009263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89360445935914005432024701 33510167225967752037009263)
  ·
    refine ⟨50265250838951628055513895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33510167225967752037009263 50265250838951628055513895)
    ·
      refine ⟨75397876258427442083270843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50265250838951628055513895 75397876258427442083270843)
      ·
        refine ⟨113096814387641163124906265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75397876258427442083270843 113096814387641163124906265)
        ·
          refine ⟨84822610790730872343679699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113096814387641163124906265 84822610790730872343679699)
          ·
            refine ⟨127233916186096308515519549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84822610790730872343679699 127233916186096308515519549)
            ·
              refine ⟨47712718569786115693319831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127233916186096308515519549 47712718569786115693319831)
              ·
                refine ⟨71569077854679173539979747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47712718569786115693319831 71569077854679173539979747)
                ·
                  refine ⟨107353616782018760309969621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71569077854679173539979747 107353616782018760309969621)
                  ·
                    refine ⟨2516100393328564694764913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 107353616782018760309969621 2516100393328564694764913)
                    ·
                      refine ⟨1887075294996423521073685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2516100393328564694764913 1887075294996423521073685)
                      ·
                        rfl

theorem cell23_3675066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 1, 1, 7, 2].length) (baseStart_3675066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3675066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3675066 prefixEnd_3675066 := by exact prefixLift 3675066
  have htrace : WordTrace (prefixWord ++ tailWord_3675066) baseStart_3675066 baseEnd_3675066 := by
    simpa [prefixWord, tailWord_3675066, baseEnd_3675066] using wordTrace_append hprefix tailTrace_3675066
  have hstable : (prefixWord ++ tailWord_3675066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3675066).length < 2 ^ (prefixWord ++ tailWord_3675066).sum := by decide
  have hdescent : baseEnd_3675066 < baseStart_3675066 := by decide
  rcases family_descends (prefixWord ++ tailWord_3675066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3675096 : List Nat := [2, 1, 2, 2, 2, 4, 1, 1, 1, 3, 4]
def baseStart_3675096 : Nat := 118140960795 + 3675096 * 2 ^ 59
def prefixEnd_3675096 : Nat := 4983230072969 + 3 ^ 40 * 3675096 * 2
def baseEnd_3675096 : Nat := 1887090699416058403698547

theorem tailTrace_3675096 : CollatzResearch.WordTrace tailWord_3675096 prefixEnd_3675096 1887090699416058403698547 := by
  unfold tailWord_3675096
  simp only [CollatzResearch.WordTrace]
  refine ⟨67020881546881161635814571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89361175395841548847752761 67020881546881161635814571)
  ·
    refine ⟨100531322320321742453721857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67020881546881161635814571 100531322320321742453721857)
    ·
      refine ⟨75398491740241306840291393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100531322320321742453721857 75398491740241306840291393)
      ·
        refine ⟨56548868805180980130218545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75398491740241306840291393 56548868805180980130218545)
        ·
          refine ⟨42411651603885735097663909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56548868805180980130218545 42411651603885735097663909)
          ·
            refine ⟨7952184675728575330811983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42411651603885735097663909 7952184675728575330811983)
            ·
              refine ⟨11928277013592862996217975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7952184675728575330811983 11928277013592862996217975)
              ·
                refine ⟨17892415520389294494326963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11928277013592862996217975 17892415520389294494326963)
                ·
                  refine ⟨26838623280583941741490445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17892415520389294494326963 26838623280583941741490445)
                  ·
                    refine ⟨10064483730218978153058917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26838623280583941741490445 10064483730218978153058917)
                    ·
                      refine ⟨1887090699416058403698547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10064483730218978153058917 1887090699416058403698547)
                      ·
                        rfl

theorem cell23_3675096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 1, 1, 3, 4].length) (baseStart_3675096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3675096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3675096 prefixEnd_3675096 := by exact prefixLift 3675096
  have htrace : WordTrace (prefixWord ++ tailWord_3675096) baseStart_3675096 baseEnd_3675096 := by
    simpa [prefixWord, tailWord_3675096, baseEnd_3675096] using wordTrace_append hprefix tailTrace_3675096
  have hstable : (prefixWord ++ tailWord_3675096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3675096).length < 2 ^ (prefixWord ++ tailWord_3675096).sum := by decide
  have hdescent : baseEnd_3675096 < baseStart_3675096 := by decide
  rcases family_descends (prefixWord ++ tailWord_3675096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3675157 : List Nat := [1, 3, 2, 1, 4, 3, 1, 3, 1, 4]
def baseStart_3675157 : Nat := 118140960795 + 3675157 * 2 ^ 59
def prefixEnd_3675157 : Nat := 4983230072969 + 3 ^ 40 * 3675157 * 2
def baseEnd_3675157 : Nat := 629040673911994221678589

theorem tailTrace_3675157 : CollatzResearch.WordTrace tailWord_3675157 prefixEnd_3675157 629040673911994221678589 := by
  unfold tailWord_3675157
  simp only [CollatzResearch.WordTrace]
  refine ⟨134043987946541330689599725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89362658631027553793066483 134043987946541330689599725)
  ·
    refine ⟨50266495479952999008599897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134043987946541330689599725 50266495479952999008599897)
    ·
      refine ⟨37699871609964749256449923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50266495479952999008599897 37699871609964749256449923)
      ·
        refine ⟨56549807414947123884674885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37699871609964749256449923 56549807414947123884674885)
        ·
          refine ⟨10603088890302585728376541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56549807414947123884674885 10603088890302585728376541)
          ·
            refine ⟨3976158333863469648141203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10603088890302585728376541 3976158333863469648141203)
            ·
              refine ⟨5964237500795204472211805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3976158333863469648141203 5964237500795204472211805)
              ·
                refine ⟨2236589062798201677079427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5964237500795204472211805 2236589062798201677079427)
                ·
                  refine ⟨3354883594197302515619141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2236589062798201677079427 3354883594197302515619141)
                  ·
                    refine ⟨629040673911994221678589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3354883594197302515619141 629040673911994221678589)
                    ·
                      rfl

theorem cell23_3675157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 1, 3, 1, 4].length) (baseStart_3675157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3675157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3675157 prefixEnd_3675157 := by exact prefixLift 3675157
  have htrace : WordTrace (prefixWord ++ tailWord_3675157) baseStart_3675157 baseEnd_3675157 := by
    simpa [prefixWord, tailWord_3675157, baseEnd_3675157] using wordTrace_append hprefix tailTrace_3675157
  have hstable : (prefixWord ++ tailWord_3675157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3675157).length < 2 ^ (prefixWord ++ tailWord_3675157).sum := by decide
  have hdescent : baseEnd_3675157 < baseStart_3675157 := by decide
  rcases family_descends (prefixWord ++ tailWord_3675157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3675213 : List Nat := [1, 6, 1, 1, 1, 2, 1, 1, 3, 6]
def baseStart_3675213 : Nat := 118140960795 + 3675213 * 2 ^ 59
def prefixEnd_3675213 : Nat := 4983230072969 + 3 ^ 40 * 3675213 * 2
def baseEnd_3675213 : Nat := 629050258884211481978503

theorem tailTrace_3675213 : CollatzResearch.WordTrace tailWord_3675213 prefixEnd_3675213 629050258884211481978503 := by
  unfold tailWord_3675213
  simp only [CollatzResearch.WordTrace]
  refine ⟨134046030434338452253638293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89364020289558968169092195 134046030434338452253638293)
  ·
    refine ⟨6283407676609614949389295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 134046030434338452253638293 6283407676609614949389295)
    ·
      refine ⟨9425111514914422424083943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6283407676609614949389295 9425111514914422424083943)
      ·
        refine ⟨14137667272371633636125915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9425111514914422424083943 14137667272371633636125915)
        ·
          refine ⟨21206500908557450454188873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14137667272371633636125915 21206500908557450454188873)
          ·
            refine ⟨15904875681418087840641655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21206500908557450454188873 15904875681418087840641655)
            ·
              refine ⟨23857313522127131760962483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15904875681418087840641655 23857313522127131760962483)
              ·
                refine ⟨35785970283190697641443725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23857313522127131760962483 35785970283190697641443725)
                ·
                  refine ⟨13419738856196511615541397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35785970283190697641443725 13419738856196511615541397)
                  ·
                    refine ⟨629050258884211481978503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13419738856196511615541397 629050258884211481978503)
                    ·
                      rfl

theorem cell23_3675213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 1, 3, 6].length) (baseStart_3675213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3675213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3675213 prefixEnd_3675213 := by exact prefixLift 3675213
  have htrace : WordTrace (prefixWord ++ tailWord_3675213) baseStart_3675213 baseEnd_3675213 := by
    simpa [prefixWord, tailWord_3675213, baseEnd_3675213] using wordTrace_append hprefix tailTrace_3675213
  have hstable : (prefixWord ++ tailWord_3675213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3675213).length < 2 ^ (prefixWord ++ tailWord_3675213).sum := by decide
  have hdescent : baseEnd_3675213 < baseStart_3675213 := by decide
  rcases family_descends (prefixWord ++ tailWord_3675213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3675287 : List Nat := [1, 1, 3, 3, 3, 1, 3, 2, 2, 1, 3]
def baseStart_3675287 : Nat := 118140960795 + 3675287 * 2 ^ 59
def prefixEnd_3675287 : Nat := 4983230072969 + 3 ^ 40 * 3675287 * 2
def baseEnd_3675287 : Nat := 1887188774221067156410169

theorem tailTrace_3675287 : CollatzResearch.WordTrace tailWord_3675287 prefixEnd_3675287 1887188774221067156410169 := by
  unfold tailWord_3675287
  simp only [CollatzResearch.WordTrace]
  refine ⟨134048729436070362891832115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89365819624046908594554743 134048729436070362891832115)
  ·
    refine ⟨201073094154105544337748173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134048729436070362891832115 201073094154105544337748173)
    ·
      refine ⟨75402410307789579126655565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201073094154105544337748173 75402410307789579126655565)
      ·
        refine ⟨28275903865421092172495837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75402410307789579126655565 28275903865421092172495837)
        ·
          refine ⟨10603463949532909564685939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28275903865421092172495837 10603463949532909564685939)
          ·
            refine ⟨15905195924299364347028909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10603463949532909564685939 15905195924299364347028909)
            ·
              refine ⟨5964448471612261630135841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15905195924299364347028909 5964448471612261630135841)
              ·
                refine ⟨4473336353709196222601881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5964448471612261630135841 4473336353709196222601881)
                ·
                  refine ⟨3355002265281897166951411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4473336353709196222601881 3355002265281897166951411)
                  ·
                    refine ⟨5032503397922845750427117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3355002265281897166951411 5032503397922845750427117)
                    ·
                      refine ⟨1887188774221067156410169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5032503397922845750427117 1887188774221067156410169)
                      ·
                        rfl

theorem cell23_3675287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 3, 2, 2, 1, 3].length) (baseStart_3675287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3675287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3675287 prefixEnd_3675287 := by exact prefixLift 3675287
  have htrace : WordTrace (prefixWord ++ tailWord_3675287) baseStart_3675287 baseEnd_3675287 := by
    simpa [prefixWord, tailWord_3675287, baseEnd_3675287] using wordTrace_append hprefix tailTrace_3675287
  have hstable : (prefixWord ++ tailWord_3675287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3675287).length < 2 ^ (prefixWord ++ tailWord_3675287).sum := by decide
  have hdescent : baseEnd_3675287 < baseStart_3675287 := by decide
  rcases family_descends (prefixWord ++ tailWord_3675287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3675343 : List Nat := [1, 1, 2, 1, 1, 3, 2, 4, 2, 3, 3]
def baseStart_3675343 : Nat := 118140960795 + 3675343 * 2 ^ 59
def prefixEnd_3675343 : Nat := 4983230072969 + 3 ^ 40 * 3675343 * 2
def baseEnd_3675343 : Nat := 1887217529137718937309911

theorem tailTrace_3675343 : CollatzResearch.WordTrace tailWord_3675343 prefixEnd_3675343 1887217529137718937309911 := by
  unfold tailWord_3675343
  simp only [CollatzResearch.WordTrace]
  refine ⟨134050771923867484455870683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89367181282578322970580455 134050771923867484455870683)
  ·
    refine ⟨201076157885801226683806025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134050771923867484455870683 201076157885801226683806025)
    ·
      refine ⟨150807118414350920012854519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201076157885801226683806025 150807118414350920012854519)
      ·
        refine ⟨226210677621526380019281779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150807118414350920012854519 226210677621526380019281779)
        ·
          refine ⟨339316016432289570028922669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226210677621526380019281779 339316016432289570028922669)
          ·
            refine ⟨127243506162108588760846001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 339316016432289570028922669 127243506162108588760846001)
            ·
              refine ⟨95432629621581441570634501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127243506162108588760846001 95432629621581441570634501)
              ·
                refine ⟨17893618054046520294493969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 95432629621581441570634501 17893618054046520294493969)
                ·
                  refine ⟨13420213540534890220870477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17893618054046520294493969 13420213540534890220870477)
                  ·
                    refine ⟨5032580077700583832826429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13420213540534890220870477 5032580077700583832826429)
                    ·
                      refine ⟨1887217529137718937309911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5032580077700583832826429 1887217529137718937309911)
                      ·
                        rfl

theorem cell23_3675343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 4, 2, 3, 3].length) (baseStart_3675343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3675343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3675343 prefixEnd_3675343 := by exact prefixLift 3675343
  have htrace : WordTrace (prefixWord ++ tailWord_3675343) baseStart_3675343 baseEnd_3675343 := by
    simpa [prefixWord, tailWord_3675343, baseEnd_3675343] using wordTrace_append hprefix tailTrace_3675343
  have hstable : (prefixWord ++ tailWord_3675343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3675343).length < 2 ^ (prefixWord ++ tailWord_3675343).sum := by decide
  have hdescent : baseEnd_3675343 < baseStart_3675343 := by decide
  rcases family_descends (prefixWord ++ tailWord_3675343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3675361 : List Nat := [1, 2, 3, 1, 3, 4, 2, 1, 2, 2, 2]
def baseStart_3675361 : Nat := 118140960795 + 3675361 * 2 ^ 59
def prefixEnd_3675361 : Nat := 4983230072969 + 3 ^ 40 * 3675361 * 2
def baseEnd_3675361 : Nat := 1887226771789499866884829

theorem tailTrace_3675361 : CollatzResearch.WordTrace tailWord_3675361 prefixEnd_3675361 1887226771789499866884829 := by
  unfold tailWord_3675361
  simp only [CollatzResearch.WordTrace]
  refine ⟨134051428437802273530025937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89367618958534849020017291 134051428437802273530025937)
  ·
    refine ⟨100538571328351705147519453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134051428437802273530025937 100538571328351705147519453)
    ·
      refine ⟨37701964248131889430319795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100538571328351705147519453 37701964248131889430319795)
      ·
        refine ⟨56552946372197834145479693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37701964248131889430319795 56552946372197834145479693)
        ·
          refine ⟨21207354889574187804554885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56552946372197834145479693 21207354889574187804554885)
          ·
            refine ⟨3976379041795160213354041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21207354889574187804554885 3976379041795160213354041)
            ·
              refine ⟨2982284281346370160015531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3976379041795160213354041 2982284281346370160015531)
              ·
                refine ⟨4473426422019555240023297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2982284281346370160015531 4473426422019555240023297)
                ·
                  refine ⟨3355069816514666430017473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4473426422019555240023297 3355069816514666430017473)
                  ·
                    refine ⟨2516302362385999822513105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3355069816514666430017473 2516302362385999822513105)
                    ·
                      refine ⟨1887226771789499866884829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2516302362385999822513105 1887226771789499866884829)
                      ·
                        rfl

theorem cell23_3675361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 2, 1, 2, 2, 2].length) (baseStart_3675361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3675361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3675361 prefixEnd_3675361 := by exact prefixLift 3675361
  have htrace : WordTrace (prefixWord ++ tailWord_3675361) baseStart_3675361 baseEnd_3675361 := by
    simpa [prefixWord, tailWord_3675361, baseEnd_3675361] using wordTrace_append hprefix tailTrace_3675361
  have hstable : (prefixWord ++ tailWord_3675361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3675361).length < 2 ^ (prefixWord ++ tailWord_3675361).sum := by decide
  have hdescent : baseEnd_3675361 < baseStart_3675361 := by decide
  rcases family_descends (prefixWord ++ tailWord_3675361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3675383 : List Nat := [1, 1, 3, 1, 1, 1, 2, 2, 6, 1, 4]
def baseStart_3675383 : Nat := 118140960795 + 3675383 * 2 ^ 59
def prefixEnd_3675383 : Nat := 4983230072969 + 3 ^ 40 * 3675383 * 2
def baseEnd_3675383 : Nat := 1887238068363898780809727

theorem tailTrace_3675383 : CollatzResearch.WordTrace tailWord_3675383 prefixEnd_3675383 1887238068363898780809727 := by
  unfold tailWord_3675383
  simp only [CollatzResearch.WordTrace]
  refine ⟨134052230843722571287326803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89368153895815047524884535 134052230843722571287326803)
  ·
    refine ⟨201078346265583856930990205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134052230843722571287326803 201078346265583856930990205)
    ·
      refine ⟨75404379849593946349121327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201078346265583856930990205 75404379849593946349121327)
      ·
        refine ⟨113106569774390919523681991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75404379849593946349121327 113106569774390919523681991)
        ·
          refine ⟨169659854661586379285522987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113106569774390919523681991 169659854661586379285522987)
          ·
            refine ⟨254489781992379568928284481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169659854661586379285522987 254489781992379568928284481)
            ·
              refine ⟨190867336494284676696213361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 254489781992379568928284481 190867336494284676696213361)
              ·
                refine ⟨143150502370713507522160021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 190867336494284676696213361 143150502370713507522160021)
                ·
                  refine ⟨6710179798627195665101251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 143150502370713507522160021 6710179798627195665101251)
                  ·
                    refine ⟨10065269697940793497651877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6710179798627195665101251 10065269697940793497651877)
                    ·
                      refine ⟨1887238068363898780809727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10065269697940793497651877 1887238068363898780809727)
                      ·
                        rfl

theorem cell23_3675383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 6, 1, 4].length) (baseStart_3675383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3675383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3675383 prefixEnd_3675383 := by exact prefixLift 3675383
  have htrace : WordTrace (prefixWord ++ tailWord_3675383) baseStart_3675383 baseEnd_3675383 := by
    simpa [prefixWord, tailWord_3675383, baseEnd_3675383] using wordTrace_append hprefix tailTrace_3675383
  have hstable : (prefixWord ++ tailWord_3675383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3675383).length < 2 ^ (prefixWord ++ tailWord_3675383).sum := by decide
  have hdescent : baseEnd_3675383 < baseStart_3675383 := by decide
  rcases family_descends (prefixWord ++ tailWord_3675383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3675390 : List Nat := [4, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5]
def baseStart_3675390 : Nat := 118140960795 + 3675390 * 2 ^ 59
def prefixEnd_3675390 : Nat := 4983230072969 + 3 ^ 40 * 3675390 * 2
def baseEnd_3675390 : Nat := 1887241662728480253422195

theorem tailTrace_3675390 : CollatzResearch.WordTrace tailWord_3675390 prefixEnd_3675390 1887241662728480253422195 := by
  unfold tailWord_3675390
  simp only [CollatzResearch.WordTrace]
  refine ⟨16756560769337151435353953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89368324103131474321887749 16756560769337151435353953)
  ·
    refine ⟨12567420577002863576515465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16756560769337151435353953 12567420577002863576515465)
    ·
      refine ⟨9425565432752147682386599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12567420577002863576515465 9425565432752147682386599)
      ·
        refine ⟨14138348149128221523579899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9425565432752147682386599 14138348149128221523579899)
        ·
          refine ⟨21207522223692332285369849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14138348149128221523579899 21207522223692332285369849)
          ·
            refine ⟨15905641667769249214027387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21207522223692332285369849 15905641667769249214027387)
            ·
              refine ⟨23858462501653873821041081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15905641667769249214027387 23858462501653873821041081)
              ·
                refine ⟨17893846876240405365780811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23858462501653873821041081 17893846876240405365780811)
                ·
                  refine ⟨26840770314360608048671217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17893846876240405365780811 26840770314360608048671217)
                  ·
                    refine ⟨20130577735770456036503413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26840770314360608048671217 20130577735770456036503413)
                    ·
                      refine ⟨1887241662728480253422195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20130577735770456036503413 1887241662728480253422195)
                      ·
                        rfl

theorem cell23_3675390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_3675390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3675390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3675390 prefixEnd_3675390 := by exact prefixLift 3675390
  have htrace : WordTrace (prefixWord ++ tailWord_3675390) baseStart_3675390 baseEnd_3675390 := by
    simpa [prefixWord, tailWord_3675390, baseEnd_3675390] using wordTrace_append hprefix tailTrace_3675390
  have hstable : (prefixWord ++ tailWord_3675390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3675390).length < 2 ^ (prefixWord ++ tailWord_3675390).sum := by decide
  have hdescent : baseEnd_3675390 < baseStart_3675390 := by decide
  rcases family_descends (prefixWord ++ tailWord_3675390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3675413 : List Nat := [1, 3, 2, 1, 2, 1, 1, 2, 2, 4, 4]
def baseStart_3675413 : Nat := 118140960795 + 3675413 * 2 ^ 59
def prefixEnd_3675413 : Nat := 4983230072969 + 3 ^ 40 * 3675413 * 2
def baseEnd_3675413 : Nat := 1887253472783533663434589

theorem tailTrace_3675413 : CollatzResearch.WordTrace tailWord_3675413 prefixEnd_3675413 1887253472783533663434589 := by
  unfold tailWord_3675413
  simp only [CollatzResearch.WordTrace]
  refine ⟨134053325033613886410918893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89368883355742590940612595 134053325033613886410918893)
  ·
    refine ⟨50269996887605207404094585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134053325033613886410918893 50269996887605207404094585)
    ·
      refine ⟨37702497665703905553070939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50269996887605207404094585 37702497665703905553070939)
      ·
        refine ⟨56553746498555858329606409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37702497665703905553070939 56553746498555858329606409)
        ·
          refine ⟨42415309873916893747204807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56553746498555858329606409 42415309873916893747204807)
          ·
            refine ⟨63622964810875340620807211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42415309873916893747204807 63622964810875340620807211)
            ·
              refine ⟨95434447216313010931210817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63622964810875340620807211 95434447216313010931210817)
              ·
                refine ⟨71575835412234758198408113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95434447216313010931210817 71575835412234758198408113)
                ·
                  refine ⟨53681876559176068648806085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71575835412234758198408113 53681876559176068648806085)
                  ·
                    refine ⟨10065351854845512871651141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53681876559176068648806085 10065351854845512871651141)
                    ·
                      refine ⟨1887253472783533663434589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10065351854845512871651141 1887253472783533663434589)
                      ·
                        rfl

theorem cell23_3675413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 2, 2, 4, 4].length) (baseStart_3675413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3675413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3675413 prefixEnd_3675413 := by exact prefixLift 3675413
  have htrace : WordTrace (prefixWord ++ tailWord_3675413) baseStart_3675413 baseEnd_3675413 := by
    simpa [prefixWord, tailWord_3675413, baseEnd_3675413] using wordTrace_append hprefix tailTrace_3675413
  have hstable : (prefixWord ++ tailWord_3675413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3675413).length < 2 ^ (prefixWord ++ tailWord_3675413).sum := by decide
  have hdescent : baseEnd_3675413 < baseStart_3675413 := by decide
  rcases family_descends (prefixWord ++ tailWord_3675413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3675420 : List Nat := [2, 2, 3, 1, 1, 1, 2, 2, 4, 2, 3]
def baseStart_3675420 : Nat := 118140960795 + 3675420 * 2 ^ 59
def prefixEnd_3675420 : Nat := 4983230072969 + 3 ^ 40 * 3675420 * 2
def baseEnd_3675420 : Nat := 1887257067148115136047057

theorem tailTrace_3675420 : CollatzResearch.WordTrace tailWord_3675420 prefixEnd_3675420 1887257067148115136047057 := by
  unfold tailWord_3675420
  simp only [CollatzResearch.WordTrace]
  refine ⟨67026790172294263303211857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89369053563059017737615809 67026790172294263303211857)
  ·
    refine ⟨50270092629220697477408893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67026790172294263303211857 50270092629220697477408893)
    ·
      refine ⟨18851284735957761554028335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50270092629220697477408893 18851284735957761554028335)
      ·
        refine ⟨28276927103936642331042503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18851284735957761554028335 28276927103936642331042503)
        ·
          refine ⟨42415390655904963496563755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28276927103936642331042503 42415390655904963496563755)
          ·
            refine ⟨63623085983857445244845633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42415390655904963496563755 63623085983857445244845633)
            ·
              refine ⟨47717314487893083933634225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63623085983857445244845633 47717314487893083933634225)
              ·
                refine ⟨35787985865919812950225669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47717314487893083933634225 35787985865919812950225669)
                ·
                  refine ⟨6710247349859964928167313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35787985865919812950225669 6710247349859964928167313)
                  ·
                    refine ⟨5032685512394973696125485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6710247349859964928167313 5032685512394973696125485)
                    ·
                      refine ⟨1887257067148115136047057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5032685512394973696125485 1887257067148115136047057)
                      ·
                        rfl

theorem cell23_3675420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 2, 4, 2, 3].length) (baseStart_3675420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3675420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3675420 prefixEnd_3675420 := by exact prefixLift 3675420
  have htrace : WordTrace (prefixWord ++ tailWord_3675420) baseStart_3675420 baseEnd_3675420 := by
    simpa [prefixWord, tailWord_3675420, baseEnd_3675420] using wordTrace_append hprefix tailTrace_3675420
  have hstable : (prefixWord ++ tailWord_3675420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3675420).length < 2 ^ (prefixWord ++ tailWord_3675420).sum := by decide
  have hdescent : baseEnd_3675420 < baseStart_3675420 := by decide
  rcases family_descends (prefixWord ++ tailWord_3675420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3675434 : List Nat := [3, 1, 4, 2, 1, 3, 1, 1, 2, 1, 4]
def baseStart_3675434 : Nat := 118140960795 + 3675434 * 2 ^ 59
def prefixEnd_3675434 : Nat := 4983230072969 + 3 ^ 40 * 3675434 * 2
def baseEnd_3675434 : Nat := 1887264255877278081271993

theorem tailTrace_3675434 : CollatzResearch.WordTrace tailWord_3675434 prefixEnd_3675434 1887264255877278081271993 := by
  unfold tailWord_3675434
  simp only [CollatzResearch.WordTrace]
  refine ⟨33513522741634451749358339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89369393977691871331622237 33513522741634451749358339)
  ·
    refine ⟨50270284112451677624037509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33513522741634451749358339 50270284112451677624037509)
    ·
      refine ⟨9425678271084689554507033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50270284112451677624037509 9425678271084689554507033)
      ·
        refine ⟨7069258703313517165880275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9425678271084689554507033 7069258703313517165880275)
        ·
          refine ⟨10603888054970275748820413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7069258703313517165880275 10603888054970275748820413)
          ·
            refine ⟨3976458020613853405807655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10603888054970275748820413 3976458020613853405807655)
            ·
              refine ⟨5964687030920780108711483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3976458020613853405807655 5964687030920780108711483)
              ·
                refine ⟨8947030546381170163067225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5964687030920780108711483 8947030546381170163067225)
                ·
                  refine ⟨6710272909785877622300419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8947030546381170163067225 6710272909785877622300419)
                  ·
                    refine ⟨10065409364678816433450629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6710272909785877622300419 10065409364678816433450629)
                    ·
                      refine ⟨1887264255877278081271993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10065409364678816433450629 1887264255877278081271993)
                      ·
                        rfl

theorem cell23_3675434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_3675434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3675434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3675434 prefixEnd_3675434 := by exact prefixLift 3675434
  have htrace : WordTrace (prefixWord ++ tailWord_3675434) baseStart_3675434 baseEnd_3675434 := by
    simpa [prefixWord, tailWord_3675434, baseEnd_3675434] using wordTrace_append hprefix tailTrace_3675434
  have hstable : (prefixWord ++ tailWord_3675434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3675434).length < 2 ^ (prefixWord ++ tailWord_3675434).sum := by decide
  have hdescent : baseEnd_3675434 < baseStart_3675434 := by decide
  rcases family_descends (prefixWord ++ tailWord_3675434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3675457 : List Nat := [1, 2, 5, 2, 1, 1, 3, 2, 6]
def baseStart_3675457 : Nat := 118140960795 + 3675457 * 2 ^ 59
def prefixEnd_3675457 : Nat := 4983230072969 + 3 ^ 40 * 3675457 * 2
def baseEnd_3675457 : Nat := 209697340659147943476043

theorem tailTrace_3675457 : CollatzResearch.WordTrace tailWord_3675457 prefixEnd_3675457 209697340659147943476043 := by
  unfold tailWord_3675457
  simp only [CollatzResearch.WordTrace]
  refine ⟨134054929845454481925520625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89369953230302987950347083 134054929845454481925520625)
  ·
    refine ⟨100541197384090861444140469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134054929845454481925520625 100541197384090861444140469)
    ·
      refine ⟨9425737254758518260388169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 100541197384090861444140469 9425737254758518260388169)
      ·
        refine ⟨7069302941068888695291127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9425737254758518260388169 7069302941068888695291127)
        ·
          refine ⟨10603954411603333042936691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7069302941068888695291127 10603954411603333042936691)
          ·
            refine ⟨15905931617404999564405037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10603954411603333042936691 15905931617404999564405037)
            ·
              refine ⟨5964724356526874836651889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15905931617404999564405037 5964724356526874836651889)
              ·
                refine ⟨4473543267395156127488917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5964724356526874836651889 4473543267395156127488917)
                ·
                  refine ⟨209697340659147943476043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4473543267395156127488917 209697340659147943476043)
                  ·
                    rfl

theorem cell23_3675457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 3, 2, 6].length) (baseStart_3675457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3675457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3675457 prefixEnd_3675457 := by exact prefixLift 3675457
  have htrace : WordTrace (prefixWord ++ tailWord_3675457) baseStart_3675457 baseEnd_3675457 := by
    simpa [prefixWord, tailWord_3675457, baseEnd_3675457] using wordTrace_append hprefix tailTrace_3675457
  have hstable : (prefixWord ++ tailWord_3675457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3675457).length < 2 ^ (prefixWord ++ tailWord_3675457).sum := by decide
  have hdescent : baseEnd_3675457 < baseStart_3675457 := by decide
  rcases family_descends (prefixWord ++ tailWord_3675457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3675477 : List Nat := [1, 3, 2, 2, 3, 1, 1, 2, 1, 5, 2]
def baseStart_3675477 : Nat := 118140960795 + 3675477 * 2 ^ 59
def prefixEnd_3675477 : Nat := 4983230072969 + 3 ^ 40 * 3675477 * 2
def baseEnd_3675477 : Nat := 1887286335545421413034295

theorem tailTrace_3675477 : CollatzResearch.WordTrace tailWord_3675477 prefixEnd_3675477 1887286335545421413034295 := by
  unfold tailWord_3675477
  simp only [CollatzResearch.WordTrace]
  refine ⟨134055659305382025341248685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89370439536921350227499123 134055659305382025341248685)
  ·
    refine ⟨50270872239518259502968257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134055659305382025341248685 50270872239518259502968257)
    ·
      refine ⟨37703154179638694627226193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50270872239518259502968257 37703154179638694627226193)
      ·
        refine ⟨28277365634729020970419645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37703154179638694627226193 28277365634729020970419645)
        ·
          refine ⟨10604012113023382863907367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28277365634729020970419645 10604012113023382863907367)
          ·
            refine ⟨15906018169535074295861051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10604012113023382863907367 15906018169535074295861051)
            ·
              refine ⟨23859027254302611443791577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15906018169535074295861051 23859027254302611443791577)
              ·
                refine ⟨17894270440726958582843683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23859027254302611443791577 17894270440726958582843683)
                ·
                  refine ⟨26841405661090437874265525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17894270440726958582843683 26841405661090437874265525)
                  ·
                    refine ⟨2516381780727228550712393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26841405661090437874265525 2516381780727228550712393)
                    ·
                      refine ⟨1887286335545421413034295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2516381780727228550712393 1887286335545421413034295)
                      ·
                        rfl

theorem cell23_3675477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 2, 1, 5, 2].length) (baseStart_3675477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3675477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3675477 prefixEnd_3675477 := by exact prefixLift 3675477
  have htrace : WordTrace (prefixWord ++ tailWord_3675477) baseStart_3675477 baseEnd_3675477 := by
    simpa [prefixWord, tailWord_3675477, baseEnd_3675477] using wordTrace_append hprefix tailTrace_3675477
  have hstable : (prefixWord ++ tailWord_3675477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3675477).length < 2 ^ (prefixWord ++ tailWord_3675477).sum := by decide
  have hdescent : baseEnd_3675477 < baseStart_3675477 := by decide
  rcases family_descends (prefixWord ++ tailWord_3675477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3675501 : List Nat := [1, 5, 1, 1, 1, 3, 3, 3, 1, 1, 3]
def baseStart_3675501 : Nat := 118140960795 + 3675501 * 2 ^ 59
def prefixEnd_3675501 : Nat := 4983230072969 + 3 ^ 40 * 3675501 * 2
def baseEnd_3675501 : Nat := 1887298659081129319134185

theorem tailTrace_3675501 : CollatzResearch.WordTrace tailWord_3675501 prefixEnd_3675501 1887298659081129319134185 := by
  unfold tailWord_3675501
  simp only [CollatzResearch.WordTrace]
  refine ⟨134056534657295077440122357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89371023104863384960081571 134056534657295077440122357)
  ·
    refine ⟨12567800124121413510011471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 134056534657295077440122357 12567800124121413510011471)
    ·
      refine ⟨18851700186182120265017207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12567800124121413510011471 18851700186182120265017207)
      ·
        refine ⟨28277550279273180397525811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18851700186182120265017207 28277550279273180397525811)
        ·
          refine ⟨42416325418909770596288717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28277550279273180397525811 42416325418909770596288717)
          ·
            refine ⟨15906122032091163973608269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42416325418909770596288717 15906122032091163973608269)
            ·
              refine ⟨5964795762034186490103101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15906122032091163973608269 5964795762034186490103101)
              ·
                refine ⟨2236798410762819933788663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5964795762034186490103101 2236798410762819933788663)
                ·
                  refine ⟨3355197616144229900682995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2236798410762819933788663 3355197616144229900682995)
                  ·
                    refine ⟨5032796424216344851024493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3355197616144229900682995 5032796424216344851024493)
                    ·
                      refine ⟨1887298659081129319134185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5032796424216344851024493 1887298659081129319134185)
                      ·
                        rfl

theorem cell23_3675501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 3, 3, 1, 1, 3].length) (baseStart_3675501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3675501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3675501 prefixEnd_3675501 := by exact prefixLift 3675501
  have htrace : WordTrace (prefixWord ++ tailWord_3675501) baseStart_3675501 baseEnd_3675501 := by
    simpa [prefixWord, tailWord_3675501, baseEnd_3675501] using wordTrace_append hprefix tailTrace_3675501
  have hstable : (prefixWord ++ tailWord_3675501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3675501).length < 2 ^ (prefixWord ++ tailWord_3675501).sum := by decide
  have hdescent : baseEnd_3675501 < baseStart_3675501 := by decide
  rcases family_descends (prefixWord ++ tailWord_3675501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3675513 : List Nat := [1, 2, 1, 3, 2, 1, 13]
def baseStart_3675513 : Nat := 118140960795 + 3675513 * 2 ^ 59
def prefixEnd_3675513 : Nat := 4983230072969 + 3 ^ 40 * 3675513 * 2
def baseEnd_3675513 : Nat := 23300059516654114471409

theorem tailTrace_3675513 : CollatzResearch.WordTrace tailWord_3675513 prefixEnd_3675513 23300059516654114471409 := by
  unfold tailWord_3675513
  simp only [CollatzResearch.WordTrace]
  refine ⟨134056972333251603489559193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89371314888834402326372795 134056972333251603489559193)
  ·
    refine ⟨100542729249938702617169395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134056972333251603489559193 100542729249938702617169395)
    ·
      refine ⟨150814093874908053925754093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100542729249938702617169395 150814093874908053925754093)
      ·
        refine ⟨56555285203090520222157785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150814093874908053925754093 56555285203090520222157785)
        ·
          refine ⟨42416463902317890166618339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56555285203090520222157785 42416463902317890166618339)
          ·
            refine ⟨63624695853476835249927509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42416463902317890166618339 63624695853476835249927509)
            ·
              refine ⟨23300059516654114471409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 63624695853476835249927509 23300059516654114471409)
              ·
                rfl

theorem cell23_3675513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 13].length) (baseStart_3675513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3675513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3675513 prefixEnd_3675513 := by exact prefixLift 3675513
  have htrace : WordTrace (prefixWord ++ tailWord_3675513) baseStart_3675513 baseEnd_3675513 := by
    simpa [prefixWord, tailWord_3675513, baseEnd_3675513] using wordTrace_append hprefix tailTrace_3675513
  have hstable : (prefixWord ++ tailWord_3675513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3675513).length < 2 ^ (prefixWord ++ tailWord_3675513).sum := by decide
  have hdescent : baseEnd_3675513 < baseStart_3675513 := by decide
  rcases family_descends (prefixWord ++ tailWord_3675513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3675517 : List Nat := [1, 4, 1, 1, 2, 2, 2, 4, 2, 4]
def baseStart_3675517 : Nat := 118140960795 + 3675517 * 2 ^ 59
def prefixEnd_3675517 : Nat := 4983230072969 + 3 ^ 40 * 3675517 * 2
def baseEnd_3675517 : Nat := 629102291590533752178037

theorem tailTrace_3675517 : CollatzResearch.WordTrace tailWord_3675517 prefixEnd_3675517 629102291590533752178037 := by
  unfold tailWord_3675517
  simp only [CollatzResearch.WordTrace]
  refine ⟨134057118225237112172704805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89371412150158074781803203 134057118225237112172704805)
  ·
    refine ⟨25135709667231958532382151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134057118225237112172704805 25135709667231958532382151)
    ·
      refine ⟨37703564500847937798573227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25135709667231958532382151 37703564500847937798573227)
      ·
        refine ⟨56555346751271906697859841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37703564500847937798573227 56555346751271906697859841)
        ·
          refine ⟨42416510063453930023394881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56555346751271906697859841 42416510063453930023394881)
          ·
            refine ⟨31812382547590447517546161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42416510063453930023394881 31812382547590447517546161)
            ·
              refine ⟨23859286910692835638159621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31812382547590447517546161 23859286910692835638159621)
              ·
                refine ⟨4473616295754906682154929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23859286910692835638159621 4473616295754906682154929)
                ·
                  refine ⟨3355212221816180011616197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4473616295754906682154929 3355212221816180011616197)
                  ·
                    refine ⟨629102291590533752178037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3355212221816180011616197 629102291590533752178037)
                    ·
                      rfl

theorem cell23_3675517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 4, 2, 4].length) (baseStart_3675517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3675517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3675517 prefixEnd_3675517 := by exact prefixLift 3675517
  have htrace : WordTrace (prefixWord ++ tailWord_3675517) baseStart_3675517 baseEnd_3675517 := by
    simpa [prefixWord, tailWord_3675517, baseEnd_3675517] using wordTrace_append hprefix tailTrace_3675517
  have hstable : (prefixWord ++ tailWord_3675517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3675517).length < 2 ^ (prefixWord ++ tailWord_3675517).sum := by decide
  have hdescent : baseEnd_3675517 < baseStart_3675517 := by decide
  rcases family_descends (prefixWord ++ tailWord_3675517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3675538 : List Nat := [3, 2, 3, 3, 2, 1, 1, 2, 1, 5]
def baseStart_3675538 : Nat := 118140960795 + 3675538 * 2 ^ 59
def prefixEnd_3675538 : Nat := 4983230072969 + 3 ^ 40 * 3675538 * 2
def baseEnd_3675538 : Nat := 629105885955115224790505

theorem tailTrace_3675538 : CollatzResearch.WordTrace tailWord_3675538 prefixEnd_3675538 629105885955115224790505 := by
  unfold tailWord_3675538
  simp only [CollatzResearch.WordTrace]
  refine ⟨33514471039540258189804817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89371922772107355172812845 33514471039540258189804817)
  ·
    refine ⟨25135853279655193642353613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33514471039540258189804817 25135853279655193642353613)
    ·
      refine ⟨9425944979870697615882605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25135853279655193642353613 9425944979870697615882605)
      ·
        refine ⟨3534729367451511605955977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9425944979870697615882605 3534729367451511605955977)
        ·
          refine ⟨2651047025588633704466983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3534729367451511605955977 2651047025588633704466983)
          ·
            refine ⟨3976570538382950556700475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2651047025588633704466983 3976570538382950556700475)
            ·
              refine ⟨5964855807574425835050713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3976570538382950556700475 5964855807574425835050713)
              ·
                refine ⟨4473641855680819376288035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5964855807574425835050713 4473641855680819376288035)
                ·
                  refine ⟨6710462783521229064432053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4473641855680819376288035 6710462783521229064432053)
                  ·
                    refine ⟨629105885955115224790505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6710462783521229064432053 629105885955115224790505)
                    ·
                      rfl

theorem cell23_3675538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 1, 2, 1, 5].length) (baseStart_3675538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3675538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3675538 prefixEnd_3675538 := by exact prefixLift 3675538
  have htrace : WordTrace (prefixWord ++ tailWord_3675538) baseStart_3675538 baseEnd_3675538 := by
    simpa [prefixWord, tailWord_3675538, baseEnd_3675538] using wordTrace_append hprefix tailTrace_3675538
  have hstable : (prefixWord ++ tailWord_3675538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3675538).length < 2 ^ (prefixWord ++ tailWord_3675538).sum := by decide
  have hdescent : baseEnd_3675538 < baseStart_3675538 := by decide
  rcases family_descends (prefixWord ++ tailWord_3675538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3675544 : List Nat := [2, 1, 2, 5, 2, 1, 1, 1, 3, 2, 3]
def baseStart_3675544 : Nat := 118140960795 + 3675544 * 2 ^ 59
def prefixEnd_3675544 : Nat := 4983230072969 + 3 ^ 40 * 3675544 * 2
def baseEnd_3675544 : Nat := 1887320738749272650896487

theorem tailTrace_3675544 : CollatzResearch.WordTrace tailWord_3675544 prefixEnd_3675544 1887320738749272650896487 := by
  unfold tailWord_3675544
  simp only [CollatzResearch.WordTrace]
  refine ⟨67029051498069647891968843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89372068664092863855958457 67029051498069647891968843)
  ·
    refine ⟨100543577247104471837953265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67029051498069647891968843 100543577247104471837953265)
    ·
      refine ⟨75407682935328353878464949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100543577247104471837953265 75407682935328353878464949)
      ·
        refine ⟨7069470275187033176106089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 75407682935328353878464949 7069470275187033176106089)
        ·
          refine ⟨5302102706390274882079567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7069470275187033176106089 5302102706390274882079567)
          ·
            refine ⟨7953154059585412323119351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5302102706390274882079567 7953154059585412323119351)
            ·
              refine ⟨11929731089378118484679027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7953154059585412323119351 11929731089378118484679027)
              ·
                refine ⟨17894596634067177727018541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11929731089378118484679027 17894596634067177727018541)
                ·
                  refine ⟨6710473737775191647631953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17894596634067177727018541 6710473737775191647631953)
                  ·
                    refine ⟨5032855303331393735723965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6710473737775191647631953 5032855303331393735723965)
                    ·
                      refine ⟨1887320738749272650896487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5032855303331393735723965 1887320738749272650896487)
                      ·
                        rfl

theorem cell23_3675544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_3675544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3675544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3675544 prefixEnd_3675544 := by exact prefixLift 3675544
  have htrace : WordTrace (prefixWord ++ tailWord_3675544) baseStart_3675544 baseEnd_3675544 := by
    simpa [prefixWord, tailWord_3675544, baseEnd_3675544] using wordTrace_append hprefix tailTrace_3675544
  have hstable : (prefixWord ++ tailWord_3675544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3675544).length < 2 ^ (prefixWord ++ tailWord_3675544).sum := by decide
  have hdescent : baseEnd_3675544 < baseStart_3675544 := by decide
  rcases family_descends (prefixWord ++ tailWord_3675544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3675557 : List Nat := [1, 3, 1, 2, 1, 1, 2, 4, 4, 1, 3]
def baseStart_3675557 : Nat := 118140960795 + 3675557 * 2 ^ 59
def prefixEnd_3675557 : Nat := 4983230072969 + 3 ^ 40 * 3675557 * 2
def baseEnd_3675557 : Nat := 1887327413997781100033927

theorem tailTrace_3675557 : CollatzResearch.WordTrace tailWord_3675557 prefixEnd_3675557 1887327413997781100033927 := by
  unfold tailWord_3675557
  simp only [CollatzResearch.WordTrace]
  refine ⟨134058577145092199004160925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89372384763394799336107283 134058577145092199004160925)
  ·
    refine ⟨50271966429409574626560347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134058577145092199004160925 50271966429409574626560347)
    ·
      refine ⟨75407949644114361939840521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50271966429409574626560347 75407949644114361939840521)
      ·
        refine ⟨56555962233085771454880391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75407949644114361939840521 56555962233085771454880391)
        ·
          refine ⟨84833943349628657182320587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56555962233085771454880391 84833943349628657182320587)
          ·
            refine ⟨127250915024442985773480881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84833943349628657182320587 127250915024442985773480881)
            ·
              refine ⟨95438186268332239330110661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127250915024442985773480881 95438186268332239330110661)
              ·
                refine ⟨17894659925312294874395749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 95438186268332239330110661 17894659925312294874395749)
                ·
                  refine ⟨3355248735996055288949203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17894659925312294874395749 3355248735996055288949203)
                  ·
                    refine ⟨5032873103994082933423805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3355248735996055288949203 5032873103994082933423805)
                    ·
                      refine ⟨1887327413997781100033927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5032873103994082933423805 1887327413997781100033927)
                      ·
                        rfl

theorem cell23_3675557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 4, 4, 1, 3].length) (baseStart_3675557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3675557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3675557 prefixEnd_3675557 := by exact prefixLift 3675557
  have htrace : WordTrace (prefixWord ++ tailWord_3675557) baseStart_3675557 baseEnd_3675557 := by
    simpa [prefixWord, tailWord_3675557, baseEnd_3675557] using wordTrace_append hprefix tailTrace_3675557
  have hstable : (prefixWord ++ tailWord_3675557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3675557).length < 2 ^ (prefixWord ++ tailWord_3675557).sum := by decide
  have hdescent : baseEnd_3675557 < baseStart_3675557 := by decide
  rcases family_descends (prefixWord ++ tailWord_3675557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3675631 : List Nat := [1, 1, 2, 1, 4, 1, 5, 2, 2, 2, 2]
def baseStart_3675631 : Nat := 118140960795 + 3675631 * 2 ^ 59
def prefixEnd_3675631 : Nat := 4983230072969 + 3 ^ 40 * 3675631 * 2
def baseEnd_3675631 : Nat := 1887365411566213810508587

theorem tailTrace_3675631 : CollatzResearch.WordTrace tailWord_3675631 prefixEnd_3675631 1887365411566213810508587 := by
  unfold tailWord_3675631
  simp only [CollatzResearch.WordTrace]
  refine ⟨134061276146824109642354747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89374184097882739761569831 134061276146824109642354747)
  ·
    refine ⟨201091914220236164463532121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134061276146824109642354747 201091914220236164463532121)
    ·
      refine ⟨150818935665177123347649091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201091914220236164463532121 150818935665177123347649091)
      ·
        refine ⟨226228403497765685021473637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150818935665177123347649091 226228403497765685021473637)
        ·
          refine ⟨42417825655831065941526307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 226228403497765685021473637 42417825655831065941526307)
          ·
            refine ⟨63626738483746598912289461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42417825655831065941526307 63626738483746598912289461)
            ·
              refine ⟨5965006732851243648027137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63626738483746598912289461 5965006732851243648027137)
              ·
                refine ⟨4473755049638432736020353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5965006732851243648027137 4473755049638432736020353)
                ·
                  refine ⟨3355316287228824552015265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4473755049638432736020353 3355316287228824552015265)
                  ·
                    refine ⟨2516487215421618414011449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3355316287228824552015265 2516487215421618414011449)
                    ·
                      refine ⟨1887365411566213810508587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2516487215421618414011449 1887365411566213810508587)
                      ·
                        rfl

theorem cell23_3675631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 5, 2, 2, 2, 2].length) (baseStart_3675631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3675631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3675631 prefixEnd_3675631 := by exact prefixLift 3675631
  have htrace : WordTrace (prefixWord ++ tailWord_3675631) baseStart_3675631 baseEnd_3675631 := by
    simpa [prefixWord, tailWord_3675631, baseEnd_3675631] using wordTrace_append hprefix tailTrace_3675631
  have hstable : (prefixWord ++ tailWord_3675631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3675631).length < 2 ^ (prefixWord ++ tailWord_3675631).sum := by decide
  have hdescent : baseEnd_3675631 < baseStart_3675631 := by decide
  rcases family_descends (prefixWord ++ tailWord_3675631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3675677 : List Nat := [1, 4, 2, 2, 1, 1, 2, 2, 1, 2, 5]
def baseStart_3675677 : Nat := 118140960795 + 3675677 * 2 ^ 59
def prefixEnd_3675677 : Nat := 4983230072969 + 3 ^ 40 * 3675677 * 2
def baseEnd_3675677 : Nat := 1887389031676320630533375

theorem tailTrace_3675677 : CollatzResearch.WordTrace tailWord_3675677 prefixEnd_3675677 1887389031676320630533375 := by
  unfold tailWord_3675677
  simp only [CollatzResearch.WordTrace]
  refine ⟨134062953904657459498529285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89375302603104972999019523 134062953904657459498529285)
  ·
    refine ⟨25136803857123273655974241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134062953904657459498529285 25136803857123273655974241)
    ·
      refine ⟨18852602892842455241980681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25136803857123273655974241 18852602892842455241980681)
      ·
        refine ⟨14139452169631841431485511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18852602892842455241980681 14139452169631841431485511)
        ·
          refine ⟨21209178254447762147228267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14139452169631841431485511 21209178254447762147228267)
          ·
            refine ⟨31813767381671643220842401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21209178254447762147228267 31813767381671643220842401)
            ·
              refine ⟨23860325536253732415631801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31813767381671643220842401 23860325536253732415631801)
              ·
                refine ⟨17895244152190299311723851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23860325536253732415631801 17895244152190299311723851)
                ·
                  refine ⟨26842866228285448967585777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17895244152190299311723851 26842866228285448967585777)
                  ·
                    refine ⟨20132149671214086725689333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26842866228285448967585777 20132149671214086725689333)
                    ·
                      refine ⟨1887389031676320630533375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20132149671214086725689333 1887389031676320630533375)
                      ·
                        rfl

theorem cell23_3675677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_3675677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3675677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3675677 prefixEnd_3675677 := by exact prefixLift 3675677
  have htrace : WordTrace (prefixWord ++ tailWord_3675677) baseStart_3675677 baseEnd_3675677 := by
    simpa [prefixWord, tailWord_3675677, baseEnd_3675677] using wordTrace_append hprefix tailTrace_3675677
  have hstable : (prefixWord ++ tailWord_3675677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3675677).length < 2 ^ (prefixWord ++ tailWord_3675677).sum := by decide
  have hdescent : baseEnd_3675677 < baseStart_3675677 := by decide
  rcases family_descends (prefixWord ++ tailWord_3675677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3675688 : List Nat := [2, 1, 5, 2, 2, 1, 3, 2, 5]
def baseStart_3675688 : Nat := 118140960795 + 3675688 * 2 ^ 59
def prefixEnd_3675688 : Nat := 4983230072969 + 3 ^ 40 * 3675688 * 2
def baseEnd_3675688 : Nat := 209710519995946676388425

theorem tailTrace_3675688 : CollatzResearch.WordTrace tailWord_3675688 prefixEnd_3675688 209710519995946676388425 := by
  unfold tailWord_3675688
  simp only [CollatzResearch.WordTrace]
  refine ⟨67031677553808804188589859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89375570071745072251453145 67031677553808804188589859)
  ·
    refine ⟨100547516330713206282884789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67031677553808804188589859 100547516330713206282884789)
    ·
      refine ⟨9426329656004363089020449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 100547516330713206282884789 9426329656004363089020449)
      ·
        refine ⟨7069747242003272316765337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9426329656004363089020449 7069747242003272316765337)
        ·
          refine ⟨5302310431502454237574003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7069747242003272316765337 5302310431502454237574003)
          ·
            refine ⟨7953465647253681356361005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5302310431502454237574003 7953465647253681356361005)
            ·
              refine ⟨2982549617720130508635377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7953465647253681356361005 2982549617720130508635377)
              ·
                refine ⟨2236912213290097881476533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2982549617720130508635377 2236912213290097881476533)
                ·
                  refine ⟨209710519995946676388425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2236912213290097881476533 209710519995946676388425)
                  ·
                    rfl

theorem cell23_3675688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 3, 2, 5].length) (baseStart_3675688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3675688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3675688 prefixEnd_3675688 := by exact prefixLift 3675688
  have htrace : WordTrace (prefixWord ++ tailWord_3675688) baseStart_3675688 baseEnd_3675688 := by
    simpa [prefixWord, tailWord_3675688, baseEnd_3675688] using wordTrace_append hprefix tailTrace_3675688
  have hstable : (prefixWord ++ tailWord_3675688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3675688).length < 2 ^ (prefixWord ++ tailWord_3675688).sum := by decide
  have hdescent : baseEnd_3675688 < baseStart_3675688 := by decide
  rcases family_descends (prefixWord ++ tailWord_3675688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3675694 : List Nat := [4, 1, 3, 1, 2, 2, 1, 1, 1, 2, 5]
def baseStart_3675694 : Nat := 118140960795 + 3675694 * 2 ^ 59
def prefixEnd_3675694 : Nat := 4983230072969 + 3 ^ 40 * 3675694 * 2
def baseEnd_3675694 : Nat := 1887397760847447064020797

theorem tailTrace_3675694 : CollatzResearch.WordTrace tailWord_3675694 prefixEnd_3675694 1887397760847447064020797 := by
  unfold tailWord_3675694
  simp only [CollatzResearch.WordTrace]
  refine ⟨16757946743199483925237267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89375715963730580934598757 16757946743199483925237267)
  ·
    refine ⟨25136920114799225887855901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16757946743199483925237267 25136920114799225887855901)
    ·
      refine ⟨9426345043049709707945963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25136920114799225887855901 9426345043049709707945963)
      ·
        refine ⟨14139517564574564561918945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9426345043049709707945963 14139517564574564561918945)
        ·
          refine ⟨10604638173430923421439209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14139517564574564561918945 10604638173430923421439209)
          ·
            refine ⟨7953478630073192566079407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10604638173430923421439209 7953478630073192566079407)
            ·
              refine ⟨11930217945109788849119111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7953478630073192566079407 11930217945109788849119111)
              ·
                refine ⟨17895326917664683273678667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11930217945109788849119111 17895326917664683273678667)
                ·
                  refine ⟨26842990376497024910518001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17895326917664683273678667 26842990376497024910518001)
                  ·
                    refine ⟨20132242782372768682888501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26842990376497024910518001 20132242782372768682888501)
                    ·
                      refine ⟨1887397760847447064020797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20132242782372768682888501 1887397760847447064020797)
                      ·
                        rfl

theorem cell23_3675694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_3675694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3675694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3675694 prefixEnd_3675694 := by exact prefixLift 3675694
  have htrace : WordTrace (prefixWord ++ tailWord_3675694) baseStart_3675694 baseEnd_3675694 := by
    simpa [prefixWord, tailWord_3675694, baseEnd_3675694] using wordTrace_append hprefix tailTrace_3675694
  have hstable : (prefixWord ++ tailWord_3675694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3675694).length < 2 ^ (prefixWord ++ tailWord_3675694).sum := by decide
  have hdescent : baseEnd_3675694 < baseStart_3675694 := by decide
  rcases family_descends (prefixWord ++ tailWord_3675694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3675718 : List Nat := [6, 1, 1, 1, 3, 1, 2, 1, 2, 5]
def baseStart_3675718 : Nat := 118140960795 + 3675718 * 2 ^ 59
def prefixEnd_3675718 : Nat := 4983230072969 + 3 ^ 40 * 3675718 * 2
def baseEnd_3675718 : Nat := 629136694794384990040229

theorem tailTrace_3675718 : CollatzResearch.WordTrace tailWord_3675718 prefixEnd_3675718 629136694794384990040229 := by
  unfold tailWord_3675718
  simp only [CollatzResearch.WordTrace]
  refine ⟨4189514040547153859399119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 89376299531672615667181205 4189514040547153859399119)
  ·
    refine ⟨6284271060820730789098679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4189514040547153859399119 6284271060820730789098679)
    ·
      refine ⟨9426406591231096183648019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6284271060820730789098679 9426406591231096183648019)
      ·
        refine ⟨14139609886846644275472029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9426406591231096183648019 14139609886846644275472029)
        ·
          refine ⟨5302353707567491603302011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14139609886846644275472029 5302353707567491603302011)
          ·
            refine ⟨7953530561351237404953017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5302353707567491603302011 7953530561351237404953017)
            ·
              refine ⟨5965147921013428053714763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7953530561351237404953017 5965147921013428053714763)
              ·
                refine ⟨8947721881520142080572145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5965147921013428053714763 8947721881520142080572145)
                ·
                  refine ⟨6710791411140106560429109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8947721881520142080572145 6710791411140106560429109)
                  ·
                    refine ⟨629136694794384990040229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6710791411140106560429109 629136694794384990040229)
                    ·
                      rfl

theorem cell23_3675718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 2, 1, 2, 5].length) (baseStart_3675718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3675718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3675718 prefixEnd_3675718 := by exact prefixLift 3675718
  have htrace : WordTrace (prefixWord ++ tailWord_3675718) baseStart_3675718 baseEnd_3675718 := by
    simpa [prefixWord, tailWord_3675718, baseEnd_3675718] using wordTrace_append hprefix tailTrace_3675718
  have hstable : (prefixWord ++ tailWord_3675718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3675718).length < 2 ^ (prefixWord ++ tailWord_3675718).sum := by decide
  have hdescent : baseEnd_3675718 < baseStart_3675718 := by decide
  rcases family_descends (prefixWord ++ tailWord_3675718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3675724 : List Nat := [2, 2, 1, 3, 1, 3, 1, 3, 2, 2, 3]
def baseStart_3675724 : Nat := 118140960795 + 3675724 * 2 ^ 59
def prefixEnd_3675724 : Nat := 4983230072969 + 3 ^ 40 * 3675724 * 2
def baseEnd_3675724 : Nat := 1887413165267081946645659

theorem tailTrace_3675724 : CollatzResearch.WordTrace tailWord_3675724 prefixEnd_3675724 1887413165267081946645659 := by
  unfold tailWord_3675724
  simp only [CollatzResearch.WordTrace]
  refine ⟨67032334067743593262745113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89376445423658124350326817 67032334067743593262745113)
  ·
    refine ⟨50274250550807694947058835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67032334067743593262745113 50274250550807694947058835)
    ·
      refine ⟨75411375826211542420588253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50274250550807694947058835 75411375826211542420588253)
      ·
        refine ⟨28279265934829328407720595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75411375826211542420588253 28279265934829328407720595)
        ·
          refine ⟨42418898902243992611580893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28279265934829328407720595 42418898902243992611580893)
          ·
            refine ⟨15907087088341497229342835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42418898902243992611580893 15907087088341497229342835)
            ·
              refine ⟨23860630632512245844014253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15907087088341497229342835 23860630632512245844014253)
              ·
                refine ⟨8947736487192092191505345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23860630632512245844014253 8947736487192092191505345)
                ·
                  refine ⟨6710802365394069143629009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8947736487192092191505345 6710802365394069143629009)
                  ·
                    refine ⟨5033101774045551857721757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6710802365394069143629009 5033101774045551857721757)
                    ·
                      refine ⟨1887413165267081946645659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5033101774045551857721757 1887413165267081946645659)
                      ·
                        rfl

theorem cell23_3675724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 3, 2, 2, 3].length) (baseStart_3675724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3675724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3675724 prefixEnd_3675724 := by exact prefixLift 3675724
  have htrace : WordTrace (prefixWord ++ tailWord_3675724) baseStart_3675724 baseEnd_3675724 := by
    simpa [prefixWord, tailWord_3675724, baseEnd_3675724] using wordTrace_append hprefix tailTrace_3675724
  have hstable : (prefixWord ++ tailWord_3675724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3675724).length < 2 ^ (prefixWord ++ tailWord_3675724).sum := by decide
  have hdescent : baseEnd_3675724 < baseStart_3675724 := by decide
  rcases family_descends (prefixWord ++ tailWord_3675724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3675748 : List Nat := [2, 3, 1, 1, 2, 3, 4, 2, 1, 4]
def baseStart_3675748 : Nat := 118140960795 + 3675748 * 2 ^ 59
def prefixEnd_3675748 : Nat := 4983230072969 + 3 ^ 40 * 3675748 * 2
def baseEnd_3675748 : Nat := 629141829600929950915183

theorem tailTrace_3675748 : CollatzResearch.WordTrace tailWord_3675748 prefixEnd_3675748 629141829600929950915183 := by
  unfold tailWord_3675748
  simp only [CollatzResearch.WordTrace]
  refine ⟨67032771743700119312181949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89377028991600159082909265 67032771743700119312181949)
  ·
    refine ⟨25137289403887544742068231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67032771743700119312181949 25137289403887544742068231)
    ·
      refine ⟨37705934105831317113102347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25137289403887544742068231 37705934105831317113102347)
      ·
        refine ⟨56558901158746975669653521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37705934105831317113102347 56558901158746975669653521)
        ·
          refine ⟨42419175869060231752240141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56558901158746975669653521 42419175869060231752240141)
          ·
            refine ⟨15907190950897586907090053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42419175869060231752240141 15907190950897586907090053)
            ·
              refine ⟨2982598303293297545079385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15907190950897586907090053 2982598303293297545079385)
              ·
                refine ⟨2236948727469973158809539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2982598303293297545079385 2236948727469973158809539)
                ·
                  refine ⟨3355423091204959738214309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2236948727469973158809539 3355423091204959738214309)
                  ·
                    refine ⟨629141829600929950915183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3355423091204959738214309 629141829600929950915183)
                    ·
                      rfl

theorem cell23_3675748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 4, 2, 1, 4].length) (baseStart_3675748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3675748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3675748 prefixEnd_3675748 := by exact prefixLift 3675748
  have htrace : WordTrace (prefixWord ++ tailWord_3675748) baseStart_3675748 baseEnd_3675748 := by
    simpa [prefixWord, tailWord_3675748, baseEnd_3675748] using wordTrace_append hprefix tailTrace_3675748
  have hstable : (prefixWord ++ tailWord_3675748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3675748).length < 2 ^ (prefixWord ++ tailWord_3675748).sum := by decide
  have hdescent : baseEnd_3675748 < baseStart_3675748 := by decide
  rcases family_descends (prefixWord ++ tailWord_3675748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3675787 : List Nat := [1, 1, 1, 1, 4, 1, 3, 4, 1, 6]
def baseStart_3675787 : Nat := 118140960795 + 3675787 * 2 ^ 59
def prefixEnd_3675787 : Nat := 4983230072969 + 3 ^ 40 * 3675787 * 2
def baseEnd_3675787 : Nat := 629148504849438400052623

theorem tailTrace_3675787 : CollatzResearch.WordTrace tailWord_3675787 prefixEnd_3675787 629148504849438400052623 := by
  unfold tailWord_3675787
  simp only [CollatzResearch.WordTrace]
  refine ⟨134066965934258948285033615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89377977289505965523355743 134066965934258948285033615)
  ·
    refine ⟨201100448901388422427550423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134066965934258948285033615 201100448901388422427550423)
    ·
      refine ⟨301650673352082633641325635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201100448901388422427550423 301650673352082633641325635)
      ·
        refine ⟨452476010028123950461988453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301650673352082633641325635 452476010028123950461988453)
        ·
          refine ⟨84839251880273240711622835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 452476010028123950461988453 84839251880273240711622835)
          ·
            refine ⟨127258877820409861067434253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84839251880273240711622835 127258877820409861067434253)
            ·
              refine ⟨47722079182653697900287845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127258877820409861067434253 47722079182653697900287845)
              ·
                refine ⟨8947889846747568356303971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47722079182653697900287845 8947889846747568356303971)
                ·
                  refine ⟨13421834770121352534455957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8947889846747568356303971 13421834770121352534455957)
                  ·
                    refine ⟨629148504849438400052623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13421834770121352534455957 629148504849438400052623)
                    ·
                      rfl

theorem cell23_3675787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 4, 1, 6].length) (baseStart_3675787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3675787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3675787 prefixEnd_3675787 := by exact prefixLift 3675787
  have htrace : WordTrace (prefixWord ++ tailWord_3675787) baseStart_3675787 baseEnd_3675787 := by
    simpa [prefixWord, tailWord_3675787, baseEnd_3675787] using wordTrace_append hprefix tailTrace_3675787
  have hstable : (prefixWord ++ tailWord_3675787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3675787).length < 2 ^ (prefixWord ++ tailWord_3675787).sum := by decide
  have hdescent : baseEnd_3675787 < baseStart_3675787 := by decide
  rcases family_descends (prefixWord ++ tailWord_3675787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3675788 : List Nat := [2, 2, 1, 2, 1, 1, 6, 3, 1, 1, 3]
def baseStart_3675788 : Nat := 118140960795 + 3675788 * 2 ^ 59
def prefixEnd_3675788 : Nat := 4983230072969 + 3 ^ 40 * 3675788 * 2
def baseEnd_3675788 : Nat := 1887446028028969696245365

theorem tailTrace_3675788 : CollatzResearch.WordTrace tailWord_3675788 prefixEnd_3675788 1887446028028969696245365 := by
  unfold tailWord_3675788
  simp only [CollatzResearch.WordTrace]
  refine ⟨67033501203627662727910009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89378001604836883637213345 67033501203627662727910009)
  ·
    refine ⟨50275125902720747045932507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67033501203627662727910009 50275125902720747045932507)
    ·
      refine ⟨75412688854081120568898761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50275125902720747045932507 75412688854081120568898761)
      ·
        refine ⟨56559516640560840426674071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75412688854081120568898761 56559516640560840426674071)
        ·
          refine ⟨84839274960841260640011107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56559516640560840426674071 84839274960841260640011107)
          ·
            refine ⟨127258912441261890960016661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84839274960841260640011107 127258912441261890960016661)
            ·
              refine ⟨5965261520684151138750781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 127258912441261890960016661 5965261520684151138750781)
              ·
                refine ⟨2236973070256556677031543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5965261520684151138750781 2236973070256556677031543)
                ·
                  refine ⟨3355459605384835015547315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2236973070256556677031543 3355459605384835015547315)
                  ·
                    refine ⟨5033189408077252523320973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3355459605384835015547315 5033189408077252523320973)
                    ·
                      refine ⟨1887446028028969696245365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5033189408077252523320973 1887446028028969696245365)
                      ·
                        rfl

theorem cell23_3675788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 6, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 6, 3, 1, 1, 3].length) (baseStart_3675788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3675788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3675788 prefixEnd_3675788 := by exact prefixLift 3675788
  have htrace : WordTrace (prefixWord ++ tailWord_3675788) baseStart_3675788 baseEnd_3675788 := by
    simpa [prefixWord, tailWord_3675788, baseEnd_3675788] using wordTrace_append hprefix tailTrace_3675788
  have hstable : (prefixWord ++ tailWord_3675788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3675788).length < 2 ^ (prefixWord ++ tailWord_3675788).sum := by decide
  have hdescent : baseEnd_3675788 < baseStart_3675788 := by decide
  rcases family_descends (prefixWord ++ tailWord_3675788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3675797 : List Nat := [1, 3, 2, 1, 1, 1, 1, 2, 5, 1, 5]
def baseStart_3675797 : Nat := 118140960795 + 3675797 * 2 ^ 59
def prefixEnd_3675797 : Nat := 4983230072969 + 3 ^ 40 * 3675797 * 2
def baseEnd_3675797 : Nat := 1887450649354860161032823

theorem tailTrace_3675797 : CollatzResearch.WordTrace tailWord_3675797 prefixEnd_3675797 1887450649354860161032823 := by
  unfold tailWord_3675797
  simp only [CollatzResearch.WordTrace]
  refine ⟨134067330664222719992897645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89378220442815146661931763 134067330664222719992897645)
  ·
    refine ⟨50275248999083519997336617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134067330664222719992897645 50275248999083519997336617)
    ·
      refine ⟨37706436749312639998002463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50275248999083519997336617 37706436749312639998002463)
      ·
        refine ⟨56559655123968959997003695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37706436749312639998002463 56559655123968959997003695)
        ·
          refine ⟨84839482685953439995505543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56559655123968959997003695 84839482685953439995505543)
          ·
            refine ⟨127259224028930159993258315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84839482685953439995505543 127259224028930159993258315)
            ·
              refine ⟨190888836043395239989887473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127259224028930159993258315 190888836043395239989887473)
              ·
                refine ⟨143166627032546429992415605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 190888836043395239989887473 143166627032546429992415605)
                ·
                  refine ⟨13421871284301227811788963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 143166627032546429992415605 13421871284301227811788963)
                  ·
                    refine ⟨20132806926451841717683445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13421871284301227811788963 20132806926451841717683445)
                    ·
                      refine ⟨1887450649354860161032823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20132806926451841717683445 1887450649354860161032823)
                      ·
                        rfl

theorem cell23_3675797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 5, 1, 5].length) (baseStart_3675797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3675797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3675797 prefixEnd_3675797 := by exact prefixLift 3675797
  have htrace : WordTrace (prefixWord ++ tailWord_3675797) baseStart_3675797 baseEnd_3675797 := by
    simpa [prefixWord, tailWord_3675797, baseEnd_3675797] using wordTrace_append hprefix tailTrace_3675797
  have hstable : (prefixWord ++ tailWord_3675797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3675797).length < 2 ^ (prefixWord ++ tailWord_3675797).sum := by decide
  have hdescent : baseEnd_3675797 < baseStart_3675797 := by decide
  rcases family_descends (prefixWord ++ tailWord_3675797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3675824 : List Nat := [2, 1, 1, 1, 2, 1, 7, 1, 1, 2, 4]
def baseStart_3675824 : Nat := 118140960795 + 3675824 * 2 ^ 59
def prefixEnd_3675824 : Nat := 4983230072969 + 3 ^ 40 * 3675824 * 2
def baseEnd_3675824 : Nat := 1887464513332531555395199

theorem tailTrace_3675824 : CollatzResearch.WordTrace tailWord_3675824 prefixEnd_3675824 1887464513332531555395199 := by
  unfold tailWord_3675824
  simp only [CollatzResearch.WordTrace]
  refine ⟨67034157717562451802065263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89378876956749935736087017 67034157717562451802065263)
  ·
    refine ⟨100551236576343677703097895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67034157717562451802065263 100551236576343677703097895)
    ·
      refine ⟨150826854864515516554646843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100551236576343677703097895 150826854864515516554646843)
      ·
        refine ⟨226240282296773274831970265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150826854864515516554646843 226240282296773274831970265)
        ·
          refine ⟨169680211722579956123977699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226240282296773274831970265 169680211722579956123977699)
          ·
            refine ⟨254520317583869934185966549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169680211722579956123977699 254520317583869934185966549)
            ·
              refine ⟨5965319943371951582483591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 254520317583869934185966549 5965319943371951582483591)
              ·
                refine ⟨8947979915057927373725387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5965319943371951582483591 8947979915057927373725387)
                ·
                  refine ⟨13421969872586891060588081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8947979915057927373725387 13421969872586891060588081)
                  ·
                    refine ⟨10066477404440168295441061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13421969872586891060588081 10066477404440168295441061)
                    ·
                      refine ⟨1887464513332531555395199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10066477404440168295441061 1887464513332531555395199)
                      ·
                        rfl

theorem cell23_3675824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 7, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 7, 1, 1, 2, 4].length) (baseStart_3675824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3675824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3675824 prefixEnd_3675824 := by exact prefixLift 3675824
  have htrace : WordTrace (prefixWord ++ tailWord_3675824) baseStart_3675824 baseEnd_3675824 := by
    simpa [prefixWord, tailWord_3675824, baseEnd_3675824] using wordTrace_append hprefix tailTrace_3675824
  have hstable : (prefixWord ++ tailWord_3675824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3675824).length < 2 ^ (prefixWord ++ tailWord_3675824).sum := by decide
  have hdescent : baseEnd_3675824 < baseStart_3675824 := by decide
  rcases family_descends (prefixWord ++ tailWord_3675824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3675831 : List Nat := [1, 1, 3, 1, 5, 1, 1, 4, 1, 2, 3]
def baseStart_3675831 : Nat := 118140960795 + 3675831 * 2 ^ 59
def prefixEnd_3675831 : Nat := 4983230072969 + 3 ^ 40 * 3675831 * 2
def baseEnd_3675831 : Nat := 1887468107697113028007667

theorem tailTrace_3675831 : CollatzResearch.WordTrace tailWord_3675831 prefixEnd_3675831 1887468107697113028007667 := by
  unfold tailWord_3675831
  simp only [CollatzResearch.WordTrace]
  refine ⟨134068570746099543799635347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89379047164066362533090231 134068570746099543799635347)
  ·
    refine ⟨201102856119149315699453021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134068570746099543799635347 201102856119149315699453021)
    ·
      refine ⟨75413571044680993387294883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201102856119149315699453021 75413571044680993387294883)
      ·
        refine ⟨113120356567021490080942325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75413571044680993387294883 113120356567021490080942325)
        ·
          refine ⟨10605033428158264695088343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 113120356567021490080942325 10605033428158264695088343)
          ·
            refine ⟨15907550142237397042632515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10605033428158264695088343 15907550142237397042632515)
            ·
              refine ⟨23861325213356095563948773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15907550142237397042632515 23861325213356095563948773)
              ·
                refine ⟨4473998477504267918240395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23861325213356095563948773 4473998477504267918240395)
                ·
                  refine ⟨6710997716256401877360593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4473998477504267918240395 6710997716256401877360593)
                  ·
                    refine ⟨5033248287192301408020445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6710997716256401877360593 5033248287192301408020445)
                    ·
                      refine ⟨1887468107697113028007667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5033248287192301408020445 1887468107697113028007667)
                      ·
                        rfl

theorem cell23_3675831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 4, 1, 2, 3].length) (baseStart_3675831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3675831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3675831 prefixEnd_3675831 := by exact prefixLift 3675831
  have htrace : WordTrace (prefixWord ++ tailWord_3675831) baseStart_3675831 baseEnd_3675831 := by
    simpa [prefixWord, tailWord_3675831, baseEnd_3675831] using wordTrace_append hprefix tailTrace_3675831
  have hstable : (prefixWord ++ tailWord_3675831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3675831).length < 2 ^ (prefixWord ++ tailWord_3675831).sum := by decide
  have hdescent : baseEnd_3675831 < baseStart_3675831 := by decide
  rcases family_descends (prefixWord ++ tailWord_3675831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3675834 : List Nat := [3, 1, 1, 1, 2, 4, 4, 7]
def baseStart_3675834 : Nat := 118140960795 + 3675834 * 2 ^ 59
def prefixEnd_3675834 : Nat := 4983230072969 + 3 ^ 40 * 3675834 * 2
def baseEnd_3675834 : Nat := 69906283264410241343339

theorem tailTrace_3675834 : CollatzResearch.WordTrace tailWord_3675834 prefixEnd_3675834 69906283264410241343339 := by
  unfold tailWord_3675834
  simp only [CollatzResearch.WordTrace]
  refine ⟨33517170041272168827998639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89379120110059116874663037 33517170041272168827998639)
  ·
    refine ⟨50275755061908253241997959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33517170041272168827998639 50275755061908253241997959)
    ·
      refine ⟨75413632592862379862996939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50275755061908253241997959 75413632592862379862996939)
      ·
        refine ⟨113120448889293569794495409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75413632592862379862996939 113120448889293569794495409)
        ·
          refine ⟨84840336666970177345871557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113120448889293569794495409 84840336666970177345871557)
          ·
            refine ⟨15907563125056908252350917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84840336666970177345871557 15907563125056908252350917)
            ·
              refine ⟨2982668085948170297315797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15907563125056908252350917 2982668085948170297315797)
              ·
                refine ⟨69906283264410241343339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2982668085948170297315797 69906283264410241343339)
                ·
                  rfl

theorem cell23_3675834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 4, 7].length) (baseStart_3675834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3675834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3675834 prefixEnd_3675834 := by exact prefixLift 3675834
  have htrace : WordTrace (prefixWord ++ tailWord_3675834) baseStart_3675834 baseEnd_3675834 := by
    simpa [prefixWord, tailWord_3675834, baseEnd_3675834] using wordTrace_append hprefix tailTrace_3675834
  have hstable : (prefixWord ++ tailWord_3675834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3675834).length < 2 ^ (prefixWord ++ tailWord_3675834).sum := by decide
  have hdescent : baseEnd_3675834 < baseStart_3675834 := by decide
  rcases family_descends (prefixWord ++ tailWord_3675834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3675871 : List Nat := [1, 1, 2, 3, 2, 2, 2, 2, 3, 3, 2]
def baseStart_3675871 : Nat := 118140960795 + 3675871 * 2 ^ 59
def prefixEnd_3675871 : Nat := 4983230072969 + 3 ^ 40 * 3675871 * 2
def baseEnd_3675871 : Nat := 1887488646923292871507483

theorem tailTrace_3675871 : CollatzResearch.WordTrace tailWord_3675871 prefixEnd_3675871 1887488646923292871507483 := by
  unfold tailWord_3675871
  simp only [CollatzResearch.WordTrace]
  refine ⟨134070029665954630631091467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89380019777303087087394311 134070029665954630631091467)
  ·
    refine ⟨201105044498931945946637201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134070029665954630631091467 201105044498931945946637201)
    ·
      refine ⟨150828783374198959459977901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201105044498931945946637201 150828783374198959459977901)
      ·
        refine ⟨56560793765324609797491713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150828783374198959459977901 56560793765324609797491713)
        ·
          refine ⟨42420595323993457348118785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56560793765324609797491713 42420595323993457348118785)
          ·
            refine ⟨31815446492995093011089089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42420595323993457348118785 31815446492995093011089089)
            ·
              refine ⟨23861584869746319758316817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31815446492995093011089089 23861584869746319758316817)
              ·
                refine ⟨17896188652309739818737613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23861584869746319758316817 17896188652309739818737613)
                ·
                  refine ⟨6711070744616152432026605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17896188652309739818737613 6711070744616152432026605)
                  ·
                    refine ⟨2516651529231057162009977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6711070744616152432026605 2516651529231057162009977)
                    ·
                      refine ⟨1887488646923292871507483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2516651529231057162009977 1887488646923292871507483)
                      ·
                        rfl

theorem cell23_3675871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 2, 3, 3, 2].length) (baseStart_3675871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3675871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3675871 prefixEnd_3675871 := by exact prefixLift 3675871
  have htrace : WordTrace (prefixWord ++ tailWord_3675871) baseStart_3675871 baseEnd_3675871 := by
    simpa [prefixWord, tailWord_3675871, baseEnd_3675871] using wordTrace_append hprefix tailTrace_3675871
  have hstable : (prefixWord ++ tailWord_3675871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3675871).length < 2 ^ (prefixWord ++ tailWord_3675871).sum := by decide
  have hdescent : baseEnd_3675871 < baseStart_3675871 := by decide
  rcases family_descends (prefixWord ++ tailWord_3675871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3675918 : List Nat := [4, 1, 1, 2, 1, 1, 2, 3, 4, 2, 2]
def baseStart_3675918 : Nat := 118140960795 + 3675918 * 2 ^ 59
def prefixEnd_3675918 : Nat := 4983230072969 + 3 ^ 40 * 3675918 * 2
def baseEnd_3675918 : Nat := 1887512780514054187619767

theorem tailTrace_3675918 : CollatzResearch.WordTrace tailWord_3675918 prefixEnd_3675918 1887512780514054187619767 := by
  unfold tailWord_3675918
  simp only [CollatzResearch.WordTrace]
  refine ⟨16758967987098044707256551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89381162597856238438701605 16758967987098044707256551)
  ·
    refine ⟨25138451980647067060884827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16758967987098044707256551 25138451980647067060884827)
    ·
      refine ⟨37707677970970600591327241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25138451980647067060884827 37707677970970600591327241)
      ·
        refine ⟨28280758478227950443495431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37707677970970600591327241 28280758478227950443495431)
        ·
          refine ⟨42421137717341925665243147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28280758478227950443495431 42421137717341925665243147)
          ·
            refine ⟨63631706576012888497864721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42421137717341925665243147 63631706576012888497864721)
            ·
              refine ⟨47723779932009666373398541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63631706576012888497864721 47723779932009666373398541)
              ·
                refine ⟨17896417474503624890024453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47723779932009666373398541 17896417474503624890024453)
                ·
                  refine ⟨3355578276469429666879585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17896417474503624890024453 3355578276469429666879585)
                  ·
                    refine ⟨2516683707352072250159689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3355578276469429666879585 2516683707352072250159689)
                    ·
                      refine ⟨1887512780514054187619767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2516683707352072250159689 1887512780514054187619767)
                      ·
                        rfl

theorem cell23_3675918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 3, 4, 2, 2].length) (baseStart_3675918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3675918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3675918 prefixEnd_3675918 := by exact prefixLift 3675918
  have htrace : WordTrace (prefixWord ++ tailWord_3675918) baseStart_3675918 baseEnd_3675918 := by
    simpa [prefixWord, tailWord_3675918, baseEnd_3675918] using wordTrace_append hprefix tailTrace_3675918
  have hstable : (prefixWord ++ tailWord_3675918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3675918).length < 2 ^ (prefixWord ++ tailWord_3675918).sum := by decide
  have hdescent : baseEnd_3675918 < baseStart_3675918 := by decide
  rcases family_descends (prefixWord ++ tailWord_3675918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3675964 : List Nat := [2, 2, 2, 2, 1, 1, 2, 1, 3, 2, 5]
def baseStart_3675964 : Nat := 118140960795 + 3675964 * 2 ^ 59
def prefixEnd_3675964 : Nat := 4983230072969 + 3 ^ 40 * 3675964 * 2
def baseEnd_3675964 : Nat := 1887536400624161007644555

theorem tailTrace_3675964 : CollatzResearch.WordTrace tailWord_3675964 prefixEnd_3675964 1887536400624161007644555 := by
  unfold tailWord_3675964
  simp only [CollatzResearch.WordTrace]
  refine ⟨67036710827308853757113473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89382281103078471676151297 67036710827308853757113473)
  ·
    refine ⟨50277533120481640317835105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67036710827308853757113473 50277533120481640317835105)
    ·
      refine ⟨37708149840361230238376329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50277533120481640317835105 37708149840361230238376329)
      ·
        refine ⟨28281112380270922678782247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37708149840361230238376329 28281112380270922678782247)
        ·
          refine ⟨42421668570406384018173371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28281112380270922678782247 42421668570406384018173371)
          ·
            refine ⟨63632502855609576027260057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42421668570406384018173371 63632502855609576027260057)
            ·
              refine ⟨47724377141707182020445043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63632502855609576027260057 47724377141707182020445043)
              ·
                refine ⟨71586565712560773030667565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47724377141707182020445043 71586565712560773030667565)
                ·
                  refine ⟨26844962142210289886500337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71586565712560773030667565 26844962142210289886500337)
                  ·
                    refine ⟨20133721606657717414875253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26844962142210289886500337 20133721606657717414875253)
                    ·
                      refine ⟨1887536400624161007644555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20133721606657717414875253 1887536400624161007644555)
                      ·
                        rfl

theorem cell23_3675964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 3, 2, 5].length) (baseStart_3675964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3675964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3675964 prefixEnd_3675964 := by exact prefixLift 3675964
  have htrace : WordTrace (prefixWord ++ tailWord_3675964) baseStart_3675964 baseEnd_3675964 := by
    simpa [prefixWord, tailWord_3675964, baseEnd_3675964] using wordTrace_append hprefix tailTrace_3675964
  have hstable : (prefixWord ++ tailWord_3675964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3675964).length < 2 ^ (prefixWord ++ tailWord_3675964).sum := by decide
  have hdescent : baseEnd_3675964 < baseStart_3675964 := by decide
  rcases family_descends (prefixWord ++ tailWord_3675964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3676001 : List Nat := [1, 2, 3, 1, 1, 1, 3, 4, 3, 4]
def baseStart_3676001 : Nat := 118140960795 + 3676001 * 2 ^ 59
def prefixEnd_3676001 : Nat := 4983230072969 + 3 ^ 40 * 3676001 * 2
def baseEnd_3676001 : Nat := 629185133136125787627295

theorem tailTrace_3676001 : CollatzResearch.WordTrace tailWord_3676001 prefixEnd_3676001 629185133136125787627295 := by
  unfold tailWord_3676001
  simp only [CollatzResearch.WordTrace]
  refine ⟨134074771155483662833323857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89383180770322441888882571 134074771155483662833323857)
  ·
    refine ⟨100556078366612747124992893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134074771155483662833323857 100556078366612747124992893)
    ·
      refine ⟨37708529387479780171872335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100556078366612747124992893 37708529387479780171872335)
      ·
        refine ⟨56562794081219670257808503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37708529387479780171872335 56562794081219670257808503)
        ·
          refine ⟨84844191121829505386712755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56562794081219670257808503 84844191121829505386712755)
          ·
            refine ⟨127266286682744258080069133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84844191121829505386712755 127266286682744258080069133)
            ·
              refine ⟨47724857506029096780025925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127266286682744258080069133 47724857506029096780025925)
              ·
                refine ⟨8948410782380455646254861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47724857506029096780025925 8948410782380455646254861)
                ·
                  refine ⟨3355654043392670867345573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8948410782380455646254861 3355654043392670867345573)
                  ·
                    refine ⟨629185133136125787627295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3355654043392670867345573 629185133136125787627295)
                    ·
                      rfl

theorem cell23_3676001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 4, 3, 4].length) (baseStart_3676001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3676001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3676001 prefixEnd_3676001 := by exact prefixLift 3676001
  have htrace : WordTrace (prefixWord ++ tailWord_3676001) baseStart_3676001 baseEnd_3676001 := by
    simpa [prefixWord, tailWord_3676001, baseEnd_3676001] using wordTrace_append hprefix tailTrace_3676001
  have hstable : (prefixWord ++ tailWord_3676001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3676001).length < 2 ^ (prefixWord ++ tailWord_3676001).sum := by decide
  have hdescent : baseEnd_3676001 < baseStart_3676001 := by decide
  rcases family_descends (prefixWord ++ tailWord_3676001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3676011 : List Nat := [1, 1, 1, 1, 2, 2, 3, 5, 2, 2, 3]
def baseStart_3676011 : Nat := 118140960795 + 3676011 * 2 ^ 59
def prefixEnd_3676011 : Nat := 4983230072969 + 3 ^ 40 * 3676011 * 2
def baseEnd_3676011 : Nat := 1887560534214922323756839

theorem tailTrace_3676011 : CollatzResearch.WordTrace tailWord_3676011 prefixEnd_3676011 1887560534214922323756839 := by
  unfold tailWord_3676011
  simp only [CollatzResearch.WordTrace]
  refine ⟨134075135885447434541187887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89383423923631623027458591 134075135885447434541187887)
  ·
    refine ⟨201112703828171151811781831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134075135885447434541187887 201112703828171151811781831)
    ·
      refine ⟨301669055742256727717672747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201112703828171151811781831 301669055742256727717672747)
      ·
        refine ⟨452503583613385091576509121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301669055742256727717672747 452503583613385091576509121)
        ·
          refine ⟨339377687710038818682381841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 452503583613385091576509121 339377687710038818682381841)
          ·
            refine ⟨254533265782529114011786381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 339377687710038818682381841 254533265782529114011786381)
            ·
              refine ⟨95449974668448417754419893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 254533265782529114011786381 95449974668448417754419893)
              ·
                refine ⟨8948435125167039164476865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 95449974668448417754419893 8948435125167039164476865)
                ·
                  refine ⟨6711326343875279373357649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8948435125167039164476865 6711326343875279373357649)
                  ·
                    refine ⟨5033494757906459530018237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6711326343875279373357649 5033494757906459530018237)
                    ·
                      refine ⟨1887560534214922323756839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5033494757906459530018237 1887560534214922323756839)
                      ·
                        rfl

theorem cell23_3676011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5, 2, 2, 3].length) (baseStart_3676011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3676011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3676011 prefixEnd_3676011 := by exact prefixLift 3676011
  have htrace : WordTrace (prefixWord ++ tailWord_3676011) baseStart_3676011 baseEnd_3676011 := by
    simpa [prefixWord, tailWord_3676011, baseEnd_3676011] using wordTrace_append hprefix tailTrace_3676011
  have hstable : (prefixWord ++ tailWord_3676011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3676011).length < 2 ^ (prefixWord ++ tailWord_3676011).sum := by decide
  have hdescent : baseEnd_3676011 < baseStart_3676011 := by decide
  rcases family_descends (prefixWord ++ tailWord_3676011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3676044 : List Nat := [2, 2, 1, 2, 1, 2, 1, 1, 2, 9]
def baseStart_3676044 : Nat := 118140960795 + 3676044 * 2 ^ 59
def prefixEnd_3676044 : Nat := 4983230072969 + 3 ^ 40 * 3676044 * 2
def baseEnd_3676044 : Nat := 629192493025506898214729

theorem tailTrace_3676044 : CollatzResearch.WordTrace tailWord_3676044 prefixEnd_3676044 629192493025506898214729 := by
  unfold tailWord_3676044
  simp only [CollatzResearch.WordTrace]
  refine ⟨67038169747163940588569593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89384226329551920784759457 67038169747163940588569593)
  ·
    refine ⟨50278627310372955441427195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67038169747163940588569593 50278627310372955441427195)
    ·
      refine ⟨75417940965559433162140793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50278627310372955441427195 75417940965559433162140793)
      ·
        refine ⟨56563455724169574871605595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75417940965559433162140793 56563455724169574871605595)
        ·
          refine ⟨84845183586254362307408393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56563455724169574871605595 84845183586254362307408393)
          ·
            refine ⟨63633887689690771730556295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84845183586254362307408393 63633887689690771730556295)
            ·
              refine ⟨95450831534536157595834443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63633887689690771730556295 95450831534536157595834443)
              ·
                refine ⟨143176247301804236393751665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95450831534536157595834443 143176247301804236393751665)
                ·
                  refine ⟨107382185476353177295313749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 143176247301804236393751665 107382185476353177295313749)
                  ·
                    refine ⟨629192493025506898214729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 107382185476353177295313749 629192493025506898214729)
                    ·
                      rfl

theorem cell23_3676044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 2, 9].length) (baseStart_3676044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3676044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3676044 prefixEnd_3676044 := by exact prefixLift 3676044
  have htrace : WordTrace (prefixWord ++ tailWord_3676044) baseStart_3676044 baseEnd_3676044 := by
    simpa [prefixWord, tailWord_3676044, baseEnd_3676044] using wordTrace_append hprefix tailTrace_3676044
  have hstable : (prefixWord ++ tailWord_3676044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3676044).length < 2 ^ (prefixWord ++ tailWord_3676044).sum := by decide
  have hdescent : baseEnd_3676044 < baseStart_3676044 := by decide
  rcases family_descends (prefixWord ++ tailWord_3676044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3676085 : List Nat := [1, 3, 3, 2, 1, 2, 2, 2, 2, 3, 2]
def baseStart_3676085 : Nat := 118140960795 + 3676085 * 2 ^ 59
def prefixEnd_3676085 : Nat := 4983230072969 + 3 ^ 40 * 3676085 * 2
def baseEnd_3676085 : Nat := 1887598531783355034231499

theorem tailTrace_3676085 : CollatzResearch.WordTrace tailWord_3676085 prefixEnd_3676085 1887598531783355034231499 := by
  unfold tailWord_3676085
  simp only [CollatzResearch.WordTrace]
  refine ⟨134077834887179345179381709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89385223258119563452921139 134077834887179345179381709)
  ·
    refine ⟨50279188082692254442268141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134077834887179345179381709 50279188082692254442268141)
    ·
      refine ⟨18854695531009595415850553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50279188082692254442268141 18854695531009595415850553)
      ·
        refine ⟨14141021648257196561887915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18854695531009595415850553 14141021648257196561887915)
        ·
          refine ⟨21211532472385794842831873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14141021648257196561887915 21211532472385794842831873)
          ·
            refine ⟨15908649354289346132123905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21211532472385794842831873 15908649354289346132123905)
            ·
              refine ⟨11931487015717009599092929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15908649354289346132123905 11931487015717009599092929)
              ·
                refine ⟨8948615261787757199319697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11931487015717009599092929 8948615261787757199319697)
                ·
                  refine ⟨6711461446340817899489773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8948615261787757199319697 6711461446340817899489773)
                  ·
                    refine ⟨2516798042377806712308665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6711461446340817899489773 2516798042377806712308665)
                    ·
                      refine ⟨1887598531783355034231499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2516798042377806712308665 1887598531783355034231499)
                      ·
                        rfl

theorem cell23_3676085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 2, 2, 3, 2].length) (baseStart_3676085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3676085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3676085 prefixEnd_3676085 := by exact prefixLift 3676085
  have htrace : WordTrace (prefixWord ++ tailWord_3676085) baseStart_3676085 baseEnd_3676085 := by
    simpa [prefixWord, tailWord_3676085, baseEnd_3676085] using wordTrace_append hprefix tailTrace_3676085
  have hstable : (prefixWord ++ tailWord_3676085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3676085).length < 2 ^ (prefixWord ++ tailWord_3676085).sum := by decide
  have hdescent : baseEnd_3676085 < baseStart_3676085 := by decide
  rcases family_descends (prefixWord ++ tailWord_3676085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3676108 : List Nat := [2, 2, 1, 4, 1, 3, 2, 1, 1, 6]
def baseStart_3676108 : Nat := 118140960795 + 3676108 * 2 ^ 59
def prefixEnd_3676108 : Nat := 4983230072969 + 3 ^ 40 * 3676108 * 2
def baseEnd_3676108 : Nat := 629203447279469481414631

theorem tailTrace_3676108 : CollatzResearch.WordTrace tailWord_3676108 prefixEnd_3676108 629203447279469481414631 := by
  unfold tailWord_3676108
  simp only [CollatzResearch.WordTrace]
  refine ⟨67039336883048010053734489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89385782510730680071645985 67039336883048010053734489)
  ·
    refine ⟨50279502662286007540300867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67039336883048010053734489 50279502662286007540300867)
    ·
      refine ⟨75419253993429011310451301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50279502662286007540300867 75419253993429011310451301)
      ·
        refine ⟨14141110123767939620709619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75419253993429011310451301 14141110123767939620709619)
        ·
          refine ⟨21211665185651909431064429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14141110123767939620709619 21211665185651909431064429)
          ·
            refine ⟨7954374444619466036649161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21211665185651909431064429 7954374444619466036649161)
            ·
              refine ⟨5965780833464599527486871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7954374444619466036649161 5965780833464599527486871)
              ·
                refine ⟨8948671250196899291230307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5965780833464599527486871 8948671250196899291230307)
                ·
                  refine ⟨13423006875295348936845461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8948671250196899291230307 13423006875295348936845461)
                  ·
                    refine ⟨629203447279469481414631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13423006875295348936845461 629203447279469481414631)
                    ·
                      rfl

theorem cell23_3676108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 2, 1, 1, 6].length) (baseStart_3676108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3676108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3676108 prefixEnd_3676108 := by exact prefixLift 3676108
  have htrace : WordTrace (prefixWord ++ tailWord_3676108) baseStart_3676108 baseEnd_3676108 := by
    simpa [prefixWord, tailWord_3676108, baseEnd_3676108] using wordTrace_append hprefix tailTrace_3676108
  have hstable : (prefixWord ++ tailWord_3676108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3676108).length < 2 ^ (prefixWord ++ tailWord_3676108).sum := by decide
  have hdescent : baseEnd_3676108 < baseStart_3676108 := by decide
  rcases family_descends (prefixWord ++ tailWord_3676108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3676142 : List Nat := [4, 1, 2, 1, 3, 3, 1, 2, 2, 4]
def baseStart_3676142 : Nat := 118140960795 + 3676142 * 2 ^ 59
def prefixEnd_3676142 : Nat := 4983230072969 + 3 ^ 40 * 3676142 * 2
def baseEnd_3676142 : Nat := 629209266726887103739579

theorem tailTrace_3676142 : CollatzResearch.WordTrace tailWord_3676142 prefixEnd_3676142 629209266726887103739579 := by
  unfold tailWord_3676142
  simp only [CollatzResearch.WordTrace]
  refine ⟨16759989230996605489275835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89386609231981895942804453 16759989230996605489275835)
  ·
    refine ⟨25139983846494908233913753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16759989230996605489275835 25139983846494908233913753)
    ·
      refine ⟨18854987884871181175435315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25139983846494908233913753 18854987884871181175435315)
      ·
        refine ⟨28282481827306771763152973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18854987884871181175435315 28282481827306771763152973)
        ·
          refine ⟨10605930685240039411182365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28282481827306771763152973 10605930685240039411182365)
          ·
            refine ⟨3977224006965014779193387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10605930685240039411182365 3977224006965014779193387)
            ·
              refine ⟨5965836010447522168790081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3977224006965014779193387 5965836010447522168790081)
              ·
                refine ⟨4474377007835641626592561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5965836010447522168790081 4474377007835641626592561)
                ·
                  refine ⟨3355782755876731219944421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4474377007835641626592561 3355782755876731219944421)
                  ·
                    refine ⟨629209266726887103739579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3355782755876731219944421 629209266726887103739579)
                    ·
                      rfl

theorem cell23_3676142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 1, 2, 2, 4].length) (baseStart_3676142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3676142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3676142 prefixEnd_3676142 := by exact prefixLift 3676142
  have htrace : WordTrace (prefixWord ++ tailWord_3676142) baseStart_3676142 baseEnd_3676142 := by
    simpa [prefixWord, tailWord_3676142, baseEnd_3676142] using wordTrace_append hprefix tailTrace_3676142
  have hstable : (prefixWord ++ tailWord_3676142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3676142).length < 2 ^ (prefixWord ++ tailWord_3676142).sum := by decide
  have hdescent : baseEnd_3676142 < baseStart_3676142 := by decide
  rcases family_descends (prefixWord ++ tailWord_3676142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3676165 : List Nat := [1, 3, 1, 1, 2, 6, 1, 1, 1, 3, 3]
def baseStart_3676165 : Nat := 118140960795 + 3676165 * 2 ^ 59
def prefixEnd_3676165 : Nat := 4983230072969 + 3 ^ 40 * 3676165 * 2
def baseEnd_3676165 : Nat := 1887639610235714721231131

theorem tailTrace_3676165 : CollatzResearch.WordTrace tailWord_3676165 prefixEnd_3676165 1887639610235714721231131 := by
  unfold tailWord_3676165
  simp only [CollatzResearch.WordTrace]
  refine ⟨134080752726889518842293949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89387168484593012561529299 134080752726889518842293949)
  ·
    refine ⟨50280282272583569565860231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134080752726889518842293949 50280282272583569565860231)
    ·
      refine ⟨75420423408875354348790347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50280282272583569565860231 75420423408875354348790347)
      ·
        refine ⟨113130635113313031523185521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75420423408875354348790347 113130635113313031523185521)
        ·
          refine ⟨84847976334984773642389141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113130635113313031523185521 84847976334984773642389141)
          ·
            refine ⟨3977248890702411264486991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 84847976334984773642389141 3977248890702411264486991)
            ·
              refine ⟨5965873336053616896730487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3977248890702411264486991 5965873336053616896730487)
              ·
                refine ⟨8948810004080425345095731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5965873336053616896730487 8948810004080425345095731)
                ·
                  refine ⟨13423215006120638017643597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8948810004080425345095731 13423215006120638017643597)
                  ·
                    refine ⟨5033705627295239256616349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13423215006120638017643597 5033705627295239256616349)
                    ·
                      refine ⟨1887639610235714721231131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5033705627295239256616349 1887639610235714721231131)
                      ·
                        rfl

theorem cell23_3676165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 1, 1, 1, 3, 3].length) (baseStart_3676165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3676165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3676165 prefixEnd_3676165 := by exact prefixLift 3676165
  have htrace : WordTrace (prefixWord ++ tailWord_3676165) baseStart_3676165 baseEnd_3676165 := by
    simpa [prefixWord, tailWord_3676165, baseEnd_3676165] using wordTrace_append hprefix tailTrace_3676165
  have hstable : (prefixWord ++ tailWord_3676165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3676165).length < 2 ^ (prefixWord ++ tailWord_3676165).sum := by decide
  have hdescent : baseEnd_3676165 < baseStart_3676165 := by decide
  rcases family_descends (prefixWord ++ tailWord_3676165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3676183 : List Nat := [1, 1, 3, 5, 3, 1, 1, 3, 1, 2, 2]
def baseStart_3676183 : Nat := 118140960795 + 3676183 * 2 ^ 59
def prefixEnd_3676183 : Nat := 4983230072969 + 3 ^ 40 * 3676183 * 2
def baseEnd_3676183 : Nat := 1887648852887495650806049

theorem tailTrace_3676183 : CollatzResearch.WordTrace tailWord_3676183 prefixEnd_3676183 1887648852887495650806049 := by
  unfold tailWord_3676183
  simp only [CollatzResearch.WordTrace]
  refine ⟨134081409240824307916449203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89387606160549538610966135 134081409240824307916449203)
  ·
    refine ⟨201122113861236461874673805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134081409240824307916449203 201122113861236461874673805)
    ·
      refine ⟨75420792697963673203002677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201122113861236461874673805 75420792697963673203002677)
      ·
        refine ⟨7070699315434094362781501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 75420792697963673203002677 7070699315434094362781501)
        ·
          refine ⟨2651512243287785386043063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7070699315434094362781501 2651512243287785386043063)
          ·
            refine ⟨3977268364931678079064595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2651512243287785386043063 3977268364931678079064595)
            ·
              refine ⟨5965902547397517118596893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3977268364931678079064595 5965902547397517118596893)
              ·
                refine ⟨2237213455274068919473835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5965902547397517118596893 2237213455274068919473835)
                ·
                  refine ⟨3355820182911103379210753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2237213455274068919473835 3355820182911103379210753)
                  ·
                    refine ⟨2516865137183327534408065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3355820182911103379210753 2516865137183327534408065)
                    ·
                      refine ⟨1887648852887495650806049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2516865137183327534408065 1887648852887495650806049)
                      ·
                        rfl

theorem cell23_3676183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 1, 3, 1, 2, 2].length) (baseStart_3676183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3676183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3676183 prefixEnd_3676183 := by exact prefixLift 3676183
  have htrace : WordTrace (prefixWord ++ tailWord_3676183) baseStart_3676183 baseEnd_3676183 := by
    simpa [prefixWord, tailWord_3676183, baseEnd_3676183] using wordTrace_append hprefix tailTrace_3676183
  have hstable : (prefixWord ++ tailWord_3676183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3676183).length < 2 ^ (prefixWord ++ tailWord_3676183).sum := by decide
  have hdescent : baseEnd_3676183 < baseStart_3676183 := by decide
  rcases family_descends (prefixWord ++ tailWord_3676183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3676216 : List Nat := [2, 1, 2, 1, 7, 1, 2, 1, 2, 1, 3]
def baseStart_3676216 : Nat := 118140960795 + 3676216 * 2 ^ 59
def prefixEnd_3676216 : Nat := 4983230072969 + 3 ^ 40 * 3676216 * 2
def baseEnd_3676216 : Nat := 1887665797749094021693397

theorem tailTrace_3676216 : CollatzResearch.WordTrace tailWord_3676216 prefixEnd_3676216 1887665797749094021693397 := by
  unfold tailWord_3676216
  simp only [CollatzResearch.WordTrace]
  refine ⟨67041306424852377276200251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89388408566469836368267001 67041306424852377276200251)
  ·
    refine ⟨100561959637278565914300377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67041306424852377276200251 100561959637278565914300377)
    ·
      refine ⟨75421469727958924435725283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100561959637278565914300377 75421469727958924435725283)
      ·
        refine ⟨113132204591938386653587925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75421469727958924435725283 113132204591938386653587925)
        ·
          refine ⟨2651536045123555937193467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 113132204591938386653587925 2651536045123555937193467)
          ·
            refine ⟨3977304067685333905790201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2651536045123555937193467 3977304067685333905790201)
            ·
              refine ⟨2982978050764000429342651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3977304067685333905790201 2982978050764000429342651)
              ·
                refine ⟨4474467076146000644013977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2982978050764000429342651 4474467076146000644013977)
                ·
                  refine ⟨3355850307109500483010483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4474467076146000644013977 3355850307109500483010483)
                  ·
                    refine ⟨5033775460664250724515725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3355850307109500483010483 5033775460664250724515725)
                    ·
                      refine ⟨1887665797749094021693397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5033775460664250724515725 1887665797749094021693397)
                      ·
                        rfl

theorem cell23_3676216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 2, 1, 2, 1, 3].length) (baseStart_3676216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3676216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3676216 prefixEnd_3676216 := by exact prefixLift 3676216
  have htrace : WordTrace (prefixWord ++ tailWord_3676216) baseStart_3676216 baseEnd_3676216 := by
    simpa [prefixWord, tailWord_3676216, baseEnd_3676216] using wordTrace_append hprefix tailTrace_3676216
  have hstable : (prefixWord ++ tailWord_3676216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3676216).length < 2 ^ (prefixWord ++ tailWord_3676216).sum := by decide
  have hdescent : baseEnd_3676216 < baseStart_3676216 := by decide
  rcases family_descends (prefixWord ++ tailWord_3676216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3676268 : List Nat := [2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 5]
def baseStart_3676268 : Nat := 118140960795 + 3676268 * 2 ^ 59
def prefixEnd_3676268 : Nat := 4983230072969 + 3 ^ 40 * 3676268 * 2
def baseEnd_3676268 : Nat := 1887692498743127818243157

theorem tailTrace_3676268 : CollatzResearch.WordTrace tailWord_3676268 prefixEnd_3676268 1887692498743127818243157 := by
  unfold tailWord_3676268
  simp only [CollatzResearch.WordTrace]
  refine ⟨67042254722758183716646729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89389672963677578288862305 67042254722758183716646729)
  ·
    refine ⟨50281691042068637787485047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67042254722758183716646729 50281691042068637787485047)
    ·
      refine ⟨75422536563102956681227571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50281691042068637787485047 75422536563102956681227571)
      ·
        refine ⟨113133804844654435021841357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75422536563102956681227571 113133804844654435021841357)
        ·
          refine ⟨42425176816745413133190509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113133804844654435021841357 42425176816745413133190509)
          ·
            refine ⟨15909441306279529924946441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42425176816745413133190509 15909441306279529924946441)
            ·
              refine ⟨11932080979709647443709831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15909441306279529924946441 11932080979709647443709831)
              ·
                refine ⟨17898121469564471165564747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11932080979709647443709831 17898121469564471165564747)
                ·
                  refine ⟨26847182204346706748347121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17898121469564471165564747 26847182204346706748347121)
                  ·
                    refine ⟨20135386653260030061260341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26847182204346706748347121 20135386653260030061260341)
                    ·
                      refine ⟨1887692498743127818243157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20135386653260030061260341 1887692498743127818243157)
                      ·
                        rfl

theorem cell23_3676268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 5].length) (baseStart_3676268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3676268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3676268 prefixEnd_3676268 := by exact prefixLift 3676268
  have htrace : WordTrace (prefixWord ++ tailWord_3676268) baseStart_3676268 baseEnd_3676268 := by
    simpa [prefixWord, tailWord_3676268, baseEnd_3676268] using wordTrace_append hprefix tailTrace_3676268
  have hstable : (prefixWord ++ tailWord_3676268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3676268).length < 2 ^ (prefixWord ++ tailWord_3676268).sum := by decide
  have hdescent : baseEnd_3676268 < baseStart_3676268 := by decide
  rcases family_descends (prefixWord ++ tailWord_3676268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3676295 : List Nat := [1, 1, 4, 2, 1, 1, 5, 1, 2, 1, 4]
def baseStart_3676295 : Nat := 118140960795 + 3676295 * 2 ^ 59
def prefixEnd_3676295 : Nat := 4983230072969 + 3 ^ 40 * 3676295 * 2
def baseEnd_3676295 : Nat := 1887706362720799212605533

theorem tailTrace_3676295 : CollatzResearch.WordTrace tailWord_3676295 prefixEnd_3676295 1887706362720799212605533 := by
  unfold tailWord_3676295
  simp only [CollatzResearch.WordTrace]
  refine ⟨134085494216418551044526339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89390329477612367363017559 134085494216418551044526339)
  ·
    refine ⟨201128241324627826566789509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134085494216418551044526339 201128241324627826566789509)
    ·
      refine ⟨37711545248367717481273033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 201128241324627826566789509 37711545248367717481273033)
      ·
        refine ⟨28283658936275788110954775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37711545248367717481273033 28283658936275788110954775)
        ·
          refine ⟨42425488404413682166432163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28283658936275788110954775 42425488404413682166432163)
          ·
            refine ⟨63638232606620523249648245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42425488404413682166432163 63638232606620523249648245)
            ·
              refine ⟨5966084306870674054654523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63638232606620523249648245 5966084306870674054654523)
              ·
                refine ⟨8949126460306011081981785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5966084306870674054654523 8949126460306011081981785)
                ·
                  refine ⟨6711844845229508311486339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8949126460306011081981785 6711844845229508311486339)
                  ·
                    refine ⟨10067767267844262467229509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6711844845229508311486339 10067767267844262467229509)
                    ·
                      refine ⟨1887706362720799212605533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10067767267844262467229509 1887706362720799212605533)
                      ·
                        rfl

theorem cell23_3676295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 5, 1, 2, 1, 4].length) (baseStart_3676295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3676295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3676295 prefixEnd_3676295 := by exact prefixLift 3676295
  have htrace : WordTrace (prefixWord ++ tailWord_3676295) baseStart_3676295 baseEnd_3676295 := by
    simpa [prefixWord, tailWord_3676295, baseEnd_3676295] using wordTrace_append hprefix tailTrace_3676295
  have hstable : (prefixWord ++ tailWord_3676295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3676295).length < 2 ^ (prefixWord ++ tailWord_3676295).sum := by decide
  have hdescent : baseEnd_3676295 < baseStart_3676295 := by decide
  rcases family_descends (prefixWord ++ tailWord_3676295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3676322 : List Nat := [3, 3, 1, 3, 1, 1, 1, 3, 3, 4]
def baseStart_3676322 : Nat := 118140960795 + 3676322 * 2 ^ 59
def prefixEnd_3676322 : Nat := 4983230072969 + 3 ^ 40 * 3676322 * 2
def baseEnd_3676322 : Nat := 629240075566156868989303

theorem tailTrace_3676322 : CollatzResearch.WordTrace tailWord_3676322 prefixEnd_3676322 629240075566156868989303 := by
  unfold tailWord_3676322
  simp only [CollatzResearch.WordTrace]
  refine ⟨33521619746830183663939805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89390985991547156437172813 33521619746830183663939805)
  ·
    refine ⟨12570607405061318873977427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33521619746830183663939805 12570607405061318873977427)
    ·
      refine ⟨18855911107591978310966141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12570607405061318873977427 18855911107591978310966141)
      ·
        refine ⟨7070966665346991866612303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18855911107591978310966141 7070966665346991866612303)
        ·
          refine ⟨10606449998020487799918455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7070966665346991866612303 10606449998020487799918455)
          ·
            refine ⟨15909674997030731699877683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10606449998020487799918455 15909674997030731699877683)
            ·
              refine ⟨23864512495546097549816525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15909674997030731699877683 23864512495546097549816525)
              ·
                refine ⟨8949192185829786581181197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23864512495546097549816525 8949192185829786581181197)
                ·
                  refine ⟨3355947069686169967942949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8949192185829786581181197 3355947069686169967942949)
                  ·
                    refine ⟨629240075566156868989303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3355947069686169967942949 629240075566156868989303)
                    ·
                      rfl

theorem cell23_3676322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 3, 3, 4].length) (baseStart_3676322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3676322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3676322 prefixEnd_3676322 := by exact prefixLift 3676322
  have htrace : WordTrace (prefixWord ++ tailWord_3676322) baseStart_3676322 baseEnd_3676322 := by
    simpa [prefixWord, tailWord_3676322, baseEnd_3676322] using wordTrace_append hprefix tailTrace_3676322
  have hstable : (prefixWord ++ tailWord_3676322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3676322).length < 2 ^ (prefixWord ++ tailWord_3676322).sum := by decide
  have hdescent : baseEnd_3676322 < baseStart_3676322 := by decide
  rcases family_descends (prefixWord ++ tailWord_3676322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3676338 : List Nat := [3, 2, 1, 1, 1, 3, 1, 2, 1, 2, 6]
def baseStart_3676338 : Nat := 118140960795 + 3676338 * 2 ^ 59
def prefixEnd_3676338 : Nat := 4983230072969 + 3 ^ 40 * 3676338 * 2
def baseEnd_3676338 : Nat := 1887728442388942544367835

theorem tailTrace_3676338 : CollatzResearch.WordTrace tailWord_3676338 prefixEnd_3676338 1887728442388942544367835 := by
  unfold tailWord_3676338
  simp only [CollatzResearch.WordTrace]
  refine ⟨33521765638815692347085417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89391375036841846258894445 33521765638815692347085417)
  ·
    refine ⟨25141324229111769260314063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33521765638815692347085417 25141324229111769260314063)
    ·
      refine ⟨37711986343667653890471095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25141324229111769260314063 37711986343667653890471095)
      ·
        refine ⟨56567979515501480835706643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37711986343667653890471095 56567979515501480835706643)
        ·
          refine ⟨84851969273252221253559965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56567979515501480835706643 84851969273252221253559965)
          ·
            refine ⟨31819488477469582970084987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84851969273252221253559965 31819488477469582970084987)
            ·
              refine ⟨47729232716204374455127481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31819488477469582970084987 47729232716204374455127481)
              ·
                refine ⟨35796924537153280841345611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47729232716204374455127481 35796924537153280841345611)
                ·
                  refine ⟨53695386805729921262018417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35796924537153280841345611 53695386805729921262018417)
                  ·
                    refine ⟨40271540104297440946513813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53695386805729921262018417 40271540104297440946513813)
                    ·
                      refine ⟨1887728442388942544367835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40271540104297440946513813 1887728442388942544367835)
                      ·
                        rfl

theorem cell23_3676338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 2, 1, 2, 6].length) (baseStart_3676338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3676338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3676338 prefixEnd_3676338 := by exact prefixLift 3676338
  have htrace : WordTrace (prefixWord ++ tailWord_3676338) baseStart_3676338 baseEnd_3676338 := by
    simpa [prefixWord, tailWord_3676338, baseEnd_3676338] using wordTrace_append hprefix tailTrace_3676338
  have hstable : (prefixWord ++ tailWord_3676338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3676338).length < 2 ^ (prefixWord ++ tailWord_3676338).sum := by decide
  have hdescent : baseEnd_3676338 < baseStart_3676338 := by decide
  rcases family_descends (prefixWord ++ tailWord_3676338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3676356 : List Nat := [2, 3, 3, 1, 2, 3, 1, 3, 1, 4]
def baseStart_3676356 : Nat := 118140960795 + 3676356 * 2 ^ 59
def prefixEnd_3676356 : Nat := 4983230072969 + 3 ^ 40 * 3676356 * 2
def baseEnd_3676356 : Nat := 629245895013574491314251

theorem tailTrace_3676356 : CollatzResearch.WordTrace tailWord_3676356 prefixEnd_3676356 629245895013574491314251 := by
  unfold tailWord_3676356
  simp only [CollatzResearch.WordTrace]
  refine ⟨67043859534598779231248461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89391812712798372308331281 67043859534598779231248461)
  ·
    refine ⟨25141447325474542211718173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67043859534598779231248461 25141447325474542211718173)
    ·
      refine ⟨9428042747052953329394315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25141447325474542211718173 9428042747052953329394315)
      ·
        refine ⟨14142064120579429994091473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9428042747052953329394315 14142064120579429994091473)
        ·
          refine ⟨10606548090434572495568605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14142064120579429994091473 10606548090434572495568605)
          ·
            refine ⟨3977455533912964685838227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10606548090434572495568605 3977455533912964685838227)
            ·
              refine ⟨5966183300869447028757341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3977455533912964685838227 5966183300869447028757341)
              ·
                refine ⟨2237318737826042635784003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5966183300869447028757341 2237318737826042635784003)
                ·
                  refine ⟨3355978106739063953676005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2237318737826042635784003 3355978106739063953676005)
                  ·
                    refine ⟨629245895013574491314251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3355978106739063953676005 629245895013574491314251)
                    ·
                      rfl

theorem cell23_3676356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 1, 3, 1, 4].length) (baseStart_3676356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3676356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3676356 prefixEnd_3676356 := by exact prefixLift 3676356
  have htrace : WordTrace (prefixWord ++ tailWord_3676356) baseStart_3676356 baseEnd_3676356 := by
    simpa [prefixWord, tailWord_3676356, baseEnd_3676356] using wordTrace_append hprefix tailTrace_3676356
  have hstable : (prefixWord ++ tailWord_3676356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3676356).length < 2 ^ (prefixWord ++ tailWord_3676356).sum := by decide
  have hdescent : baseEnd_3676356 < baseStart_3676356 := by decide
  rcases family_descends (prefixWord ++ tailWord_3676356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3676385 : List Nat := [1, 2, 3, 1, 3, 1, 2, 2, 3, 1, 4]
def baseStart_3676385 : Nat := 118140960795 + 3676385 * 2 ^ 59
def prefixEnd_3676385 : Nat := 4983230072969 + 3 ^ 40 * 3676385 * 2
def baseEnd_3676385 : Nat := 1887752575979703860480119

theorem tailTrace_3676385 : CollatzResearch.WordTrace tailWord_3676385 prefixEnd_3676385 1887752575979703860480119 := by
  unfold tailWord_3676385
  simp only [CollatzResearch.WordTrace]
  refine ⟨134088776786092496415302609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89392517857394997610201739 134088776786092496415302609)
  ·
    refine ⟨100566582589569372311476957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134088776786092496415302609 100566582589569372311476957)
    ·
      refine ⟨37712468471088514616803859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100566582589569372311476957 37712468471088514616803859)
      ·
        refine ⟨56568702706632771925205789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37712468471088514616803859 56568702706632771925205789)
        ·
          refine ⟨21213263514987289471952171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56568702706632771925205789 21213263514987289471952171)
          ·
            refine ⟨31819895272480934207928257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21213263514987289471952171 31819895272480934207928257)
            ·
              refine ⟨23864921454360700655946193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31819895272480934207928257 23864921454360700655946193)
              ·
                refine ⟨17898691090770525491959645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23864921454360700655946193 17898691090770525491959645)
                ·
                  refine ⟨6712009159038947059484867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17898691090770525491959645 6712009159038947059484867)
                  ·
                    refine ⟨10068013738558420589227301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6712009159038947059484867 10068013738558420589227301)
                    ·
                      refine ⟨1887752575979703860480119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10068013738558420589227301 1887752575979703860480119)
                      ·
                        rfl

theorem cell23_3676385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 2, 3, 1, 4].length) (baseStart_3676385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3676385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3676385 prefixEnd_3676385 := by exact prefixLift 3676385
  have htrace : WordTrace (prefixWord ++ tailWord_3676385) baseStart_3676385 baseEnd_3676385 := by
    simpa [prefixWord, tailWord_3676385, baseEnd_3676385] using wordTrace_append hprefix tailTrace_3676385
  have hstable : (prefixWord ++ tailWord_3676385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3676385).length < 2 ^ (prefixWord ++ tailWord_3676385).sum := by decide
  have hdescent : baseEnd_3676385 < baseStart_3676385 := by decide
  rcases family_descends (prefixWord ++ tailWord_3676385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3676386 : List Nat := [3, 3, 4, 1, 1, 1, 1, 3, 6]
def baseStart_3676386 : Nat := 118140960795 + 3676386 * 2 ^ 59
def prefixEnd_3676386 : Nat := 4983230072969 + 3 ^ 40 * 3676386 * 2
def baseEnd_3676386 : Nat := 209750343273373150729735

theorem tailTrace_3676386 : CollatzResearch.WordTrace tailWord_3676386 prefixEnd_3676386 209750343273373150729735 := by
  unfold tailWord_3676386
  simp only [CollatzResearch.WordTrace]
  refine ⟨33522203314772218396522253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89392542172725915724059341 33522203314772218396522253)
  ·
    refine ⟨12570826243039581898695845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33522203314772218396522253 12570826243039581898695845)
    ·
      refine ⟨2357029920569921606005471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12570826243039581898695845 2357029920569921606005471)
      ·
        refine ⟨3535544880854882409008207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2357029920569921606005471 3535544880854882409008207)
        ·
          refine ⟨5303317321282323613512311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3535544880854882409008207 5303317321282323613512311)
          ·
            refine ⟨7954975981923485420268467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5303317321282323613512311 7954975981923485420268467)
            ·
              refine ⟨11932463972885228130402701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7954975981923485420268467 11932463972885228130402701)
              ·
                refine ⟨4474673989831960548901013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11932463972885228130402701 4474673989831960548901013)
                ·
                  refine ⟨209750343273373150729735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4474673989831960548901013 209750343273373150729735)
                  ·
                    rfl

theorem cell23_3676386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 3, 6].length) (baseStart_3676386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3676386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3676386 prefixEnd_3676386 := by exact prefixLift 3676386
  have htrace : WordTrace (prefixWord ++ tailWord_3676386) baseStart_3676386 baseEnd_3676386 := by
    simpa [prefixWord, tailWord_3676386, baseEnd_3676386] using wordTrace_append hprefix tailTrace_3676386
  have hstable : (prefixWord ++ tailWord_3676386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3676386).length < 2 ^ (prefixWord ++ tailWord_3676386).sum := by decide
  have hdescent : baseEnd_3676386 < baseStart_3676386 := by decide
  rcases family_descends (prefixWord ++ tailWord_3676386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3676402 : List Nat := [3, 2, 1, 3, 2, 2, 1, 1, 3, 1, 4]
def baseStart_3676402 : Nat := 118140960795 + 3676402 * 2 ^ 59
def prefixEnd_3676402 : Nat := 4983230072969 + 3 ^ 40 * 3676402 * 2
def baseEnd_3676402 : Nat := 1887761305150830293967541

theorem tailTrace_3676402 : CollatzResearch.WordTrace tailWord_3676402 prefixEnd_3676402 1887761305150830293967541 := by
  unfold tailWord_3676402
  simp only [CollatzResearch.WordTrace]
  refine ⟨33522349206757727079667865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89392931218020605545780973 33522349206757727079667865)
  ·
    refine ⟨25141761905068295309750899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33522349206757727079667865 25141761905068295309750899)
    ·
      refine ⟨37712642857602442964626349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25141761905068295309750899 37712642857602442964626349)
      ·
        refine ⟨14142241071600916111734881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37712642857602442964626349 14142241071600916111734881)
        ·
          refine ⟨10606680803700687083801161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14142241071600916111734881 10606680803700687083801161)
          ·
            refine ⟨7955010602775515312850871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10606680803700687083801161 7955010602775515312850871)
            ·
              refine ⟨11932515904163272969276307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7955010602775515312850871 11932515904163272969276307)
              ·
                refine ⟨17898773856244909453914461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11932515904163272969276307 17898773856244909453914461)
                ·
                  refine ⟨6712040196091841045217923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17898773856244909453914461 6712040196091841045217923)
                  ·
                    refine ⟨10068060294137761567826885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6712040196091841045217923 10068060294137761567826885)
                    ·
                      refine ⟨1887761305150830293967541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10068060294137761567826885 1887761305150830293967541)
                      ·
                        rfl

theorem cell23_3676402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_3676402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3676402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3676402 prefixEnd_3676402 := by exact prefixLift 3676402
  have htrace : WordTrace (prefixWord ++ tailWord_3676402) baseStart_3676402 baseEnd_3676402 := by
    simpa [prefixWord, tailWord_3676402, baseEnd_3676402] using wordTrace_append hprefix tailTrace_3676402
  have hstable : (prefixWord ++ tailWord_3676402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3676402).length < 2 ^ (prefixWord ++ tailWord_3676402).sum := by decide
  have hdescent : baseEnd_3676402 < baseStart_3676402 := by decide
  rcases family_descends (prefixWord ++ tailWord_3676402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3676415 : List Nat := [1, 1, 2, 2, 1, 4, 3, 2, 1, 2, 4]
def baseStart_3676415 : Nat := 118140960795 + 3676415 * 2 ^ 59
def prefixEnd_3676415 : Nat := 4983230072969 + 3 ^ 40 * 3676415 * 2
def baseEnd_3676415 : Nat := 1887767980399338743104981

theorem tailTrace_3676415 : CollatzResearch.WordTrace tailWord_3676415 prefixEnd_3676415 1887767980399338743104981 := by
  unfold tailWord_3676415
  simp only [CollatzResearch.WordTrace]
  refine ⟨134089870975983811538894699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89393247317322541025929799 134089870975983811538894699)
  ·
    refine ⟨201134806463975717308342049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134089870975983811538894699 201134806463975717308342049)
    ·
      refine ⟨150851104847981787981256537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201134806463975717308342049 150851104847981787981256537)
      ·
        refine ⟨113138328635986340985942403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150851104847981787981256537 113138328635986340985942403)
        ·
          refine ⟨169707492953979511478913605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113138328635986340985942403 169707492953979511478913605)
          ·
            refine ⟨31820154928871158402296301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 169707492953979511478913605 31820154928871158402296301)
            ·
              refine ⟨11932558098326684400861113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31820154928871158402296301 11932558098326684400861113)
              ·
                refine ⟨8949418573745013300645835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11932558098326684400861113 8949418573745013300645835)
                ·
                  refine ⟨13424127860617519950968753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8949418573745013300645835 13424127860617519950968753)
                  ·
                    refine ⟨10068095895463139963226565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13424127860617519950968753 10068095895463139963226565)
                    ·
                      refine ⟨1887767980399338743104981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10068095895463139963226565 1887767980399338743104981)
                      ·
                        rfl

theorem cell23_3676415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 2, 1, 2, 4].length) (baseStart_3676415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3676415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3676415 prefixEnd_3676415 := by exact prefixLift 3676415
  have htrace : WordTrace (prefixWord ++ tailWord_3676415) baseStart_3676415 baseEnd_3676415 := by
    simpa [prefixWord, tailWord_3676415, baseEnd_3676415] using wordTrace_append hprefix tailTrace_3676415
  have hstable : (prefixWord ++ tailWord_3676415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3676415).length < 2 ^ (prefixWord ++ tailWord_3676415).sum := by decide
  have hdescent : baseEnd_3676415 < baseStart_3676415 := by decide
  rcases family_descends (prefixWord ++ tailWord_3676415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3676442 : List Nat := [3, 1, 1, 3, 4, 2, 1, 8]
def baseStart_3676442 : Nat := 118140960795 + 3676442 * 2 ^ 59
def prefixEnd_3676442 : Nat := 4983230072969 + 3 ^ 40 * 3676442 * 2
def baseEnd_3676442 : Nat := 69917846088037412498791

theorem tailTrace_3676442 : CollatzResearch.WordTrace tailWord_3676442 prefixEnd_3676442 69917846088037412498791 := by
  unfold tailWord_3676442
  simp only [CollatzResearch.WordTrace]
  refine ⟨33522713936721498787531895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89393903831257330100085053 33522713936721498787531895)
  ·
    refine ⟨50284070905082248181297843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33522713936721498787531895 50284070905082248181297843)
    ·
      refine ⟨75426106357623372271946765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50284070905082248181297843 75426106357623372271946765)
      ·
        refine ⟨28284789884108764601980037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75426106357623372271946765 28284789884108764601980037)
        ·
          refine ⟨5303398103270393362871257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28284789884108764601980037 5303398103270393362871257)
          ·
            refine ⟨3977548577452795022153443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5303398103270393362871257 3977548577452795022153443)
            ·
              refine ⟨5966322866179192533230165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3977548577452795022153443 5966322866179192533230165)
              ·
                refine ⟨69917846088037412498791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5966322866179192533230165 69917846088037412498791)
                ·
                  rfl

theorem cell23_3676442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 1, 8].length) (baseStart_3676442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3676442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3676442 prefixEnd_3676442 := by exact prefixLift 3676442
  have htrace : WordTrace (prefixWord ++ tailWord_3676442) baseStart_3676442 baseEnd_3676442 := by
    simpa [prefixWord, tailWord_3676442, baseEnd_3676442] using wordTrace_append hprefix tailTrace_3676442
  have hstable : (prefixWord ++ tailWord_3676442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3676442).length < 2 ^ (prefixWord ++ tailWord_3676442).sum := by decide
  have hdescent : baseEnd_3676442 < baseStart_3676442 := by decide
  rcases family_descends (prefixWord ++ tailWord_3676442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3676446 : List Nat := [4, 3, 2, 1, 1, 1, 2, 3, 2, 4]
def baseStart_3676446 : Nat := 118140960795 + 3676446 * 2 ^ 59
def prefixEnd_3676446 : Nat := 4983230072969 + 3 ^ 40 * 3676446 * 2
def baseEnd_3676446 : Nat := 629261299433209373939113

theorem tailTrace_3676446 : CollatzResearch.WordTrace tailWord_3676446 prefixEnd_3676446 629261299433209373939113 := by
  unfold tailWord_3676446
  simp only [CollatzResearch.WordTrace]
  refine ⟨16761375204858937979159149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89394001092581002555515461 16761375204858937979159149)
  ·
    refine ⟨6285515701822101742184681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16761375204858937979159149 6285515701822101742184681)
    ·
      refine ⟨4714136776366576306638511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6285515701822101742184681 4714136776366576306638511)
      ·
        refine ⟨7071205164549864459957767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4714136776366576306638511 7071205164549864459957767)
        ·
          refine ⟨10606807746824796689936651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7071205164549864459957767 10606807746824796689936651)
          ·
            refine ⟨15910211620237195034904977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10606807746824796689936651 15910211620237195034904977)
            ·
              refine ⟨11932658715177896276178733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15910211620237195034904977 11932658715177896276178733)
              ·
                refine ⟨4474747018191711103567025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11932658715177896276178733 4474747018191711103567025)
                ·
                  refine ⟨3356060263643783327675269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4474747018191711103567025 3356060263643783327675269)
                  ·
                    refine ⟨629261299433209373939113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3356060263643783327675269 629261299433209373939113)
                    ·
                      rfl

theorem cell23_3676446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_3676446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3676446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3676446 prefixEnd_3676446 := by exact prefixLift 3676446
  have htrace : WordTrace (prefixWord ++ tailWord_3676446) baseStart_3676446 baseEnd_3676446 := by
    simpa [prefixWord, tailWord_3676446, baseEnd_3676446] using wordTrace_append hprefix tailTrace_3676446
  have hstable : (prefixWord ++ tailWord_3676446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3676446).length < 2 ^ (prefixWord ++ tailWord_3676446).sum := by decide
  have hdescent : baseEnd_3676446 < baseStart_3676446 := by decide
  rcases family_descends (prefixWord ++ tailWord_3676446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3676452 : List Nat := [2, 3, 1, 3, 1, 2, 1, 3, 1, 3, 3]
def baseStart_3676452 : Nat := 118140960795 + 3676452 * 2 ^ 59
def prefixEnd_3676452 : Nat := 4983230072969 + 3 ^ 40 * 3676452 * 2
def baseEnd_3676452 : Nat := 1887786979183555098342311

theorem tailTrace_3676452 : CollatzResearch.WordTrace tailWord_3676452 prefixEnd_3676452 1887786979183555098342311 := by
  unfold tailWord_3676452
  simp only [CollatzResearch.WordTrace]
  refine ⟨67045610238424883428995805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89394146984566511238661073 67045610238424883428995805)
  ·
    refine ⟨25142103839409331285873427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67045610238424883428995805 25142103839409331285873427)
    ·
      refine ⟨37713155759113996928810141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25142103839409331285873427 37713155759113996928810141)
      ·
        refine ⟨14142433409667748848303803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37713155759113996928810141 14142433409667748848303803)
        ·
          refine ⟨21213650114501623272455705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14142433409667748848303803 21213650114501623272455705)
          ·
            refine ⟨15910237585876217454341779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21213650114501623272455705 15910237585876217454341779)
            ·
              refine ⟨23865356378814326181512669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15910237585876217454341779 23865356378814326181512669)
              ·
                refine ⟨8949508642055372318067251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23865356378814326181512669 8949508642055372318067251)
                ·
                  refine ⟨13424262963083058477100877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8949508642055372318067251 13424262963083058477100877)
                  ·
                    refine ⟨5034098611156146928912829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13424262963083058477100877 5034098611156146928912829)
                    ·
                      refine ⟨1887786979183555098342311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5034098611156146928912829 1887786979183555098342311)
                      ·
                        rfl

theorem cell23_3676452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 3, 1, 3, 3].length) (baseStart_3676452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3676452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3676452 prefixEnd_3676452 := by exact prefixLift 3676452
  have htrace : WordTrace (prefixWord ++ tailWord_3676452) baseStart_3676452 baseEnd_3676452 := by
    simpa [prefixWord, tailWord_3676452, baseEnd_3676452] using wordTrace_append hprefix tailTrace_3676452
  have hstable : (prefixWord ++ tailWord_3676452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3676452).length < 2 ^ (prefixWord ++ tailWord_3676452).sum := by decide
  have hdescent : baseEnd_3676452 < baseStart_3676452 := by decide
  rcases family_descends (prefixWord ++ tailWord_3676452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3676479 : List Nat := [1, 1, 2, 2, 4, 1, 3, 3, 1, 3, 2]
def baseStart_3676479 : Nat := 118140960795 + 3676479 * 2 ^ 59
def prefixEnd_3676479 : Nat := 4983230072969 + 3 ^ 40 * 3676479 * 2
def baseEnd_3676479 : Nat := 1887800843161226492704687

theorem tailTrace_3676479 : CollatzResearch.WordTrace tailWord_3676479 prefixEnd_3676479 1887800843161226492704687 := by
  unfold tailWord_3676479
  simp only [CollatzResearch.WordTrace]
  refine ⟨134092205247751950469224491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89394803498501300312816327 134092205247751950469224491)
  ·
    refine ⟨201138307871627925703836737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134092205247751950469224491 201138307871627925703836737)
    ·
      refine ⟨150853730903720944277877553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201138307871627925703836737 150853730903720944277877553)
      ·
        refine ⟨113140298177790708208408165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150853730903720944277877553 113140298177790708208408165)
        ·
          refine ⟨21213805908335757789076531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 113140298177790708208408165 21213805908335757789076531)
          ·
            refine ⟨31820708862503636683614797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21213805908335757789076531 31820708862503636683614797)
            ·
              refine ⟨11932765823438863756355549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31820708862503636683614797 11932765823438863756355549)
              ·
                refine ⟨4474787183789573908633331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11932765823438863756355549 4474787183789573908633331)
                ·
                  refine ⟨6712180775684360862949997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4474787183789573908633331 6712180775684360862949997)
                  ·
                    refine ⟨2517067790881635323606249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6712180775684360862949997 2517067790881635323606249)
                    ·
                      refine ⟨1887800843161226492704687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2517067790881635323606249 1887800843161226492704687)
                      ·
                        rfl

theorem cell23_3676479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 3, 1, 3, 2].length) (baseStart_3676479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3676479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3676479 prefixEnd_3676479 := by exact prefixLift 3676479
  have htrace : WordTrace (prefixWord ++ tailWord_3676479) baseStart_3676479 baseEnd_3676479 := by
    simpa [prefixWord, tailWord_3676479, baseEnd_3676479] using wordTrace_append hprefix tailTrace_3676479
  have hstable : (prefixWord ++ tailWord_3676479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3676479).length < 2 ^ (prefixWord ++ tailWord_3676479).sum := by decide
  have hdescent : baseEnd_3676479 < baseStart_3676479 := by decide
  rcases family_descends (prefixWord ++ tailWord_3676479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3676495 : List Nat := [1, 1, 2, 1, 1, 2, 1, 5, 2, 4, 3]
def baseStart_3676495 : Nat := 118140960795 + 3676495 * 2 ^ 59
def prefixEnd_3676495 : Nat := 4983230072969 + 3 ^ 40 * 3676495 * 2
def baseEnd_3676495 : Nat := 1887809058851698430104613

theorem tailTrace_3676495 : CollatzResearch.WordTrace tailWord_3676495 prefixEnd_3676495 1887809058851698430104613 := by
  unfold tailWord_3676495
  simp only [CollatzResearch.WordTrace]
  refine ⟨134092788815693985201806939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89395192543795990134537959 134092788815693985201806939)
  ·
    refine ⟨201139183223540977802710409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134092788815693985201806939 201139183223540977802710409)
    ·
      refine ⟨150854387417655733352032807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201139183223540977802710409 150854387417655733352032807)
      ·
        refine ⟨226281581126483600028049211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150854387417655733352032807 226281581126483600028049211)
        ·
          refine ⟨339422371689725400042073817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226281581126483600028049211 339422371689725400042073817)
          ·
            refine ⟨254566778767294050031555363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 339422371689725400042073817 254566778767294050031555363)
            ·
              refine ⟨381850168150941075047333045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 254566778767294050031555363 381850168150941075047333045)
              ·
                refine ⟨35798453264150725785687473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 381850168150941075047333045 35798453264150725785687473)
                ·
                  refine ⟨26848839948113044339265605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35798453264150725785687473 26848839948113044339265605)
                  ·
                    refine ⟨5034157490271195813612301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26848839948113044339265605 5034157490271195813612301)
                    ·
                      refine ⟨1887809058851698430104613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5034157490271195813612301 1887809058851698430104613)
                      ·
                        rfl

theorem cell23_3676495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 5, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 5, 2, 4, 3].length) (baseStart_3676495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3676495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3676495 prefixEnd_3676495 := by exact prefixLift 3676495
  have htrace : WordTrace (prefixWord ++ tailWord_3676495) baseStart_3676495 baseEnd_3676495 := by
    simpa [prefixWord, tailWord_3676495, baseEnd_3676495] using wordTrace_append hprefix tailTrace_3676495
  have hstable : (prefixWord ++ tailWord_3676495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3676495).length < 2 ^ (prefixWord ++ tailWord_3676495).sum := by decide
  have hdescent : baseEnd_3676495 < baseStart_3676495 := by decide
  rcases family_descends (prefixWord ++ tailWord_3676495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3676510 : List Nat := [4, 4, 2, 1, 1, 2, 2, 7]
def baseStart_3676510 : Nat := 118140960795 + 3676510 * 2 ^ 59
def prefixEnd_3676510 : Nat := 4983230072969 + 3 ^ 40 * 3676510 * 2
def baseEnd_3676510 : Nat := 69919139298574661904335

theorem tailTrace_3676510 : CollatzResearch.WordTrace tailWord_3676510 prefixEnd_3676510 69919139298574661904335 := by
  unfold tailWord_3676510
  simp only [CollatzResearch.WordTrace]
  refine ⟨16761666988829955345450373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89395557273759761842401989 16761666988829955345450373)
  ·
    refine ⟨3142812560405616627271945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16761666988829955345450373 3142812560405616627271945)
    ·
      refine ⟨2357109420304212470453959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3142812560405616627271945 2357109420304212470453959)
      ·
        refine ⟨3535664130456318705680939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2357109420304212470453959 3535664130456318705680939)
        ·
          refine ⟨5303496195684478058521409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3535664130456318705680939 5303496195684478058521409)
          ·
            refine ⟨3977622146763358543891057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5303496195684478058521409 3977622146763358543891057)
            ·
              refine ⟨2983216610072518907918293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3977622146763358543891057 2983216610072518907918293)
              ·
                refine ⟨69919139298574661904335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2983216610072518907918293 69919139298574661904335)
                ·
                  rfl

theorem cell23_3676510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 2, 7].length) (baseStart_3676510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3676510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3676510 prefixEnd_3676510 := by exact prefixLift 3676510
  have htrace : WordTrace (prefixWord ++ tailWord_3676510) baseStart_3676510 baseEnd_3676510 := by
    simpa [prefixWord, tailWord_3676510, baseEnd_3676510] using wordTrace_append hprefix tailTrace_3676510
  have hstable : (prefixWord ++ tailWord_3676510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3676510).length < 2 ^ (prefixWord ++ tailWord_3676510).sum := by decide
  have hdescent : baseEnd_3676510 < baseStart_3676510 := by decide
  rcases family_descends (prefixWord ++ tailWord_3676510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3676515 : List Nat := [1, 1, 1, 5, 2, 1, 1, 4, 7]
def baseStart_3676515 : Nat := 118140960795 + 3676515 * 2 ^ 59
def prefixEnd_3676515 : Nat := 4983230072969 + 3 ^ 40 * 3676515 * 2
def baseEnd_3676515 : Nat := 209757703162754261317169

theorem tailTrace_3676515 : CollatzResearch.WordTrace tailWord_3676515 prefixEnd_3676515 209757703162754261317169 := by
  unfold tailWord_3676515
  simp only [CollatzResearch.WordTrace]
  refine ⟨134093518275621528617534999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89395678850414352411689999 134093518275621528617534999)
  ·
    refine ⟨201140277413432292926302499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134093518275621528617534999 201140277413432292926302499)
    ·
      refine ⟨301710416120148439389453749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201140277413432292926302499 301710416120148439389453749)
      ·
        refine ⟨28285351511263916192761289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 301710416120148439389453749 28285351511263916192761289)
        ·
          refine ⟨21214013633447937144570967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28285351511263916192761289 21214013633447937144570967)
          ·
            refine ⟨31821020450171905716856451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21214013633447937144570967 31821020450171905716856451)
            ·
              refine ⟨47731530675257858575284677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31821020450171905716856451 47731530675257858575284677)
              ·
                refine ⟨8949662001610848482865877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47731530675257858575284677 8949662001610848482865877)
                ·
                  refine ⟨209757703162754261317169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8949662001610848482865877 209757703162754261317169)
                  ·
                    rfl

theorem cell23_3676515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 4, 7].length) (baseStart_3676515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3676515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3676515 prefixEnd_3676515 := by exact prefixLift 3676515
  have htrace : WordTrace (prefixWord ++ tailWord_3676515) baseStart_3676515 baseEnd_3676515 := by
    simpa [prefixWord, tailWord_3676515, baseEnd_3676515] using wordTrace_append hprefix tailTrace_3676515
  have hstable : (prefixWord ++ tailWord_3676515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3676515).length < 2 ^ (prefixWord ++ tailWord_3676515).sum := by decide
  have hdescent : baseEnd_3676515 < baseStart_3676515 := by decide
  rcases family_descends (prefixWord ++ tailWord_3676515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3676555 : List Nat := [1, 1, 1, 1, 4, 4, 1, 1, 1, 1, 7]
def baseStart_3676555 : Nat := 118140960795 + 3676555 * 2 ^ 59
def prefixEnd_3676555 : Nat := 4983230072969 + 3 ^ 40 * 3676555 * 2
def baseEnd_3676555 : Nat := 1887839867690968195354337

theorem tailTrace_3676555 : CollatzResearch.WordTrace tailWord_3676555 prefixEnd_3676555 1887839867690968195354337 := by
  unfold tailWord_3676555
  simp only [CollatzResearch.WordTrace]
  refine ⟨134094977195476615448991119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89396651463651076965994079 134094977195476615448991119)
  ·
    refine ⟨201142465793214923173486679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134094977195476615448991119 201142465793214923173486679)
    ·
      refine ⟨301713698689822384760230019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201142465793214923173486679 301713698689822384760230019)
      ·
        refine ⟨452570548034733577140345029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301713698689822384760230019 452570548034733577140345029)
        ·
          refine ⟨84856977756512545713814693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 452570548034733577140345029 84856977756512545713814693)
          ·
            refine ⟨15910683329346102321340255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84856977756512545713814693 15910683329346102321340255)
            ·
              refine ⟨23866024994019153482010383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15910683329346102321340255 23866024994019153482010383)
              ·
                refine ⟨35799037491028730223015575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23866024994019153482010383 35799037491028730223015575)
                ·
                  refine ⟨53698556236543095334523363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35799037491028730223015575 53698556236543095334523363)
                  ·
                    refine ⟨80547834354814643001785045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53698556236543095334523363 80547834354814643001785045)
                    ·
                      refine ⟨1887839867690968195354337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 80547834354814643001785045 1887839867690968195354337)
                      ·
                        rfl

theorem cell23_3676555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 1, 1, 1, 7].length) (baseStart_3676555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3676555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3676555 prefixEnd_3676555 := by exact prefixLift 3676555
  have htrace : WordTrace (prefixWord ++ tailWord_3676555) baseStart_3676555 baseEnd_3676555 := by
    simpa [prefixWord, tailWord_3676555, baseEnd_3676555] using wordTrace_append hprefix tailTrace_3676555
  have hstable : (prefixWord ++ tailWord_3676555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3676555).length < 2 ^ (prefixWord ++ tailWord_3676555).sum := by decide
  have hdescent : baseEnd_3676555 < baseStart_3676555 := by decide
  rcases family_descends (prefixWord ++ tailWord_3676555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3676643 : List Nat := [1, 1, 1, 6, 3, 1, 2, 3, 1, 4]
def baseStart_3676643 : Nat := 118140960795 + 3676643 * 2 ^ 59
def prefixEnd_3676643 : Nat := 4983230072969 + 3 ^ 40 * 3676643 * 2
def baseEnd_3676643 : Nat := 629295017996187950351311

theorem tailTrace_3676643 : CollatzResearch.WordTrace tailWord_3676643 prefixEnd_3676643 629295017996187950351311 := by
  unfold tailWord_3676643
  simp only [CollatzResearch.WordTrace]
  refine ⟨134098186819157806478194583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89398791212771870985463055 134098186819157806478194583)
  ·
    refine ⟨201147280228736709717291875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134098186819157806478194583 201147280228736709717291875)
    ·
      refine ⟨301720920343105064575937813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201147280228736709717291875 301720920343105064575937813)
      ·
        refine ⟨14143168141083049901997085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 301720920343105064575937813 14143168141083049901997085)
        ·
          refine ⟨5303688052906143713248907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14143168141083049901997085 5303688052906143713248907)
          ·
            refine ⟨7955532079359215569873361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5303688052906143713248907 7955532079359215569873361)
            ·
              refine ⟨5966649059519411677405021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7955532079359215569873361 5966649059519411677405021)
              ·
                refine ⟨2237493397319779379026883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5966649059519411677405021 2237493397319779379026883)
                ·
                  refine ⟨3356240095979669068540325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2237493397319779379026883 3356240095979669068540325)
                  ·
                    refine ⟨629295017996187950351311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3356240095979669068540325 629295017996187950351311)
                    ·
                      rfl

theorem cell23_3676643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 2, 3, 1, 4].length) (baseStart_3676643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3676643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3676643 prefixEnd_3676643 := by exact prefixLift 3676643
  have htrace : WordTrace (prefixWord ++ tailWord_3676643) baseStart_3676643 baseEnd_3676643 := by
    simpa [prefixWord, tailWord_3676643, baseEnd_3676643] using wordTrace_append hprefix tailTrace_3676643
  have hstable : (prefixWord ++ tailWord_3676643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3676643).length < 2 ^ (prefixWord ++ tailWord_3676643).sum := by decide
  have hdescent : baseEnd_3676643 < baseStart_3676643 := by decide
  rcases family_descends (prefixWord ++ tailWord_3676643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3676659 : List Nat := [1, 1, 1, 2, 2, 2, 4, 1, 4, 3, 2]
def baseStart_3676659 : Nat := 118140960795 + 3676659 * 2 ^ 59
def prefixEnd_3676659 : Nat := 4983230072969 + 3 ^ 40 * 3676659 * 2
def baseEnd_3676659 : Nat := 1887893269679035788453859

theorem tailTrace_3676659 : CollatzResearch.WordTrace tailWord_3676659 prefixEnd_3676659 1887893269679035788453859 := by
  unfold tailWord_3676659
  simp only [CollatzResearch.WordTrace]
  refine ⟨134098770387099841210777031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89399180258066560807184687 134098770387099841210777031)
  ·
    refine ⟨201148155580649761816165547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134098770387099841210777031 201148155580649761816165547)
    ·
      refine ⟨301722233370974642724248321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201148155580649761816165547 301722233370974642724248321)
      ·
        refine ⟨226291675028230982043186241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 301722233370974642724248321 226291675028230982043186241)
        ·
          refine ⟨169718756271173236532389681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226291675028230982043186241 169718756271173236532389681)
          ·
            refine ⟨127289067203379927399292261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169718756271173236532389681 127289067203379927399292261)
            ·
              refine ⟨23866700100633736387367299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 127289067203379927399292261 23866700100633736387367299)
              ·
                refine ⟨35800050150950604581050949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23866700100633736387367299 35800050150950604581050949)
                ·
                  refine ⟨6712509403303238358947053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35800050150950604581050949 6712509403303238358947053)
                  ·
                    refine ⟨2517191026238714384605145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6712509403303238358947053 2517191026238714384605145)
                    ·
                      refine ⟨1887893269679035788453859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2517191026238714384605145 1887893269679035788453859)
                      ·
                        rfl

theorem cell23_3676659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 1, 4, 3, 2].length) (baseStart_3676659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3676659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3676659 prefixEnd_3676659 := by exact prefixLift 3676659
  have htrace : WordTrace (prefixWord ++ tailWord_3676659) baseStart_3676659 baseEnd_3676659 := by
    simpa [prefixWord, tailWord_3676659, baseEnd_3676659] using wordTrace_append hprefix tailTrace_3676659
  have hstable : (prefixWord ++ tailWord_3676659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3676659).length < 2 ^ (prefixWord ++ tailWord_3676659).sum := by decide
  have hdescent : baseEnd_3676659 < baseStart_3676659 := by decide
  rcases family_descends (prefixWord ++ tailWord_3676659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3676676 : List Nat := [2, 3, 2, 3, 1, 1, 1, 2, 1, 5, 2]
def baseStart_3676676 : Nat := 118140960795 + 3676676 * 2 ^ 59
def prefixEnd_3676676 : Nat := 4983230072969 + 3 ^ 40 * 3676676 * 2
def baseEnd_3676676 : Nat := 1887901998850162221941281

theorem tailTrace_3676676 : CollatzResearch.WordTrace tailWord_3676676 prefixEnd_3676676 1887901998850162221941281 := by
  unfold tailWord_3676676
  simp only [CollatzResearch.WordTrace]
  refine ⟨67049695214019126557072941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89399593618692168742763921 67049695214019126557072941)
  ·
    refine ⟨25143635705257172458902353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67049695214019126557072941 25143635705257172458902353)
    ·
      refine ⟨18857726778942879344176765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25143635705257172458902353 18857726778942879344176765)
      ·
        refine ⟨7071647542103579754066287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18857726778942879344176765 7071647542103579754066287)
        ·
          refine ⟨10607471313155369631099431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7071647542103579754066287 10607471313155369631099431)
          ·
            refine ⟨15911206969733054446649147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10607471313155369631099431 15911206969733054446649147)
            ·
              refine ⟨23866810454599581669973721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15911206969733054446649147 23866810454599581669973721)
              ·
                refine ⟨17900107840949686252480291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23866810454599581669973721 17900107840949686252480291)
                ·
                  refine ⟨26850161761424529378720437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17900107840949686252480291 26850161761424529378720437)
                  ·
                    refine ⟨2517202665133549629255041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26850161761424529378720437 2517202665133549629255041)
                    ·
                      refine ⟨1887901998850162221941281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2517202665133549629255041 1887901998850162221941281)
                      ·
                        rfl

theorem cell23_3676676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 2, 1, 5, 2].length) (baseStart_3676676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3676676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3676676 prefixEnd_3676676 := by exact prefixLift 3676676
  have htrace : WordTrace (prefixWord ++ tailWord_3676676) baseStart_3676676 baseEnd_3676676 := by
    simpa [prefixWord, tailWord_3676676, baseEnd_3676676] using wordTrace_append hprefix tailTrace_3676676
  have hstable : (prefixWord ++ tailWord_3676676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3676676).length < 2 ^ (prefixWord ++ tailWord_3676676).sum := by decide
  have hdescent : baseEnd_3676676 < baseStart_3676676 := by decide
  rcases family_descends (prefixWord ++ tailWord_3676676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3676686 : List Nat := [4, 1, 1, 2, 3, 2, 2, 2, 1, 5]
def baseStart_3676686 : Nat := 118140960795 + 3676686 * 2 ^ 59
def prefixEnd_3676686 : Nat := 4983230072969 + 3 ^ 40 * 3676686 * 2
def baseEnd_3676686 : Nat := 629302377885569060938745

theorem tailTrace_3676686 : CollatzResearch.WordTrace tailWord_3676686 prefixEnd_3676686 629302377885569060938745 := by
  unfold tailWord_3676686
  simp only [CollatzResearch.WordTrace]
  refine ⟨16762469394750253102751239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89399836772001349881339941 16762469394750253102751239)
  ·
    refine ⟨25143704092125379654126859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16762469394750253102751239 25143704092125379654126859)
    ·
      refine ⟨37715556138188069481190289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25143704092125379654126859 37715556138188069481190289)
      ·
        refine ⟨28286667103641052110892717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37715556138188069481190289 28286667103641052110892717)
        ·
          refine ⟨10607500163865394541584769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28286667103641052110892717 10607500163865394541584769)
          ·
            refine ⟨7955625122899045906188577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10607500163865394541584769 7955625122899045906188577)
            ·
              refine ⟨5966718842174284429641433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7955625122899045906188577 5966718842174284429641433)
              ·
                refine ⟨4475039131630713322231075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5966718842174284429641433 4475039131630713322231075)
                ·
                  refine ⟨6712558697446069983346613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4475039131630713322231075 6712558697446069983346613)
                  ·
                    refine ⟨629302377885569060938745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6712558697446069983346613 629302377885569060938745)
                    ·
                      rfl

theorem cell23_3676686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 2, 2, 1, 5].length) (baseStart_3676686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3676686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3676686 prefixEnd_3676686 := by exact prefixLift 3676686
  have htrace : WordTrace (prefixWord ++ tailWord_3676686) baseStart_3676686 baseEnd_3676686 := by
    simpa [prefixWord, tailWord_3676686, baseEnd_3676686] using wordTrace_append hprefix tailTrace_3676686
  have hstable : (prefixWord ++ tailWord_3676686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3676686).length < 2 ^ (prefixWord ++ tailWord_3676686).sum := by decide
  have hdescent : baseEnd_3676686 < baseStart_3676686 := by decide
  rcases family_descends (prefixWord ++ tailWord_3676686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3676700 : List Nat := [2, 2, 3, 1, 2, 4, 1, 3, 1, 1, 3]
def baseStart_3676700 : Nat := 118140960795 + 3676700 * 2 ^ 59
def prefixEnd_3676700 : Nat := 4983230072969 + 3 ^ 40 * 3676700 * 2
def baseEnd_3676700 : Nat := 1887914322385870128041171

theorem tailTrace_3676700 : CollatzResearch.WordTrace tailWord_3676700 prefixEnd_3676700 1887914322385870128041171 := by
  unfold tailWord_3676700
  simp only [CollatzResearch.WordTrace]
  refine ⟨67050132889975652606509777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89400177186634203475346369 67050132889975652606509777)
  ·
    refine ⟨50287599667481739454882333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67050132889975652606509777 50287599667481739454882333)
    ·
      refine ⟨18857849875305652295580875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50287599667481739454882333 18857849875305652295580875)
      ·
        refine ⟨28286774812958478443371313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18857849875305652295580875 28286774812958478443371313)
        ·
          refine ⟨21215081109718858832528485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28286774812958478443371313 21215081109718858832528485)
          ·
            refine ⟨3977827708072286031099091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21215081109718858832528485 3977827708072286031099091)
            ·
              refine ⟨5966741562108429046648637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3977827708072286031099091 5966741562108429046648637)
              ·
                refine ⟨2237528085790660892493239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5966741562108429046648637 2237528085790660892493239)
                ·
                  refine ⟨3356292128685991338739859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2237528085790660892493239 3356292128685991338739859)
                  ·
                    refine ⟨5034438193028987008109789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3356292128685991338739859 5034438193028987008109789)
                    ·
                      refine ⟨1887914322385870128041171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5034438193028987008109789 1887914322385870128041171)
                      ·
                        rfl

theorem cell23_3676700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 1, 3, 1, 1, 3].length) (baseStart_3676700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3676700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3676700 prefixEnd_3676700 := by exact prefixLift 3676700
  have htrace : WordTrace (prefixWord ++ tailWord_3676700) baseStart_3676700 baseEnd_3676700 := by
    simpa [prefixWord, tailWord_3676700, baseEnd_3676700] using wordTrace_append hprefix tailTrace_3676700
  have hstable : (prefixWord ++ tailWord_3676700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3676700).length < 2 ^ (prefixWord ++ tailWord_3676700).sum := by decide
  have hdescent : baseEnd_3676700 < baseStart_3676700 := by decide
  rcases family_descends (prefixWord ++ tailWord_3676700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3676726 : List Nat := [5, 1, 2, 1, 2, 1, 2, 2, 1, 1, 5]
def baseStart_3676726 : Nat := 118140960795 + 3676726 * 2 ^ 59
def prefixEnd_3676726 : Nat := 4983230072969 + 3 ^ 40 * 3676726 * 2
def baseEnd_3676726 : Nat := 1887927672882887026316051

theorem tailTrace_3676726 : CollatzResearch.WordTrace tailWord_3676726 prefixEnd_3676726 1887927672882887026316051 := by
  unfold tailWord_3676726
  simp only [CollatzResearch.WordTrace]
  refine ⟨8381325879866069478341627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 89400809385238074435644021 8381325879866069478341627)
  ·
    refine ⟨12571988819799104217512441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8381325879866069478341627 12571988819799104217512441)
    ·
      refine ⟨9428991614849328163134331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12571988819799104217512441 9428991614849328163134331)
      ·
        refine ⟨14143487422273992244701497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9428991614849328163134331 14143487422273992244701497)
        ·
          refine ⟨10607615566705494183526123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14143487422273992244701497 10607615566705494183526123)
          ·
            refine ⟨15911423350058241275289185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10607615566705494183526123 15911423350058241275289185)
            ·
              refine ⟨11933567512543680956466889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15911423350058241275289185 11933567512543680956466889)
              ·
                refine ⟨8950175634407760717350167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11933567512543680956466889 8950175634407760717350167)
                ·
                  refine ⟨13425263451611641076025251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8950175634407760717350167 13425263451611641076025251)
                  ·
                    refine ⟨20137895177417461614037877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13425263451611641076025251 20137895177417461614037877)
                    ·
                      refine ⟨1887927672882887026316051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20137895177417461614037877 1887927672882887026316051)
                      ·
                        rfl

theorem cell23_3676726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_3676726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3676726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3676726 prefixEnd_3676726 := by exact prefixLift 3676726
  have htrace : WordTrace (prefixWord ++ tailWord_3676726) baseStart_3676726 baseEnd_3676726 := by
    simpa [prefixWord, tailWord_3676726, baseEnd_3676726] using wordTrace_append hprefix tailTrace_3676726
  have hstable : (prefixWord ++ tailWord_3676726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3676726).length < 2 ^ (prefixWord ++ tailWord_3676726).sum := by decide
  have hdescent : baseEnd_3676726 < baseStart_3676726 := by decide
  rcases family_descends (prefixWord ++ tailWord_3676726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3676733 : List Nat := [1, 4, 1, 3, 2, 1, 4, 1, 2, 4]
def baseStart_3676733 : Nat := 118140960795 + 3676733 * 2 ^ 59
def prefixEnd_3676733 : Nat := 4983230072969 + 3 ^ 40 * 3676733 * 2
def baseEnd_3676733 : Nat := 629310422415822832976173

theorem tailTrace_3676733 : CollatzResearch.WordTrace tailWord_3676733 prefixEnd_3676733 629310422415822832976173 := by
  unfold tailWord_3676733
  simp only [CollatzResearch.WordTrace]
  refine ⟨134101469388831751848970853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89400979592554501232647235 134101469388831751848970853)
  ·
    refine ⟨25144025510405953471682035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134101469388831751848970853 25144025510405953471682035)
    ·
      refine ⟨37716038265608930207523053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25144025510405953471682035 37716038265608930207523053)
      ·
        refine ⟨14143514349603348827821145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37716038265608930207523053 14143514349603348827821145)
        ·
          refine ⟨10607635762202511620865859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14143514349603348827821145 10607635762202511620865859)
          ·
            refine ⟨15911453643303767431298789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10607635762202511620865859 15911453643303767431298789)
            ·
              refine ⟨2983397558119456393368523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15911453643303767431298789 2983397558119456393368523)
              ·
                refine ⟨4475096337179184590052785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2983397558119456393368523 4475096337179184590052785)
                ·
                  refine ⟨3356322252884388442539589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4475096337179184590052785 3356322252884388442539589)
                  ·
                    refine ⟨629310422415822832976173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3356322252884388442539589 629310422415822832976173)
                    ·
                      rfl

theorem cell23_3676733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 4, 1, 2, 4].length) (baseStart_3676733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3676733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3676733 prefixEnd_3676733 := by exact prefixLift 3676733
  have htrace : WordTrace (prefixWord ++ tailWord_3676733) baseStart_3676733 baseEnd_3676733 := by
    simpa [prefixWord, tailWord_3676733, baseEnd_3676733] using wordTrace_append hprefix tailTrace_3676733
  have hstable : (prefixWord ++ tailWord_3676733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3676733).length < 2 ^ (prefixWord ++ tailWord_3676733).sum := by decide
  have hdescent : baseEnd_3676733 < baseStart_3676733 := by decide
  rcases family_descends (prefixWord ++ tailWord_3676733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3676740 : List Nat := [2, 3, 5, 1, 1, 1, 1, 1, 3, 1, 4]
def baseStart_3676740 : Nat := 118140960795 + 3676740 * 2 ^ 59
def prefixEnd_3676740 : Nat := 4983230072969 + 3 ^ 40 * 3676740 * 2
def baseEnd_3676740 : Nat := 1887934861612049971540987

theorem tailTrace_3676740 : CollatzResearch.WordTrace tailWord_3676740 prefixEnd_3676740 1887934861612049971540987 := by
  unfold tailWord_3676740
  simp only [CollatzResearch.WordTrace]
  refine ⟨67050862349903196022237837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89401149799870928029650449 67050862349903196022237837)
  ·
    refine ⟨25144073381213698508339189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67050862349903196022237837 25144073381213698508339189)
    ·
      refine ⟨2357256879488784235156799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25144073381213698508339189 2357256879488784235156799)
      ·
        refine ⟨3535885319233176352735199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2357256879488784235156799 3535885319233176352735199)
        ·
          refine ⟨5303827978849764529102799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3535885319233176352735199 5303827978849764529102799)
          ·
            refine ⟨7955741968274646793654199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5303827978849764529102799 7955741968274646793654199)
            ·
              refine ⟨11933612952411970190481299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7955741968274646793654199 11933612952411970190481299)
              ·
                refine ⟨17900419428617955285721949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11933612952411970190481299 17900419428617955285721949)
                ·
                  refine ⟨6712657285731733232145731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17900419428617955285721949 6712657285731733232145731)
                  ·
                    refine ⟨10068985928597599848218597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6712657285731733232145731 10068985928597599848218597)
                    ·
                      refine ⟨1887934861612049971540987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10068985928597599848218597 1887934861612049971540987)
                      ·
                        rfl

theorem cell23_3676740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_3676740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3676740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3676740 prefixEnd_3676740 := by exact prefixLift 3676740
  have htrace : WordTrace (prefixWord ++ tailWord_3676740) baseStart_3676740 baseEnd_3676740 := by
    simpa [prefixWord, tailWord_3676740, baseEnd_3676740] using wordTrace_append hprefix tailTrace_3676740
  have hstable : (prefixWord ++ tailWord_3676740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3676740).length < 2 ^ (prefixWord ++ tailWord_3676740).sum := by decide
  have hdescent : baseEnd_3676740 < baseStart_3676740 := by decide
  rcases family_descends (prefixWord ++ tailWord_3676740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3676743 : List Nat := [1, 1, 4, 1, 4, 3, 1, 2, 1, 2, 3]
def baseStart_3676743 : Nat := 118140960795 + 3676743 * 2 ^ 59
def prefixEnd_3676743 : Nat := 4983230072969 + 3 ^ 40 * 3676743 * 2
def baseEnd_3676743 : Nat := 1887936402054013459803473

theorem tailTrace_3676743 : CollatzResearch.WordTrace tailWord_3676743 prefixEnd_3676743 1887936402054013459803473 := by
  unfold tailWord_3676743
  simp only [CollatzResearch.WordTrace]
  refine ⟨134101834118795523556834883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89401222745863682371223255 134101834118795523556834883)
  ·
    refine ⟨201152751178193285335252325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134101834118795523556834883 201152751178193285335252325)
    ·
      refine ⟨37716140845911241000359811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 201152751178193285335252325 37716140845911241000359811)
      ·
        refine ⟨56574211268866861500539717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37716140845911241000359811 56574211268866861500539717)
        ·
          refine ⟨10607664612912536531351197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56574211268866861500539717 10607664612912536531351197)
          ·
            refine ⟨3977874229842201199256699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10607664612912536531351197 3977874229842201199256699)
            ·
              refine ⟨5966811344763301798885049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3977874229842201199256699 5966811344763301798885049)
              ·
                refine ⟨4475108508572476349163787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5966811344763301798885049 4475108508572476349163787)
                ·
                  refine ⟨6712662762858714523745681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4475108508572476349163787 6712662762858714523745681)
                  ·
                    refine ⟨5034497072144035892809261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6712662762858714523745681 5034497072144035892809261)
                    ·
                      refine ⟨1887936402054013459803473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5034497072144035892809261 1887936402054013459803473)
                      ·
                        rfl

theorem cell23_3676743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 1, 2, 1, 2, 3].length) (baseStart_3676743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3676743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3676743 prefixEnd_3676743 := by exact prefixLift 3676743
  have htrace : WordTrace (prefixWord ++ tailWord_3676743) baseStart_3676743 baseEnd_3676743 := by
    simpa [prefixWord, tailWord_3676743, baseEnd_3676743] using wordTrace_append hprefix tailTrace_3676743
  have hstable : (prefixWord ++ tailWord_3676743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3676743).length < 2 ^ (prefixWord ++ tailWord_3676743).sum := by decide
  have hdescent : baseEnd_3676743 < baseStart_3676743 := by decide
  rcases family_descends (prefixWord ++ tailWord_3676743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3676752 : List Nat := [2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 5]
def baseStart_3676752 : Nat := 118140960795 + 3676752 * 2 ^ 59
def prefixEnd_3676752 : Nat := 4983230072969 + 3 ^ 40 * 3676752 * 2
def baseEnd_3676752 : Nat := 1887941023379903924590931

theorem tailTrace_3676752 : CollatzResearch.WordTrace tailWord_3676752 prefixEnd_3676752 1887941023379903924590931 := by
  unfold tailWord_3676752
  simp only [CollatzResearch.WordTrace]
  refine ⟨67051081187881459046956255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89401441583841945395941673 67051081187881459046956255)
  ·
    refine ⟨100576621781822188570434383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67051081187881459046956255 100576621781822188570434383)
    ·
      refine ⟨150864932672733282855651575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100576621781822188570434383 150864932672733282855651575)
      ·
        refine ⟨226297399009099924283477363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150864932672733282855651575 226297399009099924283477363)
        ·
          refine ⟨339446098513649886425216045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226297399009099924283477363 339446098513649886425216045)
          ·
            refine ⟨127292286942618707409456017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 339446098513649886425216045 127292286942618707409456017)
            ·
              refine ⟨95469215206964030557092013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127292286942618707409456017 95469215206964030557092013)
              ·
                refine ⟨35800955702611511458909505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95469215206964030557092013 35800955702611511458909505)
                ·
                  refine ⟨26850716776958633594182129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35800955702611511458909505 26850716776958633594182129)
                  ·
                    refine ⟨20138037582718975195636597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26850716776958633594182129 20138037582718975195636597)
                    ·
                      refine ⟨1887941023379903924590931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20138037582718975195636597 1887941023379903924590931)
                      ·
                        rfl

theorem cell23_3676752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 5].length) (baseStart_3676752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3676752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3676752 prefixEnd_3676752 := by exact prefixLift 3676752
  have htrace : WordTrace (prefixWord ++ tailWord_3676752) baseStart_3676752 baseEnd_3676752 := by
    simpa [prefixWord, tailWord_3676752, baseEnd_3676752] using wordTrace_append hprefix tailTrace_3676752
  have hstable : (prefixWord ++ tailWord_3676752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3676752).length < 2 ^ (prefixWord ++ tailWord_3676752).sum := by decide
  have hdescent : baseEnd_3676752 < baseStart_3676752 := by decide
  rcases family_descends (prefixWord ++ tailWord_3676752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3676756 : List Nat := [2, 4, 1, 1, 1, 4, 1, 2, 1, 3, 3]
def baseStart_3676756 : Nat := 118140960795 + 3676756 * 2 ^ 59
def prefixEnd_3676756 : Nat := 4983230072969 + 3 ^ 40 * 3676756 * 2
def baseEnd_3676756 : Nat := 1887943077302521908940913

theorem tailTrace_3676756 : CollatzResearch.WordTrace tailWord_3676756 prefixEnd_3676756 1887943077302521908940913 := by
  unfold tailWord_3676756
  simp only [CollatzResearch.WordTrace]
  refine ⟨67051154133874213388529061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89401538845165617851372081 67051154133874213388529061)
  ·
    refine ⟨12572091400101415010349199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67051154133874213388529061 12572091400101415010349199)
    ·
      refine ⟨18858137100152122515523799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12572091400101415010349199 18858137100152122515523799)
      ·
        refine ⟨28287205650228183773285699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18858137100152122515523799 28287205650228183773285699)
        ·
          refine ⟨42430808475342275659928549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28287205650228183773285699 42430808475342275659928549)
          ·
            refine ⟨7955776589126676686236603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42430808475342275659928549 7955776589126676686236603)
            ·
              refine ⟨11933664883690015029354905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7955776589126676686236603 11933664883690015029354905)
              ·
                refine ⟨8950248662767511272016179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11933664883690015029354905 8950248662767511272016179)
                ·
                  refine ⟨13425372994151266908024269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8950248662767511272016179 13425372994151266908024269)
                  ·
                    refine ⟨5034514872806725090509101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13425372994151266908024269 5034514872806725090509101)
                    ·
                      refine ⟨1887943077302521908940913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5034514872806725090509101 1887943077302521908940913)
                      ·
                        rfl

theorem cell23_3676756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 2, 1, 3, 3].length) (baseStart_3676756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3676756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3676756 prefixEnd_3676756 := by exact prefixLift 3676756
  have htrace : WordTrace (prefixWord ++ tailWord_3676756) baseStart_3676756 baseEnd_3676756 := by
    simpa [prefixWord, tailWord_3676756, baseEnd_3676756] using wordTrace_append hprefix tailTrace_3676756
  have hstable : (prefixWord ++ tailWord_3676756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3676756).length < 2 ^ (prefixWord ++ tailWord_3676756).sum := by decide
  have hdescent : baseEnd_3676756 < baseStart_3676756 := by decide
  rcases family_descends (prefixWord ++ tailWord_3676756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3676792 : List Nat := [2, 1, 2, 1, 1, 1, 2, 2, 2, 3, 6]
def baseStart_3676792 : Nat := 118140960795 + 3676792 * 2 ^ 59
def prefixEnd_3676792 : Nat := 4983230072969 + 3 ^ 40 * 3676792 * 2
def baseEnd_3676792 : Nat := 1887961562606083768090747

theorem tailTrace_3676792 : CollatzResearch.WordTrace tailWord_3676792 prefixEnd_3676792 1887961562606083768090747 := by
  unfold tailWord_3676792
  simp only [CollatzResearch.WordTrace]
  refine ⟨67051810647809002462684315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89402414197078669950245753 67051810647809002462684315)
  ·
    refine ⟨100577715971713503694026473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67051810647809002462684315 100577715971713503694026473)
    ·
      refine ⟨75433286978785127770519855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100577715971713503694026473 75433286978785127770519855)
      ·
        refine ⟨113149930468177691655779783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75433286978785127770519855 113149930468177691655779783)
        ·
          refine ⟨169724895702266537483669675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113149930468177691655779783 169724895702266537483669675)
          ·
            refine ⟨254587343553399806225504513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169724895702266537483669675 254587343553399806225504513)
            ·
              refine ⟨190940507665049854669128385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 254587343553399806225504513 190940507665049854669128385)
              ·
                refine ⟨143205380748787391001846289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 190940507665049854669128385 143205380748787391001846289)
                ·
                  refine ⟨107404035561590543251384717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 143205380748787391001846289 107404035561590543251384717)
                  ·
                    refine ⟨40276513335596453719269269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 107404035561590543251384717 40276513335596453719269269)
                    ·
                      refine ⟨1887961562606083768090747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40276513335596453719269269 1887961562606083768090747)
                      ·
                        rfl

theorem cell23_3676792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 2, 3, 6].length) (baseStart_3676792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3676792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3676792 prefixEnd_3676792 := by exact prefixLift 3676792
  have htrace : WordTrace (prefixWord ++ tailWord_3676792) baseStart_3676792 baseEnd_3676792 := by
    simpa [prefixWord, tailWord_3676792, baseEnd_3676792] using wordTrace_append hprefix tailTrace_3676792
  have hstable : (prefixWord ++ tailWord_3676792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3676792).length < 2 ^ (prefixWord ++ tailWord_3676792).sum := by decide
  have hdescent : baseEnd_3676792 < baseStart_3676792 := by decide
  rcases family_descends (prefixWord ++ tailWord_3676792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3676796 : List Nat := [2, 2, 2, 1, 1, 2, 3, 3, 1, 4, 2]
def baseStart_3676796 : Nat := 118140960795 + 3676796 * 2 ^ 59
def prefixEnd_3676796 : Nat := 4983230072969 + 3 ^ 40 * 3676796 * 2
def baseEnd_3676796 : Nat := 1887963616528701752440729

theorem tailTrace_3676796 : CollatzResearch.WordTrace tailWord_3676796 prefixEnd_3676796 1887963616528701752440729 := by
  unfold tailWord_3676796
  simp only [CollatzResearch.WordTrace]
  refine ⟨67051883593801756804257121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89402511458402342405676161 67051883593801756804257121)
  ·
    refine ⟨50288912695351317603192841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67051883593801756804257121 50288912695351317603192841)
    ·
      refine ⟨37716684521513488202394631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50288912695351317603192841 37716684521513488202394631)
      ·
        refine ⟨56575026782270232303591947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37716684521513488202394631 56575026782270232303591947)
        ·
          refine ⟨84862540173405348455387921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56575026782270232303591947 84862540173405348455387921)
          ·
            refine ⟨63646905130054011341540941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84862540173405348455387921 63646905130054011341540941)
            ·
              refine ⟨23867589423770254253077853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63646905130054011341540941 23867589423770254253077853)
              ·
                refine ⟨8950346033913845344904195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23867589423770254253077853 8950346033913845344904195)
                ·
                  refine ⟨13425519050870768017356293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8950346033913845344904195 13425519050870768017356293)
                  ·
                    refine ⟨2517284822038269003254305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13425519050870768017356293 2517284822038269003254305)
                    ·
                      refine ⟨1887963616528701752440729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2517284822038269003254305 1887963616528701752440729)
                      ·
                        rfl

theorem cell23_3676796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 3, 1, 4, 2].length) (baseStart_3676796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3676796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3676796 prefixEnd_3676796 := by exact prefixLift 3676796
  have htrace : WordTrace (prefixWord ++ tailWord_3676796) baseStart_3676796 baseEnd_3676796 := by
    simpa [prefixWord, tailWord_3676796, baseEnd_3676796] using wordTrace_append hprefix tailTrace_3676796
  have hstable : (prefixWord ++ tailWord_3676796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3676796).length < 2 ^ (prefixWord ++ tailWord_3676796).sum := by decide
  have hdescent : baseEnd_3676796 < baseStart_3676796 := by decide
  rcases family_descends (prefixWord ++ tailWord_3676796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3676830 : List Nat := [4, 3, 1, 1, 1, 1, 3, 1, 4, 2, 2]
def baseStart_3676830 : Nat := 118140960795 + 3676830 * 2 ^ 59
def prefixEnd_3676830 : Nat := 4983230072969 + 3 ^ 40 * 3676830 * 2
def baseEnd_3676830 : Nat := 1887981074870954619415573

theorem tailTrace_3676830 : CollatzResearch.WordTrace tailWord_3676830 prefixEnd_3676830 1887981074870954619415573 := by
  unfold tailWord_3676830
  simp only [CollatzResearch.WordTrace]
  refine ⟨16763125908685042176906493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89403338179653558276834629 16763125908685042176906493)
  ·
    refine ⟨6286172215756890816339935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16763125908685042176906493 6286172215756890816339935)
    ·
      refine ⟨9429258323635336224509903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6286172215756890816339935 9429258323635336224509903)
      ·
        refine ⟨14143887485453004336764855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9429258323635336224509903 14143887485453004336764855)
        ·
          refine ⟨21215831228179506505147283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14143887485453004336764855 21215831228179506505147283)
          ·
            refine ⟨31823746842269259757720925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21215831228179506505147283 31823746842269259757720925)
            ·
              refine ⟨11933905065850972409145347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31823746842269259757720925 11933905065850972409145347)
              ·
                refine ⟨17900857598776458613718021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11933905065850972409145347 17900857598776458613718021)
                ·
                  refine ⟨3356410799770585990072129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17900857598776458613718021 3356410799770585990072129)
                  ·
                    refine ⟨2517308099827939492554097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3356410799770585990072129 2517308099827939492554097)
                    ·
                      refine ⟨1887981074870954619415573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2517308099827939492554097 1887981074870954619415573)
                      ·
                        rfl

theorem cell23_3676830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 1, 4, 2, 2].length) (baseStart_3676830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3676830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3676830 prefixEnd_3676830 := by exact prefixLift 3676830
  have htrace : WordTrace (prefixWord ++ tailWord_3676830) baseStart_3676830 baseEnd_3676830 := by
    simpa [prefixWord, tailWord_3676830, baseEnd_3676830] using wordTrace_append hprefix tailTrace_3676830
  have hstable : (prefixWord ++ tailWord_3676830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3676830).length < 2 ^ (prefixWord ++ tailWord_3676830).sum := by decide
  have hdescent : baseEnd_3676830 < baseStart_3676830 := by decide
  rcases family_descends (prefixWord ++ tailWord_3676830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3676836 : List Nat := [2, 3, 1, 2, 2, 1, 1, 6, 5]
def baseStart_3676836 : Nat := 118140960795 + 3676836 * 2 ^ 59
def prefixEnd_3676836 : Nat := 4983230072969 + 3 ^ 40 * 3676836 * 2
def baseEnd_3676836 : Nat := 209776017306097955104505

theorem tailTrace_3676836 : CollatzResearch.WordTrace tailWord_3676836 prefixEnd_3676836 209776017306097955104505 := by
  unfold tailWord_3676836
  simp only [CollatzResearch.WordTrace]
  refine ⟨67052613053729300219985181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89403484071639066959980241 67052613053729300219985181)
  ·
    refine ⟨25144729895148487582494443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67052613053729300219985181 25144729895148487582494443)
    ·
      refine ⟨37717094842722731373741665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25144729895148487582494443 37717094842722731373741665)
      ·
        refine ⟨28287821132042048530306249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37717094842722731373741665 28287821132042048530306249)
        ·
          refine ⟨21215865849031536397729687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28287821132042048530306249 21215865849031536397729687)
          ·
            refine ⟨31823798773547304596594531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21215865849031536397729687 31823798773547304596594531)
            ·
              refine ⟨47735698160320956894891797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31823798773547304596594531 47735698160320956894891797)
              ·
                refine ⟨2237610851265044854448053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 47735698160320956894891797 2237610851265044854448053)
                ·
                  refine ⟨209776017306097955104505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2237610851265044854448053 209776017306097955104505)
                  ·
                    rfl

theorem cell23_3676836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 6, 5].length) (baseStart_3676836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3676836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3676836 prefixEnd_3676836 := by exact prefixLift 3676836
  have htrace : WordTrace (prefixWord ++ tailWord_3676836) baseStart_3676836 baseEnd_3676836 := by
    simpa [prefixWord, tailWord_3676836, baseEnd_3676836] using wordTrace_append hprefix tailTrace_3676836
  have hstable : (prefixWord ++ tailWord_3676836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3676836).length < 2 ^ (prefixWord ++ tailWord_3676836).sum := by decide
  have hdescent : baseEnd_3676836 < baseStart_3676836 := by decide
  rcases family_descends (prefixWord ++ tailWord_3676836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3676906 : List Nat := [3, 1, 3, 1, 1, 1, 1, 1, 6, 2, 3]
def baseStart_3676906 : Nat := 118140960795 + 3676906 * 2 ^ 59
def prefixEnd_3676906 : Nat := 4983230072969 + 3 ^ 40 * 3676906 * 2
def baseEnd_3676906 : Nat := 1888020099400696322065223

theorem tailTrace_3676906 : CollatzResearch.WordTrace tailWord_3676906 prefixEnd_3676906 1888020099400696322065223 := by
  unfold tailWord_3676906
  simp only [CollatzResearch.WordTrace]
  refine ⟨33526944804301250598754643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89405186144803334930012381 33526944804301250598754643)
  ·
    refine ⟨50290417206451875898131965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33526944804301250598754643 50290417206451875898131965)
    ·
      refine ⟨18858906452419453461799487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50290417206451875898131965 18858906452419453461799487)
      ·
        refine ⟨28288359678629180192699231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18858906452419453461799487 28288359678629180192699231)
        ·
          refine ⟨42432539517943770289048847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28288359678629180192699231 42432539517943770289048847)
          ·
            refine ⟨63648809276915655433573271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42432539517943770289048847 63648809276915655433573271)
            ·
              refine ⟨95473213915373483150359907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63648809276915655433573271 95473213915373483150359907)
              ·
                refine ⟨143209820873060224725539861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95473213915373483150359907 143209820873060224725539861)
                ·
                  refine ⟨6712960353424698034009681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 143209820873060224725539861 6712960353424698034009681)
                  ·
                    refine ⟨5034720265068523525507261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6712960353424698034009681 5034720265068523525507261)
                    ·
                      refine ⟨1888020099400696322065223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5034720265068523525507261 1888020099400696322065223)
                      ·
                        rfl

theorem cell23_3676906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 6, 2, 3].length) (baseStart_3676906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3676906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3676906 prefixEnd_3676906 := by exact prefixLift 3676906
  have htrace : WordTrace (prefixWord ++ tailWord_3676906) baseStart_3676906 baseEnd_3676906 := by
    simpa [prefixWord, tailWord_3676906, baseEnd_3676906] using wordTrace_append hprefix tailTrace_3676906
  have hstable : (prefixWord ++ tailWord_3676906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3676906).length < 2 ^ (prefixWord ++ tailWord_3676906).sum := by decide
  have hdescent : baseEnd_3676906 < baseStart_3676906 := by decide
  rcases family_descends (prefixWord ++ tailWord_3676906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3676917 : List Nat := [1, 3, 6, 1, 1, 1, 2, 1, 2, 5]
def baseStart_3676917 : Nat := 118140960795 + 3676917 * 2 ^ 59
def prefixEnd_3676917 : Nat := 4983230072969 + 3 ^ 40 * 3676917 * 2
def baseEnd_3676917 : Nat := 629341915895965259675891

theorem tailTrace_3676917 : CollatzResearch.WordTrace tailWord_3676917 prefixEnd_3676917 629341915895965259675891 := by
  unfold tailWord_3676917
  simp only [CollatzResearch.WordTrace]
  refine ⟨134108180420165151273669005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89405453613443434182446003 134108180420165151273669005)
  ·
    refine ⟨50290567657561931727625877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134108180420165151273669005 50290567657561931727625877)
    ·
      refine ⟨2357370358948215549732463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 50290567657561931727625877 2357370358948215549732463)
      ·
        refine ⟨3536055538422323324598695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2357370358948215549732463 3536055538422323324598695)
        ·
          refine ⟨5304083307633484986898043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3536055538422323324598695 5304083307633484986898043)
          ·
            refine ⟨7956124961450227480347065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5304083307633484986898043 7956124961450227480347065)
            ·
              refine ⟨5967093721087670610260299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7956124961450227480347065 5967093721087670610260299)
              ·
                refine ⟨8950640581631505915390449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5967093721087670610260299 8950640581631505915390449)
                ·
                  refine ⟨6712980436223629436542837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8950640581631505915390449 6712980436223629436542837)
                  ·
                    refine ⟨629341915895965259675891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6712980436223629436542837 629341915895965259675891)
                    ·
                      rfl

theorem cell23_3676917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_3676917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3676917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3676917 prefixEnd_3676917 := by exact prefixLift 3676917
  have htrace : WordTrace (prefixWord ++ tailWord_3676917) baseStart_3676917 baseEnd_3676917 := by
    simpa [prefixWord, tailWord_3676917, baseEnd_3676917] using wordTrace_append hprefix tailTrace_3676917
  have hstable : (prefixWord ++ tailWord_3676917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3676917).length < 2 ^ (prefixWord ++ tailWord_3676917).sum := by decide
  have hdescent : baseEnd_3676917 < baseStart_3676917 := by decide
  rcases family_descends (prefixWord ++ tailWord_3676917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3676929 : List Nat := [1, 2, 4, 1, 1, 1, 1, 2, 1, 1, 8]
def baseStart_3676929 : Nat := 118140960795 + 3676929 * 2 ^ 59
def prefixEnd_3676929 : Nat := 4983230072969 + 3 ^ 40 * 3676929 * 2
def baseEnd_3676929 : Nat := 1888031909455749732077617

theorem tailTrace_3676929 : CollatzResearch.WordTrace tailWord_3676929 prefixEnd_3676929 1888031909455749732077617 := by
  unfold tailWord_3676929
  simp only [CollatzResearch.WordTrace]
  refine ⟨134108618096121677323105841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89405745397414451548737227 134108618096121677323105841)
  ·
    refine ⟨100581463572091257992329381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134108618096121677323105841 100581463572091257992329381)
    ·
      refine ⟨18859024419767110873561759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100581463572091257992329381 18859024419767110873561759)
      ·
        refine ⟨28288536629650666310342639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18859024419767110873561759 28288536629650666310342639)
        ·
          refine ⟨42432804944475999465513959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28288536629650666310342639 42432804944475999465513959)
          ·
            refine ⟨63649207416713999198270939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42432804944475999465513959 63649207416713999198270939)
            ·
              refine ⟨95473811125070998797406409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63649207416713999198270939 95473811125070998797406409)
              ·
                refine ⟨71605358343803249098054807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95473811125070998797406409 71605358343803249098054807)
                ·
                  refine ⟨107408037515704873647082211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71605358343803249098054807 107408037515704873647082211)
                  ·
                    refine ⟨161112056273557310470623317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 107408037515704873647082211 161112056273557310470623317)
                    ·
                      refine ⟨1888031909455749732077617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 161112056273557310470623317 1888031909455749732077617)
                      ·
                        rfl

theorem cell23_3676929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 2, 1, 1, 8].length) (baseStart_3676929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3676929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3676929 prefixEnd_3676929 := by exact prefixLift 3676929
  have htrace : WordTrace (prefixWord ++ tailWord_3676929) baseStart_3676929 baseEnd_3676929 := by
    simpa [prefixWord, tailWord_3676929, baseEnd_3676929] using wordTrace_append hprefix tailTrace_3676929
  have hstable : (prefixWord ++ tailWord_3676929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3676929).length < 2 ^ (prefixWord ++ tailWord_3676929).sum := by decide
  have hdescent : baseEnd_3676929 < baseStart_3676929 := by decide
  rcases family_descends (prefixWord ++ tailWord_3676929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3676956 : List Nat := [2, 2, 3, 1, 1, 3, 1, 2, 3, 5]
def baseStart_3676956 : Nat := 118140960795 + 3676956 * 2 ^ 59
def prefixEnd_3676956 : Nat := 4983230072969 + 3 ^ 40 * 3676956 * 2
def baseEnd_3676956 : Nat := 629348591144473708813331

theorem tailTrace_3676956 : CollatzResearch.WordTrace tailWord_3676956 prefixEnd_3676956 629348591144473708813331 := by
  unfold tailWord_3676956
  simp only [CollatzResearch.WordTrace]
  refine ⟨67054801433511930467169361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89406401911349240622892481 67054801433511930467169361)
  ·
    refine ⟨50291101075133947850377021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67054801433511930467169361 50291101075133947850377021)
    ·
      refine ⟨18859162903175230443891383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50291101075133947850377021 18859162903175230443891383)
      ·
        refine ⟨28288744354762845665837075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18859162903175230443891383 28288744354762845665837075)
        ·
          refine ⟨42433116532144268498755613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28288744354762845665837075 42433116532144268498755613)
          ·
            refine ⟨15912418699554100687033355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42433116532144268498755613 15912418699554100687033355)
            ·
              refine ⟨23868628049331151030550033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15912418699554100687033355 23868628049331151030550033)
              ·
                refine ⟨17901471036998363272912525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23868628049331151030550033 17901471036998363272912525)
                ·
                  refine ⟨6713051638874386227342197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17901471036998363272912525 6713051638874386227342197)
                  ·
                    refine ⟨629348591144473708813331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6713051638874386227342197 629348591144473708813331)
                    ·
                      rfl

theorem cell23_3676956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 2, 3, 5].length) (baseStart_3676956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3676956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3676956 prefixEnd_3676956 := by exact prefixLift 3676956
  have htrace : WordTrace (prefixWord ++ tailWord_3676956) baseStart_3676956 baseEnd_3676956 := by
    simpa [prefixWord, tailWord_3676956, baseEnd_3676956] using wordTrace_append hprefix tailTrace_3676956
  have hstable : (prefixWord ++ tailWord_3676956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3676956).length < 2 ^ (prefixWord ++ tailWord_3676956).sum := by decide
  have hdescent : baseEnd_3676956 < baseStart_3676956 := by decide
  rcases family_descends (prefixWord ++ tailWord_3676956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3676969 : List Nat := [1, 2, 1, 1, 1, 1, 1, 4, 5, 6]
def baseStart_3676969 : Nat := 118140960795 + 3676969 * 2 ^ 59
def prefixEnd_3676969 : Nat := 4983230072969 + 3 ^ 40 * 3676969 * 2
def baseEnd_3676969 : Nat := 629350816227309858525811

theorem tailTrace_3676969 : CollatzResearch.WordTrace tailWord_3676969 prefixEnd_3676969 629350816227309858525811 := by
  unfold tailWord_3676969
  simp only [CollatzResearch.WordTrace]
  refine ⟨134110077015976764154561961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89406718010651176103041307 134110077015976764154561961)
  ·
    refine ⟨100582557761982573115921471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134110077015976764154561961 100582557761982573115921471)
    ·
      refine ⟨150873836642973859673882207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100582557761982573115921471 150873836642973859673882207)
      ·
        refine ⟨226310754964460789510823311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150873836642973859673882207 226310754964460789510823311)
        ·
          refine ⟨339466132446691184266234967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226310754964460789510823311 339466132446691184266234967)
          ·
            refine ⟨509199198670036776399352451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 339466132446691184266234967 509199198670036776399352451)
            ·
              refine ⟨763798798005055164599028677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 509199198670036776399352451 763798798005055164599028677)
              ·
                refine ⟨143212274625947843362317877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 763798798005055164599028677 143212274625947843362317877)
                ·
                  refine ⟨13426150746182610315217301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 143212274625947843362317877 13426150746182610315217301)
                  ·
                    refine ⟨629350816227309858525811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13426150746182610315217301 629350816227309858525811)
                    ·
                      rfl

theorem cell23_3676969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 5, 6].length) (baseStart_3676969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3676969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3676969 prefixEnd_3676969 := by exact prefixLift 3676969
  have htrace : WordTrace (prefixWord ++ tailWord_3676969) baseStart_3676969 baseEnd_3676969 := by
    simpa [prefixWord, tailWord_3676969, baseEnd_3676969] using wordTrace_append hprefix tailTrace_3676969
  have hstable : (prefixWord ++ tailWord_3676969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3676969).length < 2 ^ (prefixWord ++ tailWord_3676969).sum := by decide
  have hdescent : baseEnd_3676969 < baseStart_3676969 := by decide
  rcases family_descends (prefixWord ++ tailWord_3676969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3676990 : List Nat := [4, 2, 1, 2, 3, 1, 1, 3, 1, 5]
def baseStart_3676990 : Nat := 118140960795 + 3676990 * 2 ^ 59
def prefixEnd_3676990 : Nat := 4983230072969 + 3 ^ 40 * 3676990 * 2
def baseEnd_3676990 : Nat := 629354410591891331138279

theorem tailTrace_3676990 : CollatzResearch.WordTrace tailWord_3676990 prefixEnd_3676990 629354410591891331138279 := by
  unfold tailWord_3676990
  simp only [CollatzResearch.WordTrace]
  refine ⟨16763855368612585592634553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89407228632600456494050949 16763855368612585592634553)
  ·
    refine ⟨12572891526459439194475915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16763855368612585592634553 12572891526459439194475915)
    ·
      refine ⟨18859337289689158791713873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12572891526459439194475915 18859337289689158791713873)
      ·
        refine ⟨14144502967266869093785405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18859337289689158791713873 14144502967266869093785405)
        ·
          refine ⟨5304188612725075910169527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14144502967266869093785405 5304188612725075910169527)
          ·
            refine ⟨7956282919087613865254291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5304188612725075910169527 7956282919087613865254291)
            ·
              refine ⟨11934424378631420797881437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7956282919087613865254291 11934424378631420797881437)
              ·
                refine ⟨4475409141986782799205539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11934424378631420797881437 4475409141986782799205539)
                ·
                  refine ⟨6713113712980174198808309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4475409141986782799205539 6713113712980174198808309)
                  ·
                    refine ⟨629354410591891331138279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6713113712980174198808309 629354410591891331138279)
                    ·
                      rfl

theorem cell23_3676990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 3, 1, 5].length) (baseStart_3676990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3676990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3676990 prefixEnd_3676990 := by exact prefixLift 3676990
  have htrace : WordTrace (prefixWord ++ tailWord_3676990) baseStart_3676990 baseEnd_3676990 := by
    simpa [prefixWord, tailWord_3676990, baseEnd_3676990] using wordTrace_append hprefix tailTrace_3676990
  have hstable : (prefixWord ++ tailWord_3676990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3676990).length < 2 ^ (prefixWord ++ tailWord_3676990).sum := by decide
  have hdescent : baseEnd_3676990 < baseStart_3676990 := by decide
  rcases family_descends (prefixWord ++ tailWord_3676990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3677006 : List Nat := [4, 1, 1, 1, 1, 1, 1, 4, 3, 2, 4]
def baseStart_3677006 : Nat := 118140960795 + 3677006 * 2 ^ 59
def prefixEnd_3677006 : Nat := 4983230072969 + 3 ^ 40 * 3677006 * 2
def baseEnd_3677006 : Nat := 1888071447466145930814763

theorem tailTrace_3677006 : CollatzResearch.WordTrace tailWord_3677006 prefixEnd_3677006 1888071447466145930814763 := by
  unfold tailWord_3677006
  simp only [CollatzResearch.WordTrace]
  refine ⟨16763928314605339934207359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89407617677895146315772581 16763928314605339934207359)
  ·
    refine ⟨25145892471908009901311039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16763928314605339934207359 25145892471908009901311039)
    ·
      refine ⟨37718838707862014851966559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25145892471908009901311039 37718838707862014851966559)
      ·
        refine ⟨56578258061793022277949839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37718838707862014851966559 56578258061793022277949839)
        ·
          refine ⟨84867387092689533416924759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56578258061793022277949839 84867387092689533416924759)
          ·
            refine ⟨127301080639034300125387139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84867387092689533416924759 127301080639034300125387139)
            ·
              refine ⟨190951620958551450188080709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127301080639034300125387139 190951620958551450188080709)
              ·
                refine ⟨35803428929728396910265133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 190951620958551450188080709 35803428929728396910265133)
                ·
                  refine ⟨13426285848648148841349425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35803428929728396910265133 13426285848648148841349425)
                  ·
                    refine ⟨10069714386486111631012069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13426285848648148841349425 10069714386486111631012069)
                    ·
                      refine ⟨1888071447466145930814763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10069714386486111631012069 1888071447466145930814763)
                      ·
                        rfl

theorem cell23_3677006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 4, 3, 2, 4].length) (baseStart_3677006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3677006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3677006 prefixEnd_3677006 := by exact prefixLift 3677006
  have htrace : WordTrace (prefixWord ++ tailWord_3677006) baseStart_3677006 baseEnd_3677006 := by
    simpa [prefixWord, tailWord_3677006, baseEnd_3677006] using wordTrace_append hprefix tailTrace_3677006
  have hstable : (prefixWord ++ tailWord_3677006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3677006).length < 2 ^ (prefixWord ++ tailWord_3677006).sum := by decide
  have hdescent : baseEnd_3677006 < baseStart_3677006 := by decide
  rcases family_descends (prefixWord ++ tailWord_3677006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3677019 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 8]
def baseStart_3677019 : Nat := 118140960795 + 3677019 * 2 ^ 59
def prefixEnd_3677019 : Nat := 4983230072969 + 3 ^ 40 * 3677019 * 2
def baseEnd_3677019 : Nat := 1888078122714654379952203

theorem tailTrace_3677019 : CollatzResearch.WordTrace tailWord_3677019 prefixEnd_3677019 1888078122714654379952203 := by
  unfold tailWord_3677019
  simp only [CollatzResearch.WordTrace]
  refine ⟨134111900665795622693882111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89407933777197081795921407 134111900665795622693882111)
  ·
    refine ⟨201167850998693434040823167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134111900665795622693882111 201167850998693434040823167)
    ·
      refine ⟨301751776498040151061234751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201167850998693434040823167 301751776498040151061234751)
      ·
        refine ⟨452627664747060226591852127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301751776498040151061234751 452627664747060226591852127)
        ·
          refine ⟨678941497120590339887778191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 452627664747060226591852127 678941497120590339887778191)
          ·
            refine ⟨1018412245680885509831667287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 678941497120590339887778191 1018412245680885509831667287)
            ·
              refine ⟨1527618368521328264747500931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1018412245680885509831667287 1527618368521328264747500931)
              ·
                refine ⟨2291427552781992397121251397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1527618368521328264747500931 2291427552781992397121251397)
                ·
                  refine ⟨429642666146623574460234637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2291427552781992397121251397 429642666146623574460234637)
                  ·
                    refine ⟨161115999804983840422587989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 429642666146623574460234637 161115999804983840422587989)
                    ·
                      refine ⟨1888078122714654379952203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 161115999804983840422587989 1888078122714654379952203)
                      ·
                        rfl

theorem cell23_3677019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 8].length) (baseStart_3677019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3677019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3677019 prefixEnd_3677019 := by exact prefixLift 3677019
  have htrace : WordTrace (prefixWord ++ tailWord_3677019) baseStart_3677019 baseEnd_3677019 := by
    simpa [prefixWord, tailWord_3677019, baseEnd_3677019] using wordTrace_append hprefix tailTrace_3677019
  have hstable : (prefixWord ++ tailWord_3677019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3677019).length < 2 ^ (prefixWord ++ tailWord_3677019).sum := by decide
  have hdescent : baseEnd_3677019 < baseStart_3677019 := by decide
  rcases family_descends (prefixWord ++ tailWord_3677019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3677020 : List Nat := [2, 2, 4, 2, 1, 3, 1, 1, 1, 6]
def baseStart_3677020 : Nat := 118140960795 + 3677020 * 2 ^ 59
def prefixEnd_3677020 : Nat := 4983230072969 + 3 ^ 40 * 3677020 * 2
def baseEnd_3677020 : Nat := 629359545398436292013233

theorem tailTrace_3677020 : CollatzResearch.WordTrace tailWord_3677020 prefixEnd_3677020 629359545398436292013233 := by
  unfold tailWord_3677020
  simp only [CollatzResearch.WordTrace]
  refine ⟨67055968569395999932334257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89407958092527999909779009 67055968569395999932334257)
  ·
    refine ⟨50291976427046999949250693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67055968569395999932334257 50291976427046999949250693)
    ·
      refine ⟨9429745580071312490484505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50291976427046999949250693 9429745580071312490484505)
      ·
        refine ⟨7072309185053484367863379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9429745580071312490484505 7072309185053484367863379)
        ·
          refine ⟨10608463777580226551795069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7072309185053484367863379 10608463777580226551795069)
          ·
            refine ⟨3978173916592584956923151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10608463777580226551795069 3978173916592584956923151)
            ·
              refine ⟨5967260874888877435384727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3978173916592584956923151 5967260874888877435384727)
              ·
                refine ⟨8950891312333316153077091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5967260874888877435384727 8950891312333316153077091)
                ·
                  refine ⟨13426336968499974229615637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8950891312333316153077091 13426336968499974229615637)
                  ·
                    refine ⟨629359545398436292013233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13426336968499974229615637 629359545398436292013233)
                    ·
                      rfl

theorem cell23_3677020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 1, 1, 1, 6].length) (baseStart_3677020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3677020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3677020 prefixEnd_3677020 := by exact prefixLift 3677020
  have htrace : WordTrace (prefixWord ++ tailWord_3677020) baseStart_3677020 baseEnd_3677020 := by
    simpa [prefixWord, tailWord_3677020, baseEnd_3677020] using wordTrace_append hprefix tailTrace_3677020
  have hstable : (prefixWord ++ tailWord_3677020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3677020).length < 2 ^ (prefixWord ++ tailWord_3677020).sum := by decide
  have hdescent : baseEnd_3677020 < baseStart_3677020 := by decide
  rcases family_descends (prefixWord ++ tailWord_3677020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3677043 : List Nat := [1, 1, 1, 2, 2, 1, 5, 2, 4, 1, 3]
def baseStart_3677043 : Nat := 118140960795 + 3677043 * 2 ^ 59
def prefixEnd_3677043 : Nat := 4983230072969 + 3 ^ 40 * 3677043 * 2
def baseEnd_3677043 : Nat := 1888090446250362286052093

theorem tailTrace_3677043 : CollatzResearch.WordTrace tailWord_3677043 prefixEnd_3677043 1888090446250362286052093 := by
  unfold tailWord_3677043
  simp only [CollatzResearch.WordTrace]
  refine ⟨134112776017708674792755783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89408517345139116528503855 134112776017708674792755783)
  ·
    refine ⟨201169164026563012189133675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134112776017708674792755783 201169164026563012189133675)
    ·
      refine ⟨301753746039844518283700513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201169164026563012189133675 301753746039844518283700513)
      ·
        refine ⟨226315309529883388712775385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 301753746039844518283700513 226315309529883388712775385)
        ·
          refine ⟨169736482147412541534581539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226315309529883388712775385 169736482147412541534581539)
          ·
            refine ⟨254604723221118812301872309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169736482147412541534581539 254604723221118812301872309)
            ·
              refine ⟨23869192801979888653300529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 254604723221118812301872309 23869192801979888653300529)
              ·
                refine ⟨17901894601484916489975397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23869192801979888653300529 17901894601484916489975397)
                ·
                  refine ⟨3356605237778421841870387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17901894601484916489975397 3356605237778421841870387)
                  ·
                    refine ⟨5034907856667632762805581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3356605237778421841870387 5034907856667632762805581)
                    ·
                      refine ⟨1888090446250362286052093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5034907856667632762805581 1888090446250362286052093)
                      ·
                        rfl

theorem cell23_3677043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 2, 4, 1, 3].length) (baseStart_3677043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3677043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3677043 prefixEnd_3677043 := by exact prefixLift 3677043
  have htrace : WordTrace (prefixWord ++ tailWord_3677043) baseStart_3677043 baseEnd_3677043 := by
    simpa [prefixWord, tailWord_3677043, baseEnd_3677043] using wordTrace_append hprefix tailTrace_3677043
  have hstable : (prefixWord ++ tailWord_3677043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3677043).length < 2 ^ (prefixWord ++ tailWord_3677043).sum := by decide
  have hdescent : baseEnd_3677043 < baseStart_3677043 := by decide
  rcases family_descends (prefixWord ++ tailWord_3677043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3677060 : List Nat := [2, 3, 2, 1, 1, 1, 1, 6, 2, 1, 3]
def baseStart_3677060 : Nat := 118140960795 + 3677060 * 2 ^ 59
def prefixEnd_3677060 : Nat := 4983230072969 + 3 ^ 40 * 3677060 * 2
def baseEnd_3677060 : Nat := 1888099175421488719539515

theorem tailTrace_3677060 : CollatzResearch.WordTrace tailWord_3677060 prefixEnd_3677060 1888099175421488719539515 := by
  unfold tailWord_3677060
  simp only [CollatzResearch.WordTrace]
  refine ⟨67056698029323543348062317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89408930705764724464083089 67056698029323543348062317)
  ·
    refine ⟨25146261760996328755523369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67056698029323543348062317 25146261760996328755523369)
    ·
      refine ⟨18859696320747246566642527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25146261760996328755523369 18859696320747246566642527)
      ·
        refine ⟨28289544481120869849963791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18859696320747246566642527 28289544481120869849963791)
        ·
          refine ⟨42434316721681304774945687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28289544481120869849963791 42434316721681304774945687)
          ·
            refine ⟨63651475082521957162418531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42434316721681304774945687 63651475082521957162418531)
            ·
              refine ⟨95477212623782935743627797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63651475082521957162418531 95477212623782935743627797)
              ·
                refine ⟨4475494341739825112982553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 95477212623782935743627797 4475494341739825112982553)
                ·
                  refine ⟨3356620756304868834736915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4475494341739825112982553 3356620756304868834736915)
                  ·
                    refine ⟨5034931134457303252105373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3356620756304868834736915 5034931134457303252105373)
                    ·
                      refine ⟨1888099175421488719539515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5034931134457303252105373 1888099175421488719539515)
                      ·
                        rfl

theorem cell23_3677060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 6, 2, 1, 3].length) (baseStart_3677060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3677060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3677060 prefixEnd_3677060 := by exact prefixLift 3677060
  have htrace : WordTrace (prefixWord ++ tailWord_3677060) baseStart_3677060 baseEnd_3677060 := by
    simpa [prefixWord, tailWord_3677060, baseEnd_3677060] using wordTrace_append hprefix tailTrace_3677060
  have hstable : (prefixWord ++ tailWord_3677060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3677060).length < 2 ^ (prefixWord ++ tailWord_3677060).sum := by decide
  have hdescent : baseEnd_3677060 < baseStart_3677060 := by decide
  rcases family_descends (prefixWord ++ tailWord_3677060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3677077 : List Nat := [1, 3, 2, 1, 1, 4, 4, 1, 2, 1, 3]
def baseStart_3677077 : Nat := 118140960795 + 3677077 * 2 ^ 59
def prefixEnd_3677077 : Nat := 4983230072969 + 3 ^ 40 * 3677077 * 2
def baseEnd_3677077 : Nat := 1888107904592615153026937

theorem tailTrace_3677077 : CollatzResearch.WordTrace tailWord_3677077 prefixEnd_3677077 1888107904592615153026937 := by
  unfold tailWord_3677077
  simp only [CollatzResearch.WordTrace]
  refine ⟨134114016099585498599493485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89409344066390332399662323 134114016099585498599493485)
  ·
    refine ⟨50292756037344561974810057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134114016099585498599493485 50292756037344561974810057)
    ·
      refine ⟨37719567028008421481107543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50292756037344561974810057 37719567028008421481107543)
      ·
        refine ⟨56579350542012632221661315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37719567028008421481107543 56579350542012632221661315)
        ·
          refine ⟨84869025813018948332491973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56579350542012632221661315 84869025813018948332491973)
          ·
            refine ⟨15912942339941052812342245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84869025813018948332491973 15912942339941052812342245)
            ·
              refine ⟨2983676688738947402314171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15912942339941052812342245 2983676688738947402314171)
              ·
                refine ⟨4475515033108421103471257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2983676688738947402314171 4475515033108421103471257)
                ·
                  refine ⟨3356636274831315827603443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4475515033108421103471257 3356636274831315827603443)
                  ·
                    refine ⟨5034954412246973741405165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3356636274831315827603443 5034954412246973741405165)
                    ·
                      refine ⟨1888107904592615153026937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5034954412246973741405165 1888107904592615153026937)
                      ·
                        rfl

theorem cell23_3677077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 4, 1, 2, 1, 3].length) (baseStart_3677077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3677077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3677077 prefixEnd_3677077 := by exact prefixLift 3677077
  have htrace : WordTrace (prefixWord ++ tailWord_3677077) baseStart_3677077 baseEnd_3677077 := by
    simpa [prefixWord, tailWord_3677077, baseEnd_3677077] using wordTrace_append hprefix tailTrace_3677077
  have hstable : (prefixWord ++ tailWord_3677077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3677077).length < 2 ^ (prefixWord ++ tailWord_3677077).sum := by decide
  have hdescent : baseEnd_3677077 < baseStart_3677077 := by decide
  rcases family_descends (prefixWord ++ tailWord_3677077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3677087 : List Nat := [1, 1, 2, 5, 2, 1, 3, 2, 1, 3, 2]
def baseStart_3677087 : Nat := 118140960795 + 3677087 * 2 ^ 59
def prefixEnd_3677087 : Nat := 4983230072969 + 3 ^ 40 * 3677087 * 2
def baseEnd_3677087 : Nat := 1888113039399160113901891

theorem tailTrace_3677087 : CollatzResearch.WordTrace tailWord_3677087 prefixEnd_3677087 1888113039399160113901891 := by
  unfold tailWord_3677087
  simp only [CollatzResearch.WordTrace]
  refine ⟨134114380829549270307357515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89409587219699513538238343 134114380829549270307357515)
  ·
    refine ⟨201171571244323905461036273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134114380829549270307357515 201171571244323905461036273)
    ·
      refine ⟨150878678433242929095777205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201171571244323905461036273 150878678433242929095777205)
      ·
        refine ⟨14144876103116524602729113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 150878678433242929095777205 14144876103116524602729113)
        ·
          refine ⟨10608657077337393452046835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14144876103116524602729113 10608657077337393452046835)
          ·
            refine ⟨15912985616006090178070253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10608657077337393452046835 15912985616006090178070253)
            ·
              refine ⟨5967369606002283816776345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15912985616006090178070253 5967369606002283816776345)
              ·
                refine ⟨4475527204501712862582259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5967369606002283816776345 4475527204501712862582259)
                ·
                  refine ⟨6713290806752569293873389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4475527204501712862582259 6713290806752569293873389)
                  ·
                    refine ⟨2517484052532213485202521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6713290806752569293873389 2517484052532213485202521)
                    ·
                      refine ⟨1888113039399160113901891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2517484052532213485202521 1888113039399160113901891)
                      ·
                        rfl

theorem cell23_3677087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 3, 2, 1, 3, 2].length) (baseStart_3677087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3677087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3677087 prefixEnd_3677087 := by exact prefixLift 3677087
  have htrace : WordTrace (prefixWord ++ tailWord_3677087) baseStart_3677087 baseEnd_3677087 := by
    simpa [prefixWord, tailWord_3677087, baseEnd_3677087] using wordTrace_append hprefix tailTrace_3677087
  have hstable : (prefixWord ++ tailWord_3677087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3677087).length < 2 ^ (prefixWord ++ tailWord_3677087).sum := by decide
  have hdescent : baseEnd_3677087 < baseStart_3677087 := by decide
  rcases family_descends (prefixWord ++ tailWord_3677087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3677123 : List Nat := [1, 1, 1, 3, 1, 1, 2, 8, 5]
def baseStart_3677123 : Nat := 118140960795 + 3677123 * 2 ^ 59
def prefixEnd_3677123 : Nat := 4983230072969 + 3 ^ 40 * 3677123 * 2
def baseEnd_3677123 : Nat := 209792391633635774783525

theorem tailTrace_3677123 : CollatzResearch.WordTrace tailWord_3677123 prefixEnd_3677123 209792391633635774783525 := by
  unfold tailWord_3677123
  simp only [CollatzResearch.WordTrace]
  refine ⟨134115693857418848455668023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89410462571612565637112015 134115693857418848455668023)
  ·
    refine ⟨201173540786128272683502035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134115693857418848455668023 201173540786128272683502035)
    ·
      refine ⟨301760311179192409025253053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201173540786128272683502035 301760311179192409025253053)
      ·
        refine ⟨113160116692197153384469895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 301760311179192409025253053 113160116692197153384469895)
        ·
          refine ⟨169740175038295730076704843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113160116692197153384469895 169740175038295730076704843)
          ·
            refine ⟨254610262557443595115057265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169740175038295730076704843 254610262557443595115057265)
            ·
              refine ⟨190957696918082696336292949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 254610262557443595115057265 190957696918082696336292949)
              ·
                refine ⟨2237785510758781597690933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 190957696918082696336292949 2237785510758781597690933)
                ·
                  refine ⟨209792391633635774783525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2237785510758781597690933 209792391633635774783525)
                  ·
                    rfl

theorem cell23_3677123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 8, 5].length) (baseStart_3677123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3677123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3677123 prefixEnd_3677123 := by exact prefixLift 3677123
  have htrace : WordTrace (prefixWord ++ tailWord_3677123) baseStart_3677123 baseEnd_3677123 := by
    simpa [prefixWord, tailWord_3677123, baseEnd_3677123] using wordTrace_append hprefix tailTrace_3677123
  have hstable : (prefixWord ++ tailWord_3677123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3677123).length < 2 ^ (prefixWord ++ tailWord_3677123).sum := by decide
  have hdescent : baseEnd_3677123 < baseStart_3677123 := by decide
  rcases family_descends (prefixWord ++ tailWord_3677123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3677136 : List Nat := [2, 1, 1, 1, 1, 2, 3, 4, 1, 7]
def baseStart_3677136 : Nat := 118140960795 + 3677136 * 2 ^ 59
def prefixEnd_3677136 : Nat := 4983230072969 + 3 ^ 40 * 3677136 * 2
def baseEnd_3677136 : Nat := 629379399983743474063055

theorem tailTrace_3677136 : CollatzResearch.WordTrace tailWord_3677136 prefixEnd_3677136 629379399983743474063055 := by
  unfold tailWord_3677136
  simp only [CollatzResearch.WordTrace]
  refine ⟨67058084003185875837945631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89410778670914501117260841 67058084003185875837945631)
  ·
    refine ⟨100587126004778813756918447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67058084003185875837945631 100587126004778813756918447)
    ·
      refine ⟨150880689007168220635377671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100587126004778813756918447 150880689007168220635377671)
      ·
        refine ⟨226321033510752330953066507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150880689007168220635377671 226321033510752330953066507)
        ·
          refine ⟨339481550266128496429599761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226321033510752330953066507 339481550266128496429599761)
          ·
            refine ⟨254611162699596372322199821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 339481550266128496429599761 254611162699596372322199821)
            ·
              refine ⟨95479186012348639620824933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 254611162699596372322199821 95479186012348639620824933)
              ·
                refine ⟨17902347377315369928904675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 95479186012348639620824933 17902347377315369928904675)
                ·
                  refine ⟨26853521065973054893357013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17902347377315369928904675 26853521065973054893357013)
                  ·
                    refine ⟨629379399983743474063055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26853521065973054893357013 629379399983743474063055)
                    ·
                      rfl

theorem cell23_3677136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 4, 1, 7].length) (baseStart_3677136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3677136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3677136 prefixEnd_3677136 := by exact prefixLift 3677136
  have htrace : WordTrace (prefixWord ++ tailWord_3677136) baseStart_3677136 baseEnd_3677136 := by
    simpa [prefixWord, tailWord_3677136, baseEnd_3677136] using wordTrace_append hprefix tailTrace_3677136
  have hstable : (prefixWord ++ tailWord_3677136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3677136).length < 2 ^ (prefixWord ++ tailWord_3677136).sum := by decide
  have hdescent : baseEnd_3677136 < baseStart_3677136 := by decide
  rcases family_descends (prefixWord ++ tailWord_3677136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3677210 : List Nat := [3, 1, 1, 3, 1, 2, 2, 3, 2, 2, 3]
def baseStart_3677210 : Nat := 118140960795 + 3677210 * 2 ^ 59
def prefixEnd_3677210 : Nat := 4983230072969 + 3 ^ 40 * 3677210 * 2
def baseEnd_3677210 : Nat := 1888176197519663132663825

theorem tailTrace_3677210 : CollatzResearch.WordTrace tailWord_3677210 prefixEnd_3677210 1888176197519663132663825 := by
  unfold tailWord_3677210
  simp only [CollatzResearch.WordTrace]
  refine ⟨33529716752025915578521271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89412578005402441542723389 33529716752025915578521271)
  ·
    refine ⟨50294575128038873367781907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33529716752025915578521271 50294575128038873367781907)
    ·
      refine ⟨75441862692058310051672861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50294575128038873367781907 75441862692058310051672861)
      ·
        refine ⟨28290698509521866269377323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75441862692058310051672861 28290698509521866269377323)
        ·
          refine ⟨42436047764282799404065985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28290698509521866269377323 42436047764282799404065985)
          ·
            refine ⟨31827035823212099553049489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42436047764282799404065985 31827035823212099553049489)
            ·
              refine ⟨23870276867409074664787117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31827035823212099553049489 23870276867409074664787117)
              ·
                refine ⟨8951353825278402999295169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23870276867409074664787117 8951353825278402999295169)
                ·
                  refine ⟨6713515368958802249471377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8951353825278402999295169 6713515368958802249471377)
                  ·
                    refine ⟨5035136526719101687103533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6713515368958802249471377 5035136526719101687103533)
                    ·
                      refine ⟨1888176197519663132663825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5035136526719101687103533 1888176197519663132663825)
                      ·
                        rfl

theorem cell23_3677210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 3, 2, 2, 3].length) (baseStart_3677210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3677210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3677210 prefixEnd_3677210 := by exact prefixLift 3677210
  have htrace : WordTrace (prefixWord ++ tailWord_3677210) baseStart_3677210 baseEnd_3677210 := by
    simpa [prefixWord, tailWord_3677210, baseEnd_3677210] using wordTrace_append hprefix tailTrace_3677210
  have hstable : (prefixWord ++ tailWord_3677210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3677210).length < 2 ^ (prefixWord ++ tailWord_3677210).sum := by decide
  have hdescent : baseEnd_3677210 < baseStart_3677210 := by decide
  rcases family_descends (prefixWord ++ tailWord_3677210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3677230 : List Nat := [4, 1, 3, 1, 1, 1, 2, 4, 6]
def baseStart_3677230 : Nat := 118140960795 + 3677230 * 2 ^ 59
def prefixEnd_3677230 : Nat := 4983230072969 + 3 ^ 40 * 3677230 * 2
def baseEnd_3677230 : Nat := 209798496348083672712637

theorem tailTrace_3677230 : CollatzResearch.WordTrace tailWord_3677230 prefixEnd_3677230 209798496348083672712637 := by
  unfold tailWord_3677230
  simp only [CollatzResearch.WordTrace]
  refine ⟨16764949558503900716226643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89413064312020803819875429 16764949558503900716226643)
  ·
    refine ⟨25147424337755851074339965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16764949558503900716226643 25147424337755851074339965)
    ·
      refine ⟨9430284126658444152877487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25147424337755851074339965 9430284126658444152877487)
      ·
        refine ⟨14145426189987666229316231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9430284126658444152877487 14145426189987666229316231)
        ·
          refine ⟨21218139284981499343974347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14145426189987666229316231 21218139284981499343974347)
          ·
            refine ⟨31827208927472249015961521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21218139284981499343974347 31827208927472249015961521)
            ·
              refine ⟨23870406695604186761971141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31827208927472249015961521 23870406695604186761971141)
              ·
                refine ⟨4475701255425785017869589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23870406695604186761971141 4475701255425785017869589)
                ·
                  refine ⟨209798496348083672712637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4475701255425785017869589 209798496348083672712637)
                  ·
                    rfl

theorem cell23_3677230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 4, 6].length) (baseStart_3677230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3677230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3677230 prefixEnd_3677230 := by exact prefixLift 3677230
  have htrace : WordTrace (prefixWord ++ tailWord_3677230) baseStart_3677230 baseEnd_3677230 := by
    simpa [prefixWord, tailWord_3677230, baseEnd_3677230] using wordTrace_append hprefix tailTrace_3677230
  have hstable : (prefixWord ++ tailWord_3677230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3677230).length < 2 ^ (prefixWord ++ tailWord_3677230).sum := by decide
  have hdescent : baseEnd_3677230 < baseStart_3677230 := by decide
  rcases family_descends (prefixWord ++ tailWord_3677230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3677234 : List Nat := [3, 2, 1, 1, 2, 2, 5, 2, 1, 4]
def baseStart_3677234 : Nat := 118140960795 + 3677234 * 2 ^ 59
def prefixEnd_3677234 : Nat := 4983230072969 + 3 ^ 40 * 3677234 * 2
def baseEnd_3677234 : Nat := 629396173685123679587905

theorem tailTrace_3677234 : CollatzResearch.WordTrace tailWord_3677234 prefixEnd_3677234 629396173685123679587905 := by
  unfold tailWord_3677234
  simp only [CollatzResearch.WordTrace]
  refine ⟨33529935590004178603239689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89413161573344476275305837 33529935590004178603239689)
  ·
    refine ⟨25147451692503133952429767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33529935590004178603239689 25147451692503133952429767)
    ·
      refine ⟨37721177538754700928644651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25147451692503133952429767 37721177538754700928644651)
      ·
        refine ⟨56581766308132051392966977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37721177538754700928644651 56581766308132051392966977)
        ·
          refine ⟨42436324731099038544725233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56581766308132051392966977 42436324731099038544725233)
          ·
            refine ⟨31827243548324278908543925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42436324731099038544725233 31827243548324278908543925)
            ·
              refine ⟨2983804082655401147675993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31827243548324278908543925 2983804082655401147675993)
              ·
                refine ⟨2237853061991550860756995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2983804082655401147675993 2237853061991550860756995)
                ·
                  refine ⟨3356779592987326291135493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2237853061991550860756995 3356779592987326291135493)
                  ·
                    refine ⟨629396173685123679587905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3356779592987326291135493 629396173685123679587905)
                    ·
                      rfl

theorem cell23_3677234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 5, 2, 1, 4].length) (baseStart_3677234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3677234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3677234 prefixEnd_3677234 := by exact prefixLift 3677234
  have htrace : WordTrace (prefixWord ++ tailWord_3677234) baseStart_3677234 baseEnd_3677234 := by
    simpa [prefixWord, tailWord_3677234, baseEnd_3677234] using wordTrace_append hprefix tailTrace_3677234
  have hstable : (prefixWord ++ tailWord_3677234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3677234).length < 2 ^ (prefixWord ++ tailWord_3677234).sum := by decide
  have hdescent : baseEnd_3677234 < baseStart_3677234 := by decide
  rcases family_descends (prefixWord ++ tailWord_3677234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3677333 : List Nat := [1, 3, 2, 1, 1, 1, 2, 2, 1, 9]
def baseStart_3677333 : Nat := 118140960795 + 3677333 * 2 ^ 59
def prefixEnd_3677333 : Nat := 4983230072969 + 3 ^ 40 * 3677333 * 2
def baseEnd_3677333 : Nat := 629413118546722050475253

theorem tailTrace_3677333 : CollatzResearch.WordTrace tailWord_3677333 prefixEnd_3677333 629413118546722050475253 := by
  unfold tailWord_3677333
  simp only [CollatzResearch.WordTrace]
  refine ⟨134123353186658054320812653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89415568791105369547208435 134123353186658054320812653)
  ·
    refine ⟨50296257444996770370304745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134123353186658054320812653 50296257444996770370304745)
    ·
      refine ⟨37722193083747577777728559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50296257444996770370304745 37722193083747577777728559)
      ·
        refine ⟨56583289625621366666592839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37722193083747577777728559 56583289625621366666592839)
        ·
          refine ⟨84874934438432049999889259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56583289625621366666592839 84874934438432049999889259)
          ·
            refine ⟨127312401657648074999833889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84874934438432049999889259 127312401657648074999833889)
            ·
              refine ⟨95484301243236056249875417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127312401657648074999833889 95484301243236056249875417)
              ·
                refine ⟨71613225932427042187406563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95484301243236056249875417 71613225932427042187406563)
                ·
                  refine ⟨107419838898640563281109845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71613225932427042187406563 107419838898640563281109845)
                  ·
                    refine ⟨629413118546722050475253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 107419838898640563281109845 629413118546722050475253)
                    ·
                      rfl

theorem cell23_3677333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 2, 1, 9].length) (baseStart_3677333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3677333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3677333 prefixEnd_3677333 := by exact prefixLift 3677333
  have htrace : WordTrace (prefixWord ++ tailWord_3677333) baseStart_3677333 baseEnd_3677333 := by
    simpa [prefixWord, tailWord_3677333, baseEnd_3677333] using wordTrace_append hprefix tailTrace_3677333
  have hstable : (prefixWord ++ tailWord_3677333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3677333).length < 2 ^ (prefixWord ++ tailWord_3677333).sum := by decide
  have hdescent : baseEnd_3677333 < baseStart_3677333 := by decide
  rcases family_descends (prefixWord ++ tailWord_3677333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3677377 : List Nat := [1, 2, 6, 1, 1, 1, 1, 1, 2, 2, 5]
def baseStart_3677377 : Nat := 118140960795 + 3677377 * 2 ^ 59
def prefixEnd_3677377 : Nat := 4983230072969 + 3 ^ 40 * 3677377 * 2
def baseEnd_3677377 : Nat := 1888261948788963979275557

theorem tailTrace_3677377 : CollatzResearch.WordTrace tailWord_3677377 prefixEnd_3677377 1888261948788963979275557 := by
  unfold tailWord_3677377
  simp only [CollatzResearch.WordTrace]
  refine ⟨134124957998498649835414385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89416638665665766556942923 134124957998498649835414385)
  ·
    refine ⟨100593718498873987376560789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134124957998498649835414385 100593718498873987376560789)
    ·
      refine ⟨4715330554634718158276287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 100593718498873987376560789 4715330554634718158276287)
      ·
        refine ⟨7072995831952077237414431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4715330554634718158276287 7072995831952077237414431)
        ·
          refine ⟨10609493747928115856121647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7072995831952077237414431 10609493747928115856121647)
          ·
            refine ⟨15914240621892173784182471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10609493747928115856121647 15914240621892173784182471)
            ·
              refine ⟨23871360932838260676273707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15914240621892173784182471 23871360932838260676273707)
              ·
                refine ⟨35807041399257391014410561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23871360932838260676273707 35807041399257391014410561)
                ·
                  refine ⟨26855281049443043260807921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35807041399257391014410561 26855281049443043260807921)
                  ·
                    refine ⟨20141460787082282445605941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26855281049443043260807921 20141460787082282445605941)
                    ·
                      refine ⟨1888261948788963979275557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20141460787082282445605941 1888261948788963979275557)
                      ·
                        rfl

theorem cell23_3677377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_3677377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3677377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3677377 prefixEnd_3677377 := by exact prefixLift 3677377
  have htrace : WordTrace (prefixWord ++ tailWord_3677377) baseStart_3677377 baseEnd_3677377 := by
    simpa [prefixWord, tailWord_3677377, baseEnd_3677377] using wordTrace_append hprefix tailTrace_3677377
  have hstable : (prefixWord ++ tailWord_3677377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3677377).length < 2 ^ (prefixWord ++ tailWord_3677377).sum := by decide
  have hdescent : baseEnd_3677377 < baseStart_3677377 := by decide
  rcases family_descends (prefixWord ++ tailWord_3677377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3677415 : List Nat := [1, 1, 5, 3, 3, 1, 2, 1, 2, 1, 3]
def baseStart_3677415 : Nat := 118140960795 + 3677415 * 2 ^ 59
def prefixEnd_3677415 : Nat := 4983230072969 + 3 ^ 40 * 3677415 * 2
def baseEnd_3677415 : Nat := 1888281461053834830600383

theorem tailTrace_3677415 : CollatzResearch.WordTrace tailWord_3677415 prefixEnd_3677415 1888281461053834830600383 := by
  unfold tailWord_3677415
  simp only [CollatzResearch.WordTrace]
  refine ⟨134126343972360982325297699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89417562648240654883531799 134126343972360982325297699)
  ·
    refine ⟨201189515958541473487946549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134126343972360982325297699 201189515958541473487946549)
    ·
      refine ⟨18861517121113263139494989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 201189515958541473487946549 18861517121113263139494989)
      ·
        refine ⟨7073068920417473677310621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18861517121113263139494989 7073068920417473677310621)
        ·
          refine ⟨2652400845156552628991483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7073068920417473677310621 2652400845156552628991483)
          ·
            refine ⟨3978601267734828943487225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2652400845156552628991483 3978601267734828943487225)
            ·
              refine ⟨2983950950801121707615419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3978601267734828943487225 2983950950801121707615419)
              ·
                refine ⟨4475926426201682561423129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2983950950801121707615419 4475926426201682561423129)
                ·
                  refine ⟨3356944819651261921067347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4475926426201682561423129 3356944819651261921067347)
                  ·
                    refine ⟨5035417229476892881601021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3356944819651261921067347 5035417229476892881601021)
                    ·
                      refine ⟨1888281461053834830600383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5035417229476892881601021 1888281461053834830600383)
                      ·
                        rfl

theorem cell23_3677415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 2, 1, 2, 1, 3].length) (baseStart_3677415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3677415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3677415 prefixEnd_3677415 := by exact prefixLift 3677415
  have htrace : WordTrace (prefixWord ++ tailWord_3677415) baseStart_3677415 baseEnd_3677415 := by
    simpa [prefixWord, tailWord_3677415, baseEnd_3677415] using wordTrace_append hprefix tailTrace_3677415
  have hstable : (prefixWord ++ tailWord_3677415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3677415).length < 2 ^ (prefixWord ++ tailWord_3677415).sum := by decide
  have hdescent : baseEnd_3677415 < baseStart_3677415 := by decide
  rcases family_descends (prefixWord ++ tailWord_3677415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3677520 : List Nat := [2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 8]
def baseStart_3677520 : Nat := 118140960795 + 3677520 * 2 ^ 59
def prefixEnd_3677520 : Nat := 4983230072969 + 3 ^ 40 * 3677520 * 2
def baseEnd_3677520 : Nat := 1888335376522556919787399

theorem tailTrace_3677520 : CollatzResearch.WordTrace tailWord_3677520 prefixEnd_3677520 1888335376522556919787399 := by
  unfold tailWord_3677520
  simp only [CollatzResearch.WordTrace]
  refine ⟨67065086818490292628935007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89420115757987056838580009 67065086818490292628935007)
  ·
    refine ⟨100597630227735438943402511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67065086818490292628935007 100597630227735438943402511)
    ·
      refine ⟨150896445341603158415103767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100597630227735438943402511 150896445341603158415103767)
      ·
        refine ⟨226344668012404737622655651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150896445341603158415103767 226344668012404737622655651)
        ·
          refine ⟨339517002018607106433983477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226344668012404737622655651 339517002018607106433983477)
          ·
            refine ⟨31829718939244416228185951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 339517002018607106433983477 31829718939244416228185951)
            ·
              refine ⟨47744578408866624342278927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31829718939244416228185951 47744578408866624342278927)
              ·
                refine ⟨71616867613299936513418391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47744578408866624342278927 71616867613299936513418391)
                ·
                  refine ⟨107425301419949904770127587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71616867613299936513418391 107425301419949904770127587)
                  ·
                    refine ⟨161137952129924857155191381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 107425301419949904770127587 161137952129924857155191381)
                    ·
                      refine ⟨1888335376522556919787399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 161137952129924857155191381 1888335376522556919787399)
                      ·
                        rfl

theorem cell23_3677520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 8].length) (baseStart_3677520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3677520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3677520 prefixEnd_3677520 := by exact prefixLift 3677520
  have htrace : WordTrace (prefixWord ++ tailWord_3677520) baseStart_3677520 baseEnd_3677520 := by
    simpa [prefixWord, tailWord_3677520, baseEnd_3677520] using wordTrace_append hprefix tailTrace_3677520
  have hstable : (prefixWord ++ tailWord_3677520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3677520).length < 2 ^ (prefixWord ++ tailWord_3677520).sum := by decide
  have hdescent : baseEnd_3677520 < baseStart_3677520 := by decide
  rcases family_descends (prefixWord ++ tailWord_3677520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3677554 : List Nat := [3, 2, 1, 2, 1, 2, 1, 3, 1, 5, 2]
def baseStart_3677554 : Nat := 118140960795 + 3677554 * 2 ^ 59
def prefixEnd_3677554 : Nat := 4983230072969 + 3 ^ 40 * 3677554 * 2
def baseEnd_3677554 : Nat := 1888352834864809786762243

theorem tailTrace_3677554 : CollatzResearch.WordTrace tailWord_3677554 prefixEnd_3677554 1888352834864809786762243 := by
  unfold tailWord_3677554
  simp only [CollatzResearch.WordTrace]
  refine ⟨33532853429714352266151929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89420942479238272709738477 33532853429714352266151929)
  ·
    refine ⟨25149640072285764199613947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33532853429714352266151929 25149640072285764199613947)
    ·
      refine ⟨37724460108428646299420921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25149640072285764199613947 37724460108428646299420921)
      ·
        refine ⟨28293345081321484724565691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37724460108428646299420921 28293345081321484724565691)
        ·
          refine ⟨42440017621982227086848537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28293345081321484724565691 42440017621982227086848537)
          ·
            refine ⟨31830013216486670315136403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42440017621982227086848537 31830013216486670315136403)
            ·
              refine ⟨47745019824730005472704605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31830013216486670315136403 47745019824730005472704605)
              ·
                refine ⟨17904382434273752052264227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47745019824730005472704605 17904382434273752052264227)
                ·
                  refine ⟨26856573651410628078396341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17904382434273752052264227 26856573651410628078396341)
                  ·
                    refine ⟨2517803779819746382349657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26856573651410628078396341 2517803779819746382349657)
                    ·
                      refine ⟨1888352834864809786762243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2517803779819746382349657 1888352834864809786762243)
                      ·
                        rfl

theorem cell23_3677554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 3, 1, 5, 2].length) (baseStart_3677554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3677554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3677554 prefixEnd_3677554 := by exact prefixLift 3677554
  have htrace : WordTrace (prefixWord ++ tailWord_3677554) baseStart_3677554 baseEnd_3677554 := by
    simpa [prefixWord, tailWord_3677554, baseEnd_3677554] using wordTrace_append hprefix tailTrace_3677554
  have hstable : (prefixWord ++ tailWord_3677554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3677554).length < 2 ^ (prefixWord ++ tailWord_3677554).sum := by decide
  have hdescent : baseEnd_3677554 < baseStart_3677554 := by decide
  rcases family_descends (prefixWord ++ tailWord_3677554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3677571 : List Nat := [1, 1, 1, 3, 5, 2, 1, 2, 2, 3, 2]
def baseStart_3677571 : Nat := 118140960795 + 3677571 * 2 ^ 59
def prefixEnd_3677571 : Nat := 4983230072969 + 3 ^ 40 * 3677571 * 2
def baseEnd_3677571 : Nat := 1888361564035936220249665

theorem tailTrace_3677571 : CollatzResearch.WordTrace tailWord_3677571 prefixEnd_3677571 1888361564035936220249665 := by
  unfold tailWord_3677571
  simp only [CollatzResearch.WordTrace]
  refine ⟨134132033759795820967976567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89421355839863880645317711 134132033759795820967976567)
  ·
    refine ⟨201198050639693731451964851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134132033759795820967976567 201198050639693731451964851)
    ·
      refine ⟨301797075959540597177947277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201198050639693731451964851 301797075959540597177947277)
      ·
        refine ⟨113173903484827723941730229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 301797075959540597177947277 113173903484827723941730229)
        ·
          refine ⟨10610053451702599119537209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 113173903484827723941730229 10610053451702599119537209)
          ·
            refine ⟨7957540088776949339652907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10610053451702599119537209 7957540088776949339652907)
            ·
              refine ⟨11936310133165424009479361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7957540088776949339652907 11936310133165424009479361)
              ·
                refine ⟨8952232599874068007109521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11936310133165424009479361 8952232599874068007109521)
                ·
                  refine ⟨6714174449905551005332141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8952232599874068007109521 6714174449905551005332141)
                  ·
                    refine ⟨2517815418714581626999553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6714174449905551005332141 2517815418714581626999553)
                    ·
                      refine ⟨1888361564035936220249665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2517815418714581626999553 1888361564035936220249665)
                      ·
                        rfl

theorem cell23_3677571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 2, 2, 3, 2].length) (baseStart_3677571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3677571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3677571 prefixEnd_3677571 := by exact prefixLift 3677571
  have htrace : WordTrace (prefixWord ++ tailWord_3677571) baseStart_3677571 baseEnd_3677571 := by
    simpa [prefixWord, tailWord_3677571, baseEnd_3677571] using wordTrace_append hprefix tailTrace_3677571
  have hstable : (prefixWord ++ tailWord_3677571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3677571).length < 2 ^ (prefixWord ++ tailWord_3677571).sum := by decide
  have hdescent : baseEnd_3677571 < baseStart_3677571 := by decide
  rcases family_descends (prefixWord ++ tailWord_3677571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3677607 : List Nat := [1, 1, 6, 1, 1, 1, 1, 11]
def baseStart_3677607 : Nat := 118140960795 + 3677607 * 2 ^ 59
def prefixEnd_3677607 : Nat := 4983230072969 + 3 ^ 40 * 3677607 * 2
def baseEnd_3677607 : Nat := 69940001827388817755537

theorem tailTrace_3677607 : CollatzResearch.WordTrace tailWord_3677607 prefixEnd_3677607 69940001827388817755537 := by
  unfold tailWord_3677607
  simp only [CollatzResearch.WordTrace]
  refine ⟨134133346787665399116287075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89422231191776932744191383 134133346787665399116287075)
  ·
    refine ⟨201200020181498098674430613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134133346787665399116287075 201200020181498098674430613)
    ·
      refine ⟨9431250946007723375363935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 201200020181498098674430613 9431250946007723375363935)
      ·
        refine ⟨14146876419011585063045903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9431250946007723375363935 14146876419011585063045903)
        ·
          refine ⟨21220314628517377594568855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14146876419011585063045903 21220314628517377594568855)
          ·
            refine ⟨31830471942776066391853283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21220314628517377594568855 31830471942776066391853283)
            ·
              refine ⟨47745707914164099587779925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31830471942776066391853283 47745707914164099587779925)
              ·
                refine ⟨69940001827388817755537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 47745707914164099587779925 69940001827388817755537)
                ·
                  rfl

theorem cell23_3677607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 11].length) (baseStart_3677607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3677607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3677607 prefixEnd_3677607 := by exact prefixLift 3677607
  have htrace : WordTrace (prefixWord ++ tailWord_3677607) baseStart_3677607 baseEnd_3677607 := by
    simpa [prefixWord, tailWord_3677607, baseEnd_3677607] using wordTrace_append hprefix tailTrace_3677607
  have hstable : (prefixWord ++ tailWord_3677607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3677607).length < 2 ^ (prefixWord ++ tailWord_3677607).sum := by decide
  have hdescent : baseEnd_3677607 < baseStart_3677607 := by decide
  rcases family_descends (prefixWord ++ tailWord_3677607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3677621 : List Nat := [1, 3, 3, 2, 2, 3, 1, 1, 1, 1, 5]
def baseStart_3677621 : Nat := 118140960795 + 3677621 * 2 ^ 59
def prefixEnd_3677621 : Nat := 4983230072969 + 3 ^ 40 * 3677621 * 2
def baseEnd_3677621 : Nat := 1888387238068661024624435

theorem tailTrace_3677621 : CollatzResearch.WordTrace tailWord_3677621 prefixEnd_3677621 1888387238068661024624435 := by
  unfold tailWord_3677621
  simp only [CollatzResearch.WordTrace]
  refine ⟨134133857409614679507296717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89422571606409786338197811 134133857409614679507296717)
  ·
    refine ⟨50300196528605504815236269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134133857409614679507296717 50300196528605504815236269)
    ·
      refine ⟨18862573698227064305713601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50300196528605504815236269 18862573698227064305713601)
      ·
        refine ⟨14146930273670298229285201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18862573698227064305713601 14146930273670298229285201)
        ·
          refine ⟨10610197705252723671963901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14146930273670298229285201 10610197705252723671963901)
          ·
            refine ⟨3978824139469771376986463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10610197705252723671963901 3978824139469771376986463)
            ·
              refine ⟨5968236209204657065479695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3978824139469771376986463 5968236209204657065479695)
              ·
                refine ⟨8952354313806985598219543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5968236209204657065479695 8952354313806985598219543)
                ·
                  refine ⟨13428531470710478397329315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8952354313806985598219543 13428531470710478397329315)
                  ·
                    refine ⟨20142797206065717595993973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13428531470710478397329315 20142797206065717595993973)
                    ·
                      refine ⟨1888387238068661024624435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20142797206065717595993973 1888387238068661024624435)
                      ·
                        rfl

theorem cell23_3677621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 1, 1, 1, 1, 5].length) (baseStart_3677621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3677621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3677621 prefixEnd_3677621 := by exact prefixLift 3677621
  have htrace : WordTrace (prefixWord ++ tailWord_3677621) baseStart_3677621 baseEnd_3677621 := by
    simpa [prefixWord, tailWord_3677621, baseEnd_3677621] using wordTrace_append hprefix tailTrace_3677621
  have hstable : (prefixWord ++ tailWord_3677621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3677621).length < 2 ^ (prefixWord ++ tailWord_3677621).sum := by decide
  have hdescent : baseEnd_3677621 < baseStart_3677621 := by decide
  rcases family_descends (prefixWord ++ tailWord_3677621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3677628 : List Nat := [2, 2, 2, 4, 2, 1, 2, 2, 2, 4]
def baseStart_3677628 : Nat := 118140960795 + 3677628 * 2 ^ 59
def prefixEnd_3677628 : Nat := 4983230072969 + 3 ^ 40 * 3677628 * 2
def baseEnd_3677628 : Nat := 629463610811080832412301

theorem tailTrace_3677628 : CollatzResearch.WordTrace tailWord_3677628 prefixEnd_3677628 629463610811080832412301 := by
  unfold tailWord_3677628
  simp only [CollatzResearch.WordTrace]
  refine ⟨67067056360294659851400769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89422741813726213135201025 67067056360294659851400769)
  ·
    refine ⟨50300292270220994888550577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67067056360294659851400769 50300292270220994888550577)
    ·
      refine ⟨37725219202665746166412933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50300292270220994888550577 37725219202665746166412933)
      ·
        refine ⟨7073478600499827406202425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37725219202665746166412933 7073478600499827406202425)
        ·
          refine ⟨5305108950374870554651819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7073478600499827406202425 5305108950374870554651819)
          ·
            refine ⟨7957663425562305831977729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5305108950374870554651819 7957663425562305831977729)
            ·
              refine ⟨5968247569171729373983297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7957663425562305831977729 5968247569171729373983297)
              ·
                refine ⟨4476185676878797030487473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5968247569171729373983297 4476185676878797030487473)
                ·
                  refine ⟨3357139257659097772865605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4476185676878797030487473 3357139257659097772865605)
                  ·
                    refine ⟨629463610811080832412301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3357139257659097772865605 629463610811080832412301)
                    ·
                      rfl

theorem cell23_3677628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 2, 2, 2, 4].length) (baseStart_3677628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3677628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3677628 prefixEnd_3677628 := by exact prefixLift 3677628
  have htrace : WordTrace (prefixWord ++ tailWord_3677628) baseStart_3677628 baseEnd_3677628 := by
    simpa [prefixWord, tailWord_3677628, baseEnd_3677628] using wordTrace_append hprefix tailTrace_3677628
  have hstable : (prefixWord ++ tailWord_3677628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3677628).length < 2 ^ (prefixWord ++ tailWord_3677628).sum := by decide
  have hdescent : baseEnd_3677628 < baseStart_3677628 := by decide
  rcases family_descends (prefixWord ++ tailWord_3677628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3677635 : List Nat := [1, 1, 1, 3, 1, 1, 8, 2, 1, 2, 2]
def baseStart_3677635 : Nat := 118140960795 + 3677635 * 2 ^ 59
def prefixEnd_3677635 : Nat := 4983230072969 + 3 ^ 40 * 3677635 * 2
def baseEnd_3677635 : Nat := 1888394426797823969849371

theorem tailTrace_3677635 : CollatzResearch.WordTrace tailWord_3677635 prefixEnd_3677635 1888394426797823969849371 := by
  unfold tailWord_3677635
  simp only [CollatzResearch.WordTrace]
  refine ⟨134134368031563959898306359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89422912021042639932204239 134134368031563959898306359)
  ·
    refine ⟨201201552047345939847459539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134134368031563959898306359 201201552047345939847459539)
    ·
      refine ⟨301802328071018909771189309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201201552047345939847459539 301802328071018909771189309)
      ·
        refine ⟨113175873026632091164195991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 301802328071018909771189309 113175873026632091164195991)
        ·
          refine ⟨169763809539948136746293987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113175873026632091164195991 169763809539948136746293987)
          ·
            refine ⟨254645714309922205119440981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169763809539948136746293987 254645714309922205119440981)
            ·
              refine ⟨2984129464569400841243449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 254645714309922205119440981 2984129464569400841243449)
              ·
                refine ⟨2238097098427050630932587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2984129464569400841243449 2238097098427050630932587)
                ·
                  refine ⟨3357145647640575946398881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2238097098427050630932587 3357145647640575946398881)
                  ·
                    refine ⟨2517859235730431959799161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3357145647640575946398881 2517859235730431959799161)
                    ·
                      refine ⟨1888394426797823969849371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2517859235730431959799161 1888394426797823969849371)
                      ·
                        rfl

theorem cell23_3677635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 8, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 8, 2, 1, 2, 2].length) (baseStart_3677635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3677635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3677635 prefixEnd_3677635 := by exact prefixLift 3677635
  have htrace : WordTrace (prefixWord ++ tailWord_3677635) baseStart_3677635 baseEnd_3677635 := by
    simpa [prefixWord, tailWord_3677635, baseEnd_3677635] using wordTrace_append hprefix tailTrace_3677635
  have hstable : (prefixWord ++ tailWord_3677635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3677635).length < 2 ^ (prefixWord ++ tailWord_3677635).sum := by decide
  have hdescent : baseEnd_3677635 < baseStart_3677635 := by decide
  rcases family_descends (prefixWord ++ tailWord_3677635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3677678 : List Nat := [4, 1, 2, 1, 2, 1, 3, 3, 1, 3, 2]
def baseStart_3677678 : Nat := 118140960795 + 3677678 * 2 ^ 59
def prefixEnd_3677678 : Nat := 4983230072969 + 3 ^ 40 * 3677678 * 2
def baseEnd_3677678 : Nat := 1888416506465967301611673

theorem tailTrace_3677678 : CollatzResearch.WordTrace tailWord_3677678 prefixEnd_3677678 1888416506465967301611673 := by
  unfold tailWord_3677678
  simp only [CollatzResearch.WordTrace]
  refine ⟨16766992046301022280265211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89423957580272118828081125 16766992046301022280265211)
  ·
    refine ⟨25150488069451533420397817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16766992046301022280265211 25150488069451533420397817)
    ·
      refine ⟨18862866052088650065298363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25150488069451533420397817 18862866052088650065298363)
      ·
        refine ⟨28294299078132975097947545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18862866052088650065298363 28294299078132975097947545)
        ·
          refine ⟨21220724308599731323460659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28294299078132975097947545 21220724308599731323460659)
          ·
            refine ⟨31831086462899596985190989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21220724308599731323460659 31831086462899596985190989)
            ·
              refine ⟨11936657423587348869446621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31831086462899596985190989 11936657423587348869446621)
              ·
                refine ⟨4476246533845255826042483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11936657423587348869446621 4476246533845255826042483)
                ·
                  refine ⟨6714369800767883739063725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4476246533845255826042483 6714369800767883739063725)
                  ·
                    refine ⟨2517888675287956402148897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6714369800767883739063725 2517888675287956402148897)
                    ·
                      refine ⟨1888416506465967301611673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2517888675287956402148897 1888416506465967301611673)
                      ·
                        rfl

theorem cell23_3677678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 3, 1, 3, 2].length) (baseStart_3677678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3677678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3677678 prefixEnd_3677678 := by exact prefixLift 3677678
  have htrace : WordTrace (prefixWord ++ tailWord_3677678) baseStart_3677678 baseEnd_3677678 := by
    simpa [prefixWord, tailWord_3677678, baseEnd_3677678] using wordTrace_append hprefix tailTrace_3677678
  have hstable : (prefixWord ++ tailWord_3677678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3677678).length < 2 ^ (prefixWord ++ tailWord_3677678).sum := by decide
  have hdescent : baseEnd_3677678 < baseStart_3677678 := by decide
  rcases family_descends (prefixWord ++ tailWord_3677678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3677685 : List Nat := [1, 3, 5, 1, 1, 1, 3, 2, 2, 1, 3]
def baseStart_3677685 : Nat := 118140960795 + 3677685 * 2 ^ 59
def prefixEnd_3677685 : Nat := 4983230072969 + 3 ^ 40 * 3677685 * 2
def baseEnd_3677685 : Nat := 1888420100830548774224141

theorem tailTrace_3677685 : CollatzResearch.WordTrace tailWord_3677685 prefixEnd_3677685 1888420100830548774224141 := by
  unfold tailWord_3677685
  simp only [CollatzResearch.WordTrace]
  refine ⟨134136191681382818437626509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89424127787588545625084339 134136191681382818437626509)
  ·
    refine ⟨50301071880518556914109941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134136191681382818437626509 50301071880518556914109941)
    ·
      refine ⟨4715725488798614710697807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 50301071880518556914109941 4715725488798614710697807)
      ·
        refine ⟨7073588233197922066046711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4715725488798614710697807 7073588233197922066046711)
        ·
          refine ⟨10610382349796883099070067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7073588233197922066046711 10610382349796883099070067)
          ·
            refine ⟨15915573524695324648605101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10610382349796883099070067 15915573524695324648605101)
            ·
              refine ⟨5968340071760746743226913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15915573524695324648605101 5968340071760746743226913)
              ·
                refine ⟨4476255053820560057420185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5968340071760746743226913 4476255053820560057420185)
                ·
                  refine ⟨3357191290365420043065139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4476255053820560057420185 3357191290365420043065139)
                  ·
                    refine ⟨5035786935548130064597709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3357191290365420043065139 5035786935548130064597709)
                    ·
                      refine ⟨1888420100830548774224141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5035786935548130064597709 1888420100830548774224141)
                      ·
                        rfl

theorem cell23_3677685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_3677685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3677685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3677685 prefixEnd_3677685 := by exact prefixLift 3677685
  have htrace : WordTrace (prefixWord ++ tailWord_3677685) baseStart_3677685 baseEnd_3677685 := by
    simpa [prefixWord, tailWord_3677685, baseEnd_3677685] using wordTrace_append hprefix tailTrace_3677685
  have hstable : (prefixWord ++ tailWord_3677685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3677685).length < 2 ^ (prefixWord ++ tailWord_3677685).sum := by decide
  have hdescent : baseEnd_3677685 < baseStart_3677685 := by decide
  rcases family_descends (prefixWord ++ tailWord_3677685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3677691 : List Nat := [1, 1, 1, 1, 1, 3, 2, 5, 4, 2, 2]
def baseStart_3677691 : Nat := 118140960795 + 3677691 * 2 ^ 59
def prefixEnd_3677691 : Nat := 4983230072969 + 3 ^ 40 * 3677691 * 2
def baseEnd_3677691 : Nat := 1888423181714475750749113

theorem tailTrace_3677691 : CollatzResearch.WordTrace tailWord_3677691 prefixEnd_3677691 1888423181714475750749113 := by
  unfold tailWord_3677691
  simp only [CollatzResearch.WordTrace]
  refine ⟨134136410519361081462344927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89424273679574054308229951 134136410519361081462344927)
  ·
    refine ⟨201204615779041622193517391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134136410519361081462344927 201204615779041622193517391)
    ·
      refine ⟨301806923668562433290276087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201204615779041622193517391 301806923668562433290276087)
      ·
        refine ⟨452710385502843649935414131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301806923668562433290276087 452710385502843649935414131)
        ·
          refine ⟨679065578254265474903121197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 452710385502843649935414131 679065578254265474903121197)
          ·
            refine ⟨254649591845349553088670449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 679065578254265474903121197 254649591845349553088670449)
            ·
              refine ⟨190987193884012164816502837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 254649591845349553088670449 190987193884012164816502837)
              ·
                refine ⟨17905049426626140451547141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 190987193884012164816502837 17905049426626140451547141)
                ·
                  refine ⟨3357196767492401334665089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17905049426626140451547141 3357196767492401334665089)
                  ·
                    refine ⟨2517897575619301000998817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3357196767492401334665089 2517897575619301000998817)
                    ·
                      refine ⟨1888423181714475750749113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2517897575619301000998817 1888423181714475750749113)
                      ·
                        rfl

theorem cell23_3677691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 5, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 5, 4, 2, 2].length) (baseStart_3677691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3677691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3677691 prefixEnd_3677691 := by exact prefixLift 3677691
  have htrace : WordTrace (prefixWord ++ tailWord_3677691) baseStart_3677691 baseEnd_3677691 := by
    simpa [prefixWord, tailWord_3677691, baseEnd_3677691] using wordTrace_append hprefix tailTrace_3677691
  have hstable : (prefixWord ++ tailWord_3677691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3677691).length < 2 ^ (prefixWord ++ tailWord_3677691).sum := by decide
  have hdescent : baseEnd_3677691 < baseStart_3677691 := by decide
  rcases family_descends (prefixWord ++ tailWord_3677691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3677704 : List Nat := [2, 1, 3, 2, 1, 1, 4, 1, 2, 2, 4]
def baseStart_3677704 : Nat := 118140960795 + 3677704 * 2 ^ 59
def prefixEnd_3677704 : Nat := 4983230072969 + 3 ^ 40 * 3677704 * 2
def baseEnd_3677704 : Nat := 1888429856962984199886553

theorem tailTrace_3677704 : CollatzResearch.WordTrace tailWord_3677704 prefixEnd_3677704 1888429856962984199886553 := by
  unfold tailWord_3677704
  simp only [CollatzResearch.WordTrace]
  refine ⟨67068442334156992341284083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89424589778875989788378777 67068442334156992341284083)
  ·
    refine ⟨100602663501235488511926125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67068442334156992341284083 100602663501235488511926125)
    ·
      refine ⟨37725998812963308191972297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100602663501235488511926125 37725998812963308191972297)
      ·
        refine ⟨28294499109722481143979223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37725998812963308191972297 28294499109722481143979223)
        ·
          refine ⟨42441748664583721715968835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28294499109722481143979223 42441748664583721715968835)
          ·
            refine ⟨63662622996875582573953253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42441748664583721715968835 63662622996875582573953253)
            ·
              refine ⟨11936741811914171732616235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63662622996875582573953253 11936741811914171732616235)
              ·
                refine ⟨17905112717871257598924353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11936741811914171732616235 17905112717871257598924353)
                ·
                  refine ⟨13428834538403443199193265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17905112717871257598924353 13428834538403443199193265)
                  ·
                    refine ⟨10071625903802582399394949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13428834538403443199193265 10071625903802582399394949)
                    ·
                      refine ⟨1888429856962984199886553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10071625903802582399394949 1888429856962984199886553)
                      ·
                        rfl

theorem cell23_3677704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 1, 2, 2, 4].length) (baseStart_3677704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3677704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3677704 prefixEnd_3677704 := by exact prefixLift 3677704
  have htrace : WordTrace (prefixWord ++ tailWord_3677704) baseStart_3677704 baseEnd_3677704 := by
    simpa [prefixWord, tailWord_3677704, baseEnd_3677704] using wordTrace_append hprefix tailTrace_3677704
  have hstable : (prefixWord ++ tailWord_3677704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3677704).length < 2 ^ (prefixWord ++ tailWord_3677704).sum := by decide
  have hdescent : baseEnd_3677704 < baseStart_3677704 := by decide
  rcases family_descends (prefixWord ++ tailWord_3677704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3677754 : List Nat := [3, 1, 1, 1, 3, 2, 3, 1, 1, 2, 5]
def baseStart_3677754 : Nat := 118140960795 + 3677754 * 2 ^ 59
def prefixEnd_3677754 : Nat := 4983230072969 + 3 ^ 40 * 3677754 * 2
def baseEnd_3677754 : Nat := 1888455530995709004261323

theorem tailTrace_3677754 : CollatzResearch.WordTrace tailWord_3677754 prefixEnd_3677754 1888455530995709004261323 := by
  unfold tailWord_3677754
  simp only [CollatzResearch.WordTrace]
  refine ⟨33534677079533210805472079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89425805545421895481258877 33534677079533210805472079)
  ·
    refine ⟨50302015619299816208208119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33534677079533210805472079 50302015619299816208208119)
    ·
      refine ⟨75453023428949724312312179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50302015619299816208208119 75453023428949724312312179)
      ·
        refine ⟨113179535143424586468468269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75453023428949724312312179 113179535143424586468468269)
        ·
          refine ⟨42442325678784219925675601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113179535143424586468468269 42442325678784219925675601)
          ·
            refine ⟨31831744259088164944256701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42442325678784219925675601 31831744259088164944256701)
            ·
              refine ⟨11936904097158061854096263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31831744259088164944256701 11936904097158061854096263)
              ·
                refine ⟨17905356145737092781144395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11936904097158061854096263 17905356145737092781144395)
                ·
                  refine ⟨26858034218605639171716593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17905356145737092781144395 26858034218605639171716593)
                  ·
                    refine ⟨20143525663954229378787445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26858034218605639171716593 20143525663954229378787445)
                    ·
                      refine ⟨1888455530995709004261323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20143525663954229378787445 1888455530995709004261323)
                      ·
                        rfl

theorem cell23_3677754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 1, 1, 2, 5].length) (baseStart_3677754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3677754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3677754 prefixEnd_3677754 := by exact prefixLift 3677754
  have htrace : WordTrace (prefixWord ++ tailWord_3677754) baseStart_3677754 baseEnd_3677754 := by
    simpa [prefixWord, tailWord_3677754, baseEnd_3677754] using wordTrace_append hprefix tailTrace_3677754
  have hstable : (prefixWord ++ tailWord_3677754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3677754).length < 2 ^ (prefixWord ++ tailWord_3677754).sum := by decide
  have hdescent : baseEnd_3677754 < baseStart_3677754 := by decide
  rcases family_descends (prefixWord ++ tailWord_3677754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3677781 : List Nat := [1, 3, 2, 2, 1, 1, 1, 2, 4, 4, 2]
def baseStart_3677781 : Nat := 118140960795 + 3677781 * 2 ^ 59
def prefixEnd_3677781 : Nat := 4983230072969 + 3 ^ 40 * 3677781 * 2
def baseEnd_3677781 : Nat := 1888469394973380398623699

theorem tailTrace_3677781 : CollatzResearch.WordTrace tailWord_3677781 prefixEnd_3677781 1888469394973380398623699 := by
  unfold tailWord_3677781
  simp only [CollatzResearch.WordTrace]
  refine ⟨134139693089035026833121197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89426462059356684555414131 134139693089035026833121197)
  ·
    refine ⟨50302384908388135062420449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134139693089035026833121197 50302384908388135062420449)
    ·
      refine ⟨37726788681291101296815337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50302384908388135062420449 37726788681291101296815337)
      ·
        refine ⟨28295091510968325972611503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37726788681291101296815337 28295091510968325972611503)
        ·
          refine ⟨42442637266452488958917255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28295091510968325972611503 42442637266452488958917255)
          ·
            refine ⟨63663955899678733438375883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42442637266452488958917255 63663955899678733438375883)
            ·
              refine ⟨95495933849518100157563825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63663955899678733438375883 95495933849518100157563825)
              ·
                refine ⟨71621950387138575118172869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95495933849518100157563825 71621950387138575118172869)
                ·
                  refine ⟨13429115697588482834657413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71621950387138575118172869 13429115697588482834657413)
                  ·
                    refine ⟨2517959193297840531498265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13429115697588482834657413 2517959193297840531498265)
                    ·
                      refine ⟨1888469394973380398623699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2517959193297840531498265 1888469394973380398623699)
                      ·
                        rfl

theorem cell23_3677781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 2, 4, 4, 2].length) (baseStart_3677781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3677781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3677781 prefixEnd_3677781 := by exact prefixLift 3677781
  have htrace : WordTrace (prefixWord ++ tailWord_3677781) baseStart_3677781 baseEnd_3677781 := by
    simpa [prefixWord, tailWord_3677781, baseEnd_3677781] using wordTrace_append hprefix tailTrace_3677781
  have hstable : (prefixWord ++ tailWord_3677781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3677781).length < 2 ^ (prefixWord ++ tailWord_3677781).sum := by decide
  have hdescent : baseEnd_3677781 < baseStart_3677781 := by decide
  rcases family_descends (prefixWord ++ tailWord_3677781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3677801 : List Nat := [1, 2, 1, 1, 1, 4, 4, 2, 2, 2, 3]
def baseStart_3677801 : Nat := 118140960795 + 3677801 * 2 ^ 59
def prefixEnd_3677801 : Nat := 4983230072969 + 3 ^ 40 * 3677801 * 2
def baseEnd_3677801 : Nat := 1888479664586470320373607

theorem tailTrace_3677801 : CollatzResearch.WordTrace tailWord_3677801 prefixEnd_3677801 1888479664586470320373607 := by
  unfold tailWord_3677801
  simp only [CollatzResearch.WordTrace]
  refine ⟨134140422548962570248849257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89426948365975046832566171 134140422548962570248849257)
  ·
    refine ⟨100605316911721927686636943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134140422548962570248849257 100605316911721927686636943)
    ·
      refine ⟨150907975367582891529955415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100605316911721927686636943 150907975367582891529955415)
      ·
        refine ⟨226361963051374337294933123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150907975367582891529955415 226361963051374337294933123)
        ·
          refine ⟨339542944577061505942399685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226361963051374337294933123 339542944577061505942399685)
          ·
            refine ⟨63664302108199032364199941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 339542944577061505942399685 63664302108199032364199941)
            ·
              refine ⟨11937056645287318568287489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63664302108199032364199941 11937056645287318568287489)
              ·
                refine ⟨8952792483965488926215617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11937056645287318568287489 8952792483965488926215617)
                ·
                  refine ⟨6714594362974116694661713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8952792483965488926215617 6714594362974116694661713)
                  ·
                    refine ⟨5035945772230587520996285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6714594362974116694661713 5035945772230587520996285)
                    ·
                      refine ⟨1888479664586470320373607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5035945772230587520996285 1888479664586470320373607)
                      ·
                        rfl

theorem cell23_3677801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 2, 2, 2, 3].length) (baseStart_3677801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3677801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3677801 prefixEnd_3677801 := by exact prefixLift 3677801
  have htrace : WordTrace (prefixWord ++ tailWord_3677801) baseStart_3677801 baseEnd_3677801 := by
    simpa [prefixWord, tailWord_3677801, baseEnd_3677801] using wordTrace_append hprefix tailTrace_3677801
  have hstable : (prefixWord ++ tailWord_3677801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3677801).length < 2 ^ (prefixWord ++ tailWord_3677801).sum := by decide
  have hdescent : baseEnd_3677801 < baseStart_3677801 := by decide
  rcases family_descends (prefixWord ++ tailWord_3677801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3677821 : List Nat := [1, 4, 1, 1, 4, 1, 2, 3, 6]
def baseStart_3677821 : Nat := 118140960795 + 3677821 * 2 ^ 59
def prefixEnd_3677821 : Nat := 4983230072969 + 3 ^ 40 * 3677821 * 2
def baseEnd_3677821 : Nat := 209832214911062249124835

theorem tailTrace_3677821 : CollatzResearch.WordTrace tailWord_3677821 prefixEnd_3677821 209832214911062249124835 := by
  unfold tailWord_3677821
  simp only [CollatzResearch.WordTrace]
  refine ⟨134141152008890113664577317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89427434672593409109718211 134141152008890113664577317)
  ·
    refine ⟨25151466001666896312108247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134141152008890113664577317 25151466001666896312108247)
    ·
      refine ⟨37727199002500344468162371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25151466001666896312108247 37727199002500344468162371)
      ·
        refine ⟨56590798503750516702243557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37727199002500344468162371 56590798503750516702243557)
        ·
          refine ⟨10610774719453221881670667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56590798503750516702243557 10610774719453221881670667)
          ·
            refine ⟨15916162079179832822506001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10610774719453221881670667 15916162079179832822506001)
            ·
              refine ⟨11937121559384874616879501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15916162079179832822506001 11937121559384874616879501)
              ·
                refine ⟨4476420584769327981329813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11937121559384874616879501 4476420584769327981329813)
                ·
                  refine ⟨209832214911062249124835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4476420584769327981329813 209832214911062249124835)
                  ·
                    rfl

theorem cell23_3677821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 3, 6].length) (baseStart_3677821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3677821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3677821 prefixEnd_3677821 := by exact prefixLift 3677821
  have htrace : WordTrace (prefixWord ++ tailWord_3677821) baseStart_3677821 baseEnd_3677821 := by
    simpa [prefixWord, tailWord_3677821, baseEnd_3677821] using wordTrace_append hprefix tailTrace_3677821
  have hstable : (prefixWord ++ tailWord_3677821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3677821).length < 2 ^ (prefixWord ++ tailWord_3677821).sum := by decide
  have hdescent : baseEnd_3677821 < baseStart_3677821 := by decide
  rcases family_descends (prefixWord ++ tailWord_3677821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3677832 : List Nat := [2, 1, 3, 5, 2, 1, 1, 1, 2, 1, 4]
def baseStart_3677832 : Nat := 118140960795 + 3677832 * 2 ^ 59
def prefixEnd_3677832 : Nat := 4983230072969 + 3 ^ 40 * 3677832 * 2
def baseEnd_3677832 : Nat := 1888495582486759699085965

theorem tailTrace_3677832 : CollatzResearch.WordTrace tailWord_3677832 prefixEnd_3677832 1888495582486759699085965 := by
  unfold tailWord_3677832
  simp only [CollatzResearch.WordTrace]
  refine ⟨67070776605925131271613875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89427702141233508362151833 67070776605925131271613875)
  ·
    refine ⟨100606164908887696907420813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67070776605925131271613875 100606164908887696907420813)
    ·
      refine ⟨37727311840832886340282805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100606164908887696907420813 37727311840832886340282805)
      ·
        refine ⟨3536935485078083094401513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37727311840832886340282805 3536935485078083094401513)
        ·
          refine ⟨2652701613808562320801135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3536935485078083094401513 2652701613808562320801135)
          ·
            refine ⟨3979052420712843481201703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2652701613808562320801135 3979052420712843481201703)
            ·
              refine ⟨5968578631069265221802555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3979052420712843481201703 5968578631069265221802555)
              ·
                refine ⟨8952867946603897832703833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5968578631069265221802555 8952867946603897832703833)
                ·
                  refine ⟨6714650959952923374527875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8952867946603897832703833 6714650959952923374527875)
                  ·
                    refine ⟨10071976439929385061791813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6714650959952923374527875 10071976439929385061791813)
                    ·
                      refine ⟨1888495582486759699085965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10071976439929385061791813 1888495582486759699085965)
                      ·
                        rfl

theorem cell23_3677832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_3677832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3677832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3677832 prefixEnd_3677832 := by exact prefixLift 3677832
  have htrace : WordTrace (prefixWord ++ tailWord_3677832) baseStart_3677832 baseEnd_3677832 := by
    simpa [prefixWord, tailWord_3677832, baseEnd_3677832] using wordTrace_append hprefix tailTrace_3677832
  have hstable : (prefixWord ++ tailWord_3677832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3677832).length < 2 ^ (prefixWord ++ tailWord_3677832).sum := by decide
  have hdescent : baseEnd_3677832 < baseStart_3677832 := by decide
  rcases family_descends (prefixWord ++ tailWord_3677832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3677842 : List Nat := [3, 2, 3, 1, 3, 1, 2, 3, 1, 4]
def baseStart_3677842 : Nat := 118140960795 + 3677842 * 2 ^ 59
def prefixEnd_3677842 : Nat := 4983230072969 + 3 ^ 40 * 3677842 * 2
def baseEnd_3677842 : Nat := 629500239097768219986973

theorem tailTrace_3677842 : CollatzResearch.WordTrace tailWord_3677842 prefixEnd_3677842 629500239097768219986973 := by
  unfold tailWord_3677842
  simp only [CollatzResearch.WordTrace]
  refine ⟨33535479485453508562772945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89427945294542689500727853 33535479485453508562772945)
  ·
    refine ⟨25151609614090131422079709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33535479485453508562772945 25151609614090131422079709)
    ·
      refine ⟨9431853605283799283279891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25151609614090131422079709 9431853605283799283279891)
      ·
        refine ⟨14147780407925698924919837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9431853605283799283279891 14147780407925698924919837)
        ·
          refine ⟨5305417652972137096844939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14147780407925698924919837 5305417652972137096844939)
          ·
            refine ⟨7958126479458205645267409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5305417652972137096844939 7958126479458205645267409)
            ·
              refine ⟨5968594859593654233950557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7958126479458205645267409 5968594859593654233950557)
              ·
                refine ⟨2238223072347620337731459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5968594859593654233950557 2238223072347620337731459)
                ·
                  refine ⟨3357334608521430506597189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2238223072347620337731459 3357334608521430506597189)
                  ·
                    refine ⟨629500239097768219986973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3357334608521430506597189 629500239097768219986973)
                    ·
                      rfl

theorem cell23_3677842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 2, 3, 1, 4].length) (baseStart_3677842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3677842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3677842 prefixEnd_3677842 := by exact prefixLift 3677842
  have htrace : WordTrace (prefixWord ++ tailWord_3677842) baseStart_3677842 baseEnd_3677842 := by
    simpa [prefixWord, tailWord_3677842, baseEnd_3677842] using wordTrace_append hprefix tailTrace_3677842
  have hstable : (prefixWord ++ tailWord_3677842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3677842).length < 2 ^ (prefixWord ++ tailWord_3677842).sum := by decide
  have hdescent : baseEnd_3677842 < baseStart_3677842 := by decide
  rcases family_descends (prefixWord ++ tailWord_3677842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3677855 : List Nat := [1, 1, 2, 7, 1, 2, 1, 2, 6]
def baseStart_3677855 : Nat := 118140960795 + 3677855 * 2 ^ 59
def prefixEnd_3677855 : Nat := 4983230072969 + 3 ^ 40 * 3677855 * 2
def baseEnd_3677855 : Nat := 209834154726868123233151

theorem tailTrace_3677855 : CollatzResearch.WordTrace tailWord_3677855 prefixEnd_3677855 209834154726868123233151 := by
  unfold tailWord_3677855
  simp only [CollatzResearch.WordTrace]
  refine ⟨134142392090766937471315019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89428261393844624980876679 134142392090766937471315019)
  ·
    refine ⟨201213588136150406206972529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134142392090766937471315019 201213588136150406206972529)
    ·
      refine ⟨150910191102112804655229397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201213588136150406206972529 150910191102112804655229397)
      ·
        refine ⟨3536957603955768859106939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 150910191102112804655229397 3536957603955768859106939)
        ·
          refine ⟨5305436405933653288660409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3536957603955768859106939 5305436405933653288660409)
          ·
            refine ⟨3979077304450239966495307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5305436405933653288660409 3979077304450239966495307)
            ·
              refine ⟨5968615956675359949742961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3979077304450239966495307 5968615956675359949742961)
              ·
                refine ⟨4476461967506519962307221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5968615956675359949742961 4476461967506519962307221)
                ·
                  refine ⟨209834154726868123233151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4476461967506519962307221 209834154726868123233151)
                  ·
                    rfl

theorem cell23_3677855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 1, 2, 6].length) (baseStart_3677855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3677855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3677855 prefixEnd_3677855 := by exact prefixLift 3677855
  have htrace : WordTrace (prefixWord ++ tailWord_3677855) baseStart_3677855 baseEnd_3677855 := by
    simpa [prefixWord, tailWord_3677855, baseEnd_3677855] using wordTrace_append hprefix tailTrace_3677855
  have hstable : (prefixWord ++ tailWord_3677855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3677855).length < 2 ^ (prefixWord ++ tailWord_3677855).sum := by decide
  have hdescent : baseEnd_3677855 < baseStart_3677855 := by decide
  rcases family_descends (prefixWord ++ tailWord_3677855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3677881 : List Nat := [1, 2, 1, 4, 1, 1, 5, 1, 1, 6]
def baseStart_3677881 : Nat := 118140960795 + 3677881 * 2 ^ 59
def prefixEnd_3677881 : Nat := 4983230072969 + 3 ^ 40 * 3677881 * 2
def baseEnd_3677881 : Nat := 629506914346276669124413

theorem tailTrace_3677881 : CollatzResearch.WordTrace tailWord_3677881 prefixEnd_3677881 629506914346276669124413 := by
  unfold tailWord_3677881
  simp only [CollatzResearch.WordTrace]
  refine ⟨134143340388672743911761497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89428893592448495941174331 134143340388672743911761497)
  ·
    refine ⟨100607505291504557933821123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134143340388672743911761497 100607505291504557933821123)
    ·
      refine ⟨150911257937256836900731685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100607505291504557933821123 150911257937256836900731685)
      ·
        refine ⟨28295860863235656918887191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 150911257937256836900731685 28295860863235656918887191)
        ·
          refine ⟨42443791294853485378330787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28295860863235656918887191 42443791294853485378330787)
          ·
            refine ⟨63665686942280228067496181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42443791294853485378330787 63665686942280228067496181)
            ·
              refine ⟨5968658150838771381327767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63665686942280228067496181 5968658150838771381327767)
              ·
                refine ⟨8952987226258157071991651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5968658150838771381327767 8952987226258157071991651)
                ·
                  refine ⟨13429480839387235607987477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8952987226258157071991651 13429480839387235607987477)
                  ·
                    refine ⟨629506914346276669124413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13429480839387235607987477 629506914346276669124413)
                    ·
                      rfl

theorem cell23_3677881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 5, 1, 1, 6].length) (baseStart_3677881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3677881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3677881 prefixEnd_3677881 := by exact prefixLift 3677881
  have htrace : WordTrace (prefixWord ++ tailWord_3677881) baseStart_3677881 baseEnd_3677881 := by
    simpa [prefixWord, tailWord_3677881, baseEnd_3677881] using wordTrace_append hprefix tailTrace_3677881
  have hstable : (prefixWord ++ tailWord_3677881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3677881).length < 2 ^ (prefixWord ++ tailWord_3677881).sum := by decide
  have hdescent : baseEnd_3677881 < baseStart_3677881 := by decide
  rcases family_descends (prefixWord ++ tailWord_3677881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3677888 : List Nat := [2, 1, 1, 2, 4, 1, 4, 2, 1, 1, 4]
def baseStart_3677888 : Nat := 118140960795 + 3677888 * 2 ^ 59
def prefixEnd_3677888 : Nat := 4983230072969 + 3 ^ 40 * 3677888 * 2
def baseEnd_3677888 : Nat := 1888524337403411479985707

theorem tailTrace_3677888 : CollatzResearch.WordTrace tailWord_3677888 prefixEnd_3677888 1888524337403411479985707 := by
  unfold tailWord_3677888
  simp only [CollatzResearch.WordTrace]
  refine ⟨67071797849823692053633159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89429063799764922738177545 67071797849823692053633159)
  ·
    refine ⟨100607696774735538080449739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67071797849823692053633159 100607696774735538080449739)
    ·
      refine ⟨150911545162103307120674609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100607696774735538080449739 150911545162103307120674609)
      ·
        refine ⟨113183658871577480340505957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150911545162103307120674609 113183658871577480340505957)
        ·
          refine ⟨21221936038420777563844867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 113183658871577480340505957 21221936038420777563844867)
          ·
            refine ⟨31832904057631166345767301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21221936038420777563844867 31832904057631166345767301)
            ·
              refine ⟨5968669510805843689831369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31832904057631166345767301 5968669510805843689831369)
              ·
                refine ⟨4476502133104382767373527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5968669510805843689831369 4476502133104382767373527)
                ·
                  refine ⟨6714753199656574151060291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4476502133104382767373527 6714753199656574151060291)
                  ·
                    refine ⟨10072129799484861226590437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6714753199656574151060291 10072129799484861226590437)
                    ·
                      refine ⟨1888524337403411479985707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10072129799484861226590437 1888524337403411479985707)
                      ·
                        rfl

theorem cell23_3677888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 4, 2, 1, 1, 4].length) (baseStart_3677888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3677888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3677888 prefixEnd_3677888 := by exact prefixLift 3677888
  have htrace : WordTrace (prefixWord ++ tailWord_3677888) baseStart_3677888 baseEnd_3677888 := by
    simpa [prefixWord, tailWord_3677888, baseEnd_3677888] using wordTrace_append hprefix tailTrace_3677888
  have hstable : (prefixWord ++ tailWord_3677888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3677888).length < 2 ^ (prefixWord ++ tailWord_3677888).sum := by decide
  have hdescent : baseEnd_3677888 < baseStart_3677888 := by decide
  rcases family_descends (prefixWord ++ tailWord_3677888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3677908 : List Nat := [2, 4, 1, 3, 1, 1, 1, 3, 1, 1, 5]
def baseStart_3677908 : Nat := 118140960795 + 3677908 * 2 ^ 59
def prefixEnd_3677908 : Nat := 4983230072969 + 3 ^ 40 * 3677908 * 2
def baseEnd_3677908 : Nat := 1888534607016501401735615

theorem tailTrace_3677908 : CollatzResearch.WordTrace tailWord_3677908 prefixEnd_3677908 1888534607016501401735615 := by
  unfold tailWord_3677908
  simp only [CollatzResearch.WordTrace]
  refine ⟨67072162579787463761497189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89429550106383285015329585 67072162579787463761497189)
  ·
    refine ⟨12576030483710149455280723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67072162579787463761497189 12576030483710149455280723)
    ·
      refine ⟨18864045725565224182921085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12576030483710149455280723 18864045725565224182921085)
      ·
        refine ⟨7074017147086959068595407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18864045725565224182921085 7074017147086959068595407)
        ·
          refine ⟨10611025720630438602893111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7074017147086959068595407 10611025720630438602893111)
          ·
            refine ⟨15916538580945657904339667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10611025720630438602893111 15916538580945657904339667)
            ·
              refine ⟨23874807871418486856509501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15916538580945657904339667 23874807871418486856509501)
              ·
                refine ⟨8953052951781932571191063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23874807871418486856509501 8953052951781932571191063)
                ·
                  refine ⟨13429579427672898856786595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8953052951781932571191063 13429579427672898856786595)
                  ·
                    refine ⟨20144369141509348285179893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13429579427672898856786595 20144369141509348285179893)
                    ·
                      refine ⟨1888534607016501401735615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20144369141509348285179893 1888534607016501401735615)
                      ·
                        rfl

theorem cell23_3677908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_3677908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3677908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3677908 prefixEnd_3677908 := by exact prefixLift 3677908
  have htrace : WordTrace (prefixWord ++ tailWord_3677908) baseStart_3677908 baseEnd_3677908 := by
    simpa [prefixWord, tailWord_3677908, baseEnd_3677908] using wordTrace_append hprefix tailTrace_3677908
  have hstable : (prefixWord ++ tailWord_3677908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3677908).length < 2 ^ (prefixWord ++ tailWord_3677908).sum := by decide
  have hdescent : baseEnd_3677908 < baseStart_3677908 := by decide
  rcases family_descends (prefixWord ++ tailWord_3677908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3677916 : List Nat := [2, 2, 5, 1, 2, 1, 3, 2, 1, 1, 3]
def baseStart_3677916 : Nat := 118140960795 + 3677916 * 2 ^ 59
def prefixEnd_3677916 : Nat := 4983230072969 + 3 ^ 40 * 3677916 * 2
def baseEnd_3677916 : Nat := 1888538714861737370435579

theorem tailTrace_3677916 : CollatzResearch.WordTrace tailWord_3677916 prefixEnd_3677916 1888538714861737370435579 := by
  unfold tailWord_3677916
  simp only [CollatzResearch.WordTrace]
  refine ⟨67072308471772972444642801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89429744629030629926190401 67072308471772972444642801)
  ·
    refine ⟨50304231353829729333482101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67072308471772972444642801 50304231353829729333482101)
    ·
      refine ⟨4716021689421537125013947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 50304231353829729333482101 4716021689421537125013947)
      ·
        refine ⟨7074032534132305687520921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4716021689421537125013947 7074032534132305687520921)
        ·
          refine ⟨5305524400599229265640691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7074032534132305687520921 5305524400599229265640691)
          ·
            refine ⟨7958286600898843898461037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5305524400599229265640691 7958286600898843898461037)
            ·
              refine ⟨2984357475337066461922889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7958286600898843898461037 2984357475337066461922889)
              ·
                refine ⟨2238268106502799846442167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2984357475337066461922889 2238268106502799846442167)
                ·
                  refine ⟨3357402159754199769663251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2238268106502799846442167 3357402159754199769663251)
                  ·
                    refine ⟨5036103239631299654494877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3357402159754199769663251 5036103239631299654494877)
                    ·
                      refine ⟨1888538714861737370435579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5036103239631299654494877 1888538714861737370435579)
                      ·
                        rfl

theorem cell23_3677916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 3, 2, 1, 1, 3].length) (baseStart_3677916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3677916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3677916 prefixEnd_3677916 := by exact prefixLift 3677916
  have htrace : WordTrace (prefixWord ++ tailWord_3677916) baseStart_3677916 baseEnd_3677916 := by
    simpa [prefixWord, tailWord_3677916, baseEnd_3677916] using wordTrace_append hprefix tailTrace_3677916
  have hstable : (prefixWord ++ tailWord_3677916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3677916).length < 2 ^ (prefixWord ++ tailWord_3677916).sum := by decide
  have hdescent : baseEnd_3677916 < baseStart_3677916 := by decide
  rcases family_descends (prefixWord ++ tailWord_3677916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3677938 : List Nat := [3, 2, 1, 3, 1, 1, 2, 3, 1, 3, 3]
def baseStart_3677938 : Nat := 118140960795 + 3677938 * 2 ^ 59
def prefixEnd_3677938 : Nat := 4983230072969 + 3 ^ 40 * 3677938 * 2
def baseEnd_3677938 : Nat := 1888550011436136284360477

theorem tailTrace_3677938 : CollatzResearch.WordTrace tailWord_3677938 prefixEnd_3677938 1888550011436136284360477 := by
  unfold tailWord_3677938
  simp only [CollatzResearch.WordTrace]
  refine ⟨33536354837366560661646617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89430279566310828431057645 33536354837366560661646617)
  ·
    refine ⟨25152266128024920496234963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33536354837366560661646617 25152266128024920496234963)
    ·
      refine ⟨37728399192037380744352445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25152266128024920496234963 37728399192037380744352445)
      ·
        refine ⟨14148149697014017779132167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37728399192037380744352445 14148149697014017779132167)
        ·
          refine ⟨21222224545521026668698251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14148149697014017779132167 21222224545521026668698251)
          ·
            refine ⟨31833336818281540003047377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21222224545521026668698251 31833336818281540003047377)
            ·
              refine ⟨23875002613711155002285533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31833336818281540003047377 23875002613711155002285533)
              ·
                refine ⟨8953125980141683125857075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23875002613711155002285533 8953125980141683125857075)
                ·
                  refine ⟨13429688970212524688785613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8953125980141683125857075 13429688970212524688785613)
                  ·
                    refine ⟨5036133363829696758294605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13429688970212524688785613 5036133363829696758294605)
                    ·
                      refine ⟨1888550011436136284360477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5036133363829696758294605 1888550011436136284360477)
                      ·
                        rfl

theorem cell23_3677938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 3, 1, 3, 3].length) (baseStart_3677938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3677938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3677938 prefixEnd_3677938 := by exact prefixLift 3677938
  have htrace : WordTrace (prefixWord ++ tailWord_3677938) baseStart_3677938 baseEnd_3677938 := by
    simpa [prefixWord, tailWord_3677938, baseEnd_3677938] using wordTrace_append hprefix tailTrace_3677938
  have hstable : (prefixWord ++ tailWord_3677938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3677938).length < 2 ^ (prefixWord ++ tailWord_3677938).sum := by decide
  have hdescent : baseEnd_3677938 < baseStart_3677938 := by decide
  rcases family_descends (prefixWord ++ tailWord_3677938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3677942 : List Nat := [5, 1, 1, 1, 1, 5, 1, 2, 1, 2, 3]
def baseStart_3677942 : Nat := 118140960795 + 3677942 * 2 ^ 59
def prefixEnd_3677942 : Nat := 4983230072969 + 3 ^ 40 * 3677942 * 2
def baseEnd_3677942 : Nat := 1888552065358754268710459

theorem tailTrace_3677942 : CollatzResearch.WordTrace tailWord_3677942 prefixEnd_3677942 1888552065358754268710459 := by
  unfold tailWord_3677942
  simp only [CollatzResearch.WordTrace]
  refine ⟨8384097827590734458108255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 89430376827634500886488053 8384097827590734458108255)
  ·
    refine ⟨12576146741386101687162383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8384097827590734458108255 12576146741386101687162383)
    ·
      refine ⟨18864220112079152530743575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12576146741386101687162383 18864220112079152530743575)
      ·
        refine ⟨28296330168118728796115363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18864220112079152530743575 28296330168118728796115363)
        ·
          refine ⟨42444495252178093194173045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28296330168118728796115363 42444495252178093194173045)
          ·
            refine ⟨3979171429891696236953723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42444495252178093194173045 3979171429891696236953723)
            ·
              refine ⟨5968757144837544355430585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3979171429891696236953723 5968757144837544355430585)
              ·
                refine ⟨4476567858628158266572939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5968757144837544355430585 4476567858628158266572939)
                ·
                  refine ⟨6714851787942237399859409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4476567858628158266572939 6714851787942237399859409)
                  ·
                    refine ⟨5036138840956678049894557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6714851787942237399859409 5036138840956678049894557)
                    ·
                      refine ⟨1888552065358754268710459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5036138840956678049894557 1888552065358754268710459)
                      ·
                        rfl

theorem cell23_3677942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 1, 2, 1, 2, 3].length) (baseStart_3677942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3677942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3677942 prefixEnd_3677942 := by exact prefixLift 3677942
  have htrace : WordTrace (prefixWord ++ tailWord_3677942) baseStart_3677942 baseEnd_3677942 := by
    simpa [prefixWord, tailWord_3677942, baseEnd_3677942] using wordTrace_append hprefix tailTrace_3677942
  have hstable : (prefixWord ++ tailWord_3677942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3677942).length < 2 ^ (prefixWord ++ tailWord_3677942).sum := by decide
  have hdescent : baseEnd_3677942 < baseStart_3677942 := by decide
  rcases family_descends (prefixWord ++ tailWord_3677942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3677988 : List Nat := [2, 3, 1, 3, 2, 2, 1, 1, 2, 6]
def baseStart_3677988 : Nat := 118140960795 + 3677988 * 2 ^ 59
def prefixEnd_3677988 : Nat := 4983230072969 + 3 ^ 40 * 3677988 * 2
def baseEnd_3677988 : Nat := 629525228489620362911749

theorem tailTrace_3677988 : CollatzResearch.WordTrace tailWord_3677988 prefixEnd_3677988 629525228489620362911749 := by
  unfold tailWord_3677988
  simp only [CollatzResearch.WordTrace]
  refine ⟨67073621499642550592953309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89431495332856734123937745 67073621499642550592953309)
  ·
    refine ⟨25152608062365956472357491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67073621499642550592953309 25152608062365956472357491)
    ·
      refine ⟨37728912093548934708536237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25152608062365956472357491 37728912093548934708536237)
      ·
        refine ⟨14148342035080850515701089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37728912093548934708536237 14148342035080850515701089)
        ·
          refine ⟨10611256526310637886775817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14148342035080850515701089 10611256526310637886775817)
          ·
            refine ⟨7958442394732978415081863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10611256526310637886775817 7958442394732978415081863)
            ·
              refine ⟨11937663592099467622622795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7958442394732978415081863 11937663592099467622622795)
              ·
                refine ⟨17906495388149201433934193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11937663592099467622622795 17906495388149201433934193)
                ·
                  refine ⟨13429871541111901075450645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17906495388149201433934193 13429871541111901075450645)
                  ·
                    refine ⟨629525228489620362911749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13429871541111901075450645 629525228489620362911749)
                    ·
                      rfl

theorem cell23_3677988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 1, 2, 6].length) (baseStart_3677988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3677988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3677988 prefixEnd_3677988 := by exact prefixLift 3677988
  have htrace : WordTrace (prefixWord ++ tailWord_3677988) baseStart_3677988 baseEnd_3677988 := by
    simpa [prefixWord, tailWord_3677988, baseEnd_3677988] using wordTrace_append hprefix tailTrace_3677988
  have hstable : (prefixWord ++ tailWord_3677988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3677988).length < 2 ^ (prefixWord ++ tailWord_3677988).sum := by decide
  have hdescent : baseEnd_3677988 < baseStart_3677988 := by decide
  rcases family_descends (prefixWord ++ tailWord_3677988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3678001 : List Nat := [1, 2, 2, 3, 2, 2, 1, 1, 9]
def baseStart_3678001 : Nat := 118140960795 + 3678001 * 2 ^ 59
def prefixEnd_3678001 : Nat := 4983230072969 + 3 ^ 40 * 3678001 * 2
def baseEnd_3678001 : Nat := 209842484524152170874743

theorem tailTrace_3678001 : CollatzResearch.WordTrace tailWord_3678001 prefixEnd_3678001 209842484524152170874743 := by
  unfold tailWord_3678001
  simp only [CollatzResearch.WordTrace]
  refine ⟨134147717148238004406129857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89431811432158669604086571 134147717148238004406129857)
  ·
    refine ⟨100610787861178503304597393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134147717148238004406129857 100610787861178503304597393)
    ·
      refine ⟨75458090895883877478448045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100610787861178503304597393 75458090895883877478448045)
      ·
        refine ⟨28296784085956454054418017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75458090895883877478448045 28296784085956454054418017)
        ·
          refine ⟨21222588064467340540813513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28296784085956454054418017 21222588064467340540813513)
          ·
            refine ⟨15916941048350505405610135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21222588064467340540813513 15916941048350505405610135)
            ·
              refine ⟨23875411572525758108415203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15916941048350505405610135 23875411572525758108415203)
              ·
                refine ⟨35813117358788637162622805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23875411572525758108415203 35813117358788637162622805)
                ·
                  refine ⟨209842484524152170874743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 35813117358788637162622805 209842484524152170874743)
                  ·
                    rfl

theorem cell23_3678001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 1, 9].length) (baseStart_3678001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3678001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3678001 prefixEnd_3678001 := by exact prefixLift 3678001
  have htrace : WordTrace (prefixWord ++ tailWord_3678001) baseStart_3678001 baseEnd_3678001 := by
    simpa [prefixWord, tailWord_3678001, baseEnd_3678001] using wordTrace_append hprefix tailTrace_3678001
  have hstable : (prefixWord ++ tailWord_3678001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3678001).length < 2 ^ (prefixWord ++ tailWord_3678001).sum := by decide
  have hdescent : baseEnd_3678001 < baseStart_3678001 := by decide
  rcases family_descends (prefixWord ++ tailWord_3678001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3678029 : List Nat := [1, 6, 1, 2, 1, 2, 1, 1, 4, 2, 2]
def baseStart_3678029 : Nat := 118140960795 + 3678029 * 2 ^ 59
def prefixEnd_3678029 : Nat := 4983230072969 + 3 ^ 40 * 3678029 * 2
def baseEnd_3678029 : Nat := 1888596738175695428322559

theorem tailTrace_3678029 : CollatzResearch.WordTrace tailWord_3678029 prefixEnd_3678029 1888596738175695428322559 := by
  unfold tailWord_3678029
  simp only [CollatzResearch.WordTrace]
  refine ⟨134148738392136565188149141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89432492261424376792099427 134148738392136565188149141)
  ·
    refine ⟨6288222112131401493194491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 134148738392136565188149141 6288222112131401493194491)
    ·
      refine ⟨9432333168197102239791737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6288222112131401493194491 9432333168197102239791737)
      ·
        refine ⟨7074249876147826679843803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9432333168197102239791737 7074249876147826679843803)
        ·
          refine ⟨10611374814221740019765705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7074249876147826679843803 10611374814221740019765705)
          ·
            refine ⟨7958531110666305014824279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10611374814221740019765705 7958531110666305014824279)
            ·
              refine ⟨11937796665999457522236419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7958531110666305014824279 11937796665999457522236419)
              ·
                refine ⟨17906694998999186283354629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11937796665999457522236419 17906694998999186283354629)
                ·
                  refine ⟨3357505312312347428128993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17906694998999186283354629 3357505312312347428128993)
                  ·
                    refine ⟨2518128984234260571096745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3357505312312347428128993 2518128984234260571096745)
                    ·
                      refine ⟨1888596738175695428322559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2518128984234260571096745 1888596738175695428322559)
                      ·
                        rfl

theorem cell23_3678029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 1, 4, 2, 2].length) (baseStart_3678029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3678029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3678029 prefixEnd_3678029 := by exact prefixLift 3678029
  have htrace : WordTrace (prefixWord ++ tailWord_3678029) baseStart_3678029 baseEnd_3678029 := by
    simpa [prefixWord, tailWord_3678029, baseEnd_3678029] using wordTrace_append hprefix tailTrace_3678029
  have hstable : (prefixWord ++ tailWord_3678029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3678029).length < 2 ^ (prefixWord ++ tailWord_3678029).sum := by decide
  have hdescent : baseEnd_3678029 < baseStart_3678029 := by decide
  rcases family_descends (prefixWord ++ tailWord_3678029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3678041 : List Nat := [1, 2, 1, 2, 2, 3, 2, 1, 1, 1, 7]
def baseStart_3678041 : Nat := 118140960795 + 3678041 * 2 ^ 59
def prefixEnd_3678041 : Nat := 4983230072969 + 3 ^ 40 * 3678041 * 2
def baseEnd_3678041 : Nat := 1888602899943549381372503

theorem tailTrace_3678041 : CollatzResearch.WordTrace tailWord_3678041 prefixEnd_3678041 1888602899943549381372503 := by
  unfold tailWord_3678041
  simp only [CollatzResearch.WordTrace]
  refine ⟨134149176068093091237585977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89432784045395394158390651 134149176068093091237585977)
  ·
    refine ⟨100611882051069818428189483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134149176068093091237585977 100611882051069818428189483)
    ·
      refine ⟨150917823076604727642284225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100611882051069818428189483 150917823076604727642284225)
      ·
        refine ⟨113188367307453545731713169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150917823076604727642284225 113188367307453545731713169)
        ·
          refine ⟨84891275480590159298784877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113188367307453545731713169 84891275480590159298784877)
          ·
            refine ⟨31834228305221309737044329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84891275480590159298784877 31834228305221309737044329)
            ·
              refine ⟨23875671228915982302783247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31834228305221309737044329 23875671228915982302783247)
              ·
                refine ⟨35813506843373973454174871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23875671228915982302783247 35813506843373973454174871)
                ·
                  refine ⟨53720260265060960181262307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35813506843373973454174871 53720260265060960181262307)
                  ·
                    refine ⟨80580390397591440271893461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53720260265060960181262307 80580390397591440271893461)
                    ·
                      refine ⟨1888602899943549381372503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 80580390397591440271893461 1888602899943549381372503)
                      ·
                        rfl

theorem cell23_3678041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 1, 1, 1, 7].length) (baseStart_3678041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3678041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3678041 prefixEnd_3678041 := by exact prefixLift 3678041
  have htrace : WordTrace (prefixWord ++ tailWord_3678041) baseStart_3678041 baseEnd_3678041 := by
    simpa [prefixWord, tailWord_3678041, baseEnd_3678041] using wordTrace_append hprefix tailTrace_3678041
  have hstable : (prefixWord ++ tailWord_3678041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3678041).length < 2 ^ (prefixWord ++ tailWord_3678041).sum := by decide
  have hdescent : baseEnd_3678041 < baseStart_3678041 := by decide
  rcases family_descends (prefixWord ++ tailWord_3678041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3678071 : List Nat := [1, 1, 3, 1, 1, 2, 1, 1, 4, 3, 5]
def baseStart_3678071 : Nat := 118140960795 + 3678071 * 2 ^ 59
def prefixEnd_3678071 : Nat := 4983230072969 + 3 ^ 40 * 3678071 * 2
def baseEnd_3678071 : Nat := 1888618304363184263997365

theorem tailTrace_3678071 : CollatzResearch.WordTrace tailWord_3678071 prefixEnd_3678071 1888618304363184263997365 := by
  unfold tailWord_3678071
  simp only [CollatzResearch.WordTrace]
  refine ⟨134150270257984406361178067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89433513505322937574118711 134150270257984406361178067)
  ·
    refine ⟨201225405386976609541767101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134150270257984406361178067 201225405386976609541767101)
    ·
      refine ⟨75459527020116228578162663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201225405386976609541767101 75459527020116228578162663)
      ·
        refine ⟨113189290530174342867243995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75459527020116228578162663 113189290530174342867243995)
        ·
          refine ⟨169783935795261514300865993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113189290530174342867243995 169783935795261514300865993)
          ·
            refine ⟨127337951846446135725649495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169783935795261514300865993 127337951846446135725649495)
            ·
              refine ⟨191006927769669203588474243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127337951846446135725649495 191006927769669203588474243)
              ·
                refine ⟨286510391654503805382711365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 191006927769669203588474243 286510391654503805382711365)
                ·
                  refine ⟨53720698435219463509258381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 286510391654503805382711365 53720698435219463509258381)
                  ·
                    refine ⟨20145261913207298815971893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53720698435219463509258381 20145261913207298815971893)
                    ·
                      refine ⟨1888618304363184263997365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20145261913207298815971893 1888618304363184263997365)
                      ·
                        rfl

theorem cell23_3678071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 4, 3, 5].length) (baseStart_3678071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3678071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3678071 prefixEnd_3678071 := by exact prefixLift 3678071
  have htrace : WordTrace (prefixWord ++ tailWord_3678071) baseStart_3678071 baseEnd_3678071 := by
    simpa [prefixWord, tailWord_3678071, baseEnd_3678071] using wordTrace_append hprefix tailTrace_3678071
  have hstable : (prefixWord ++ tailWord_3678071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3678071).length < 2 ^ (prefixWord ++ tailWord_3678071).sum := by decide
  have hdescent : baseEnd_3678071 < baseStart_3678071 := by decide
  rcases family_descends (prefixWord ++ tailWord_3678071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3678175 : List Nat := [1, 1, 2, 3, 4, 1, 2, 1, 3, 1, 4]
def baseStart_3678175 : Nat := 118140960795 + 3678175 * 2 ^ 59
def prefixEnd_3678175 : Nat := 4983230072969 + 3 ^ 40 * 3678175 * 2
def baseEnd_3678175 : Nat := 1888671706351251857096887

theorem tailTrace_3678175 : CollatzResearch.WordTrace tailWord_3678175 prefixEnd_3678175 1888671706351251857096887 := by
  unfold tailWord_3678175
  simp only [CollatzResearch.WordTrace]
  refine ⟨134154063449607632122963979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89436042299738421415309319 134154063449607632122963979)
  ·
    refine ⟨201231095174411448184445969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134154063449607632122963979 201231095174411448184445969)
    ·
      refine ⟨150923321380808586138334477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201231095174411448184445969 150923321380808586138334477)
      ·
        refine ⟨56596245517803219801875429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150923321380808586138334477 56596245517803219801875429)
        ·
          refine ⟨10611796034588103712851643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56596245517803219801875429 10611796034588103712851643)
          ·
            refine ⟨15917694051882155569277465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10611796034588103712851643 15917694051882155569277465)
            ·
              refine ⟨11938270538911616676958099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15917694051882155569277465 11938270538911616676958099)
              ·
                refine ⟨17907405808367425015437149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11938270538911616676958099 17907405808367425015437149)
                ·
                  refine ⟨6715277178137784380788931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17907405808367425015437149 6715277178137784380788931)
                  ·
                    refine ⟨10072915767206676571183397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6715277178137784380788931 10072915767206676571183397)
                    ·
                      refine ⟨1888671706351251857096887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10072915767206676571183397 1888671706351251857096887)
                      ·
                        rfl

theorem cell23_3678175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 1, 3, 1, 4].length) (baseStart_3678175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3678175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3678175 prefixEnd_3678175 := by exact prefixLift 3678175
  have htrace : WordTrace (prefixWord ++ tailWord_3678175) baseStart_3678175 baseEnd_3678175 := by
    simpa [prefixWord, tailWord_3678175, baseEnd_3678175] using wordTrace_append hprefix tailTrace_3678175
  have hstable : (prefixWord ++ tailWord_3678175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3678175).length < 2 ^ (prefixWord ++ tailWord_3678175).sum := by decide
  have hdescent : baseEnd_3678175 < baseStart_3678175 := by decide
  rcases family_descends (prefixWord ++ tailWord_3678175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3678179 : List Nat := [1, 1, 1, 6, 1, 4, 1, 1, 2, 3, 2]
def baseStart_3678179 : Nat := 118140960795 + 3678179 * 2 ^ 59
def prefixEnd_3678179 : Nat := 4983230072969 + 3 ^ 40 * 3678179 * 2
def baseEnd_3678179 : Nat := 1888673760273869841446869

theorem tailTrace_3678179 : CollatzResearch.WordTrace tailWord_3678179 prefixEnd_3678179 1888673760273869841446869 := by
  unfold tailWord_3678179
  simp only [CollatzResearch.WordTrace]
  refine ⟨134154209341593140806109591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89436139561062093870739727 134154209341593140806109591)
  ·
    refine ⟨201231314012389711209164387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134154209341593140806109591 201231314012389711209164387)
    ·
      refine ⟨301846971018584566813746581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201231314012389711209164387 301846971018584566813746581)
      ·
        refine ⟨14149076766496151569394371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 301846971018584566813746581 14149076766496151569394371)
        ·
          refine ⟨21223615149744227354091557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14149076766496151569394371 21223615149744227354091557)
          ·
            refine ⟨3979427840577042628892167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21223615149744227354091557 3979427840577042628892167)
            ·
              refine ⟨5969141760865563943338251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3979427840577042628892167 5969141760865563943338251)
              ·
                refine ⟨8953712641298345915007377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5969141760865563943338251 8953712641298345915007377)
                ·
                  refine ⟨6715284480973759436255533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8953712641298345915007377 6715284480973759436255533)
                  ·
                    refine ⟨2518231680365159788595825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6715284480973759436255533 2518231680365159788595825)
                    ·
                      refine ⟨1888673760273869841446869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2518231680365159788595825 1888673760273869841446869)
                      ·
                        rfl

theorem cell23_3678179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 1, 1, 2, 3, 2].length) (baseStart_3678179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3678179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3678179 prefixEnd_3678179 := by exact prefixLift 3678179
  have htrace : WordTrace (prefixWord ++ tailWord_3678179) baseStart_3678179 baseEnd_3678179 := by
    simpa [prefixWord, tailWord_3678179, baseEnd_3678179] using wordTrace_append hprefix tailTrace_3678179
  have hstable : (prefixWord ++ tailWord_3678179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3678179).length < 2 ^ (prefixWord ++ tailWord_3678179).sum := by decide
  have hdescent : baseEnd_3678179 < baseStart_3678179 := by decide
  rcases family_descends (prefixWord ++ tailWord_3678179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
