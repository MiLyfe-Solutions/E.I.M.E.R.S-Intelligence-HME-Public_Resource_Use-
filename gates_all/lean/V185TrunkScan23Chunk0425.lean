import V185TrunkScan23Chunk0424

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2512544 : List Nat := [2, 1, 1, 4, 3, 2, 3, 1, 2, 2, 2]
def baseStart_2512544 : Nat := 118140960795 + 2512544 * 2 ^ 59
def prefixEnd_2512544 : Nat := 4983230072969 + 3 ^ 40 * 2512544 * 2
def baseEnd_2512544 : Nat := 1290142737570322893745027

theorem tailTrace_2512544 : CollatzResearch.WordTrace tailWord_2512544 prefixEnd_2512544 1290142737570322893745027 := by
  unfold tailWord_2512544
  simp only [CollatzResearch.WordTrace]
  refine ⟨45820004104744835598624343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61093338806326447464832457 45820004104744835598624343)
  ·
    refine ⟨68730006157117253397936515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45820004104744835598624343 68730006157117253397936515)
    ·
      refine ⟨103095009235675880096904773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68730006157117253397936515 103095009235675880096904773)
      ·
        refine ⟨19330314231689227518169645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 103095009235675880096904773 19330314231689227518169645)
        ·
          refine ⟨7248867836883460319313617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19330314231689227518169645 7248867836883460319313617)
          ·
            refine ⟨5436650877662595239485213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7248867836883460319313617 5436650877662595239485213)
            ·
              refine ⟨2038744079123473214806955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5436650877662595239485213 2038744079123473214806955)
              ·
                refine ⟨3058116118685209822210433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2038744079123473214806955 3058116118685209822210433)
                ·
                  refine ⟨2293587089013907366657825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3058116118685209822210433 2293587089013907366657825)
                  ·
                    refine ⟨1720190316760430524993369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2293587089013907366657825 1720190316760430524993369)
                    ·
                      refine ⟨1290142737570322893745027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1720190316760430524993369 1290142737570322893745027)
                      ·
                        rfl

theorem cell23_2512544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 3, 1, 2, 2, 2].length) (baseStart_2512544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2512544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2512544 prefixEnd_2512544 := by exact prefixLift 2512544
  have htrace : WordTrace (prefixWord ++ tailWord_2512544) baseStart_2512544 baseEnd_2512544 := by
    simpa [prefixWord, tailWord_2512544, baseEnd_2512544] using wordTrace_append hprefix tailTrace_2512544
  have hstable : (prefixWord ++ tailWord_2512544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2512544).length < 2 ^ (prefixWord ++ tailWord_2512544).sum := by decide
  have hdescent : baseEnd_2512544 < baseStart_2512544 := by decide
  rcases family_descends (prefixWord ++ tailWord_2512544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2512583 : List Nat := [1, 1, 4, 1, 1, 1, 5, 2, 2, 1, 4]
def baseStart_2512583 : Nat := 118140960795 + 2512583 * 2 ^ 59
def prefixEnd_2512583 : Nat := 4983230072969 + 3 ^ 40 * 2512583 * 2
def baseEnd_2512583 : Nat := 1290162763315848241157347

theorem tailTrace_2512583 : CollatzResearch.WordTrace tailWord_2512583 prefixEnd_2512583 1290162763315848241157347 := by
  unfold tailWord_2512583
  simp only [CollatzResearch.WordTrace]
  refine ⟨91641430656348380857918403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61094287104232253905278935 91641430656348380857918403)
  ·
    refine ⟨137462145984522571286877605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91641430656348380857918403 137462145984522571286877605)
    ·
      refine ⟨25774152372097982116289551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 137462145984522571286877605 25774152372097982116289551)
      ·
        refine ⟨38661228558146973174434327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25774152372097982116289551 38661228558146973174434327)
        ·
          refine ⟨57991842837220459761651491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38661228558146973174434327 57991842837220459761651491)
          ·
            refine ⟨86987764255830689642477237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57991842837220459761651491 86987764255830689642477237)
            ·
              refine ⟨8155102898984127153982241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 86987764255830689642477237 8155102898984127153982241)
              ·
                refine ⟨6116327174238095365486681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8155102898984127153982241 6116327174238095365486681)
                ·
                  refine ⟨4587245380678571524115011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6116327174238095365486681 4587245380678571524115011)
                  ·
                    refine ⟨6880868071017857286172517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4587245380678571524115011 6880868071017857286172517)
                    ·
                      refine ⟨1290162763315848241157347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6880868071017857286172517 1290162763315848241157347)
                      ·
                        rfl

theorem cell23_2512583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 2, 2, 1, 4].length) (baseStart_2512583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2512583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2512583 prefixEnd_2512583 := by exact prefixLift 2512583
  have htrace : WordTrace (prefixWord ++ tailWord_2512583) baseStart_2512583 baseEnd_2512583 := by
    simpa [prefixWord, tailWord_2512583, baseEnd_2512583] using wordTrace_append hprefix tailTrace_2512583
  have hstable : (prefixWord ++ tailWord_2512583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2512583).length < 2 ^ (prefixWord ++ tailWord_2512583).sum := by decide
  have hdescent : baseEnd_2512583 < baseStart_2512583 := by decide
  rcases family_descends (prefixWord ++ tailWord_2512583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2512644 : List Nat := [2, 3, 2, 2, 1, 2, 4, 2, 1, 4]
def baseStart_2512644 : Nat := 118140960795 + 2512644 * 2 ^ 59
def prefixEnd_2512644 : Nat := 4983230072969 + 3 ^ 40 * 2512644 * 2
def baseEnd_2512644 : Nat := 430064695211924167498189

theorem tailTrace_2512644 : CollatzResearch.WordTrace tailWord_2512644 prefixEnd_2512644 430064695211924167498189 := by
  unfold tailWord_2512644
  simp only [CollatzResearch.WordTrace]
  refine ⟨45821827754563694137944493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61095770339418258850592657 45821827754563694137944493)
  ·
    refine ⟨17183185407961385301729185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45821827754563694137944493 17183185407961385301729185)
    ·
      refine ⟨12887389055971038976296889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17183185407961385301729185 12887389055971038976296889)
      ·
        refine ⟨9665541791978279232222667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12887389055971038976296889 9665541791978279232222667)
        ·
          refine ⟨14498312687967418848334001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9665541791978279232222667 14498312687967418848334001)
          ·
            refine ⟨10873734515975564136250501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14498312687967418848334001 10873734515975564136250501)
            ·
              refine ⟨2038825221745418275546969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10873734515975564136250501 2038825221745418275546969)
              ·
                refine ⟨1529118916309063706660227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2038825221745418275546969 1529118916309063706660227)
                ·
                  refine ⟨2293678374463595559990341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1529118916309063706660227 2293678374463595559990341)
                  ·
                    refine ⟨430064695211924167498189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2293678374463595559990341 430064695211924167498189)
                    ·
                      rfl

theorem cell23_2512644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 4, 2, 1, 4].length) (baseStart_2512644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2512644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2512644 prefixEnd_2512644 := by exact prefixLift 2512644
  have htrace : WordTrace (prefixWord ++ tailWord_2512644) baseStart_2512644 baseEnd_2512644 := by
    simpa [prefixWord, tailWord_2512644, baseEnd_2512644] using wordTrace_append hprefix tailTrace_2512644
  have hstable : (prefixWord ++ tailWord_2512644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2512644).length < 2 ^ (prefixWord ++ tailWord_2512644).sum := by decide
  have hdescent : baseEnd_2512644 < baseStart_2512644 := by decide
  rcases family_descends (prefixWord ++ tailWord_2512644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2512677 : List Nat := [1, 3, 1, 2, 3, 2, 3, 1, 2, 3, 2]
def baseStart_2512677 : Nat := 118140960795 + 2512677 * 2 ^ 59
def prefixEnd_2512677 : Nat := 4983230072969 + 3 ^ 40 * 2512677 * 2
def baseEnd_2512677 : Nat := 1290211030497370873381915

theorem tailTrace_2512677 : CollatzResearch.WordTrace tailWord_2512677 prefixEnd_2512677 1290211030497370873381915 := by
  unfold tailWord_2512677
  simp only [CollatzResearch.WordTrace]
  refine ⟨91644859118007834911840285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61096572745338556607893523 91644859118007834911840285)
  ·
    refine ⟨34366822169252938091940107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91644859118007834911840285 34366822169252938091940107)
    ·
      refine ⟨51550233253879407137910161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34366822169252938091940107 51550233253879407137910161)
      ·
        refine ⟨38662674940409555353432621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51550233253879407137910161 38662674940409555353432621)
        ·
          refine ⟨14498503102653583257537233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38662674940409555353432621 14498503102653583257537233)
          ·
            refine ⟨10873877326990187443152925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14498503102653583257537233 10873877326990187443152925)
            ·
              refine ⟨4077703997621320291182347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10873877326990187443152925 4077703997621320291182347)
              ·
                refine ⟨6116555996431980436773521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4077703997621320291182347 6116555996431980436773521)
                ·
                  refine ⟨4587416997323985327580141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6116555996431980436773521 4587416997323985327580141)
                  ·
                    refine ⟨1720281373996494497842553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4587416997323985327580141 1720281373996494497842553)
                    ·
                      refine ⟨1290211030497370873381915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1720281373996494497842553 1290211030497370873381915)
                      ·
                        rfl

theorem cell23_2512677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 3, 1, 2, 3, 2].length) (baseStart_2512677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2512677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2512677 prefixEnd_2512677 := by exact prefixLift 2512677
  have htrace : WordTrace (prefixWord ++ tailWord_2512677) baseStart_2512677 baseEnd_2512677 := by
    simpa [prefixWord, tailWord_2512677, baseEnd_2512677] using wordTrace_append hprefix tailTrace_2512677
  have hstable : (prefixWord ++ tailWord_2512677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2512677).length < 2 ^ (prefixWord ++ tailWord_2512677).sum := by decide
  have hdescent : baseEnd_2512677 < baseStart_2512677 := by decide
  rcases family_descends (prefixWord ++ tailWord_2512677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2512684 : List Nat := [2, 2, 1, 1, 1, 6, 2, 3, 1, 1, 3]
def baseStart_2512684 : Nat := 118140960795 + 2512684 * 2 ^ 59
def prefixEnd_2512684 : Nat := 4983230072969 + 3 ^ 40 * 2512684 * 2
def baseEnd_2512684 : Nat := 1290214624861952345994383

theorem tailTrace_2512684 : CollatzResearch.WordTrace tailWord_2512684 prefixEnd_2512684 1290214624861952345994383 := by
  unfold tailWord_2512684
  simp only [CollatzResearch.WordTrace]
  refine ⟨45822557214491237553672553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61096742952654983404896737 45822557214491237553672553)
  ·
    refine ⟨34366917910868428165254415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45822557214491237553672553 34366917910868428165254415)
    ·
      refine ⟨51550376866302642247881623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34366917910868428165254415 51550376866302642247881623)
      ·
        refine ⟨77325565299453963371822435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51550376866302642247881623 77325565299453963371822435)
        ·
          refine ⟨115988347949180945057733653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77325565299453963371822435 115988347949180945057733653)
          ·
            refine ⟨5436953810117856799581265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 115988347949180945057733653 5436953810117856799581265)
            ·
              refine ⟨4077715357588392599685949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5436953810117856799581265 4077715357588392599685949)
              ·
                refine ⟨1529143259095647224882231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4077715357588392599685949 1529143259095647224882231)
                ·
                  refine ⟨2293714888643470837323347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1529143259095647224882231 2293714888643470837323347)
                  ·
                    refine ⟨3440572332965206255985021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2293714888643470837323347 3440572332965206255985021)
                    ·
                      refine ⟨1290214624861952345994383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3440572332965206255985021 1290214624861952345994383)
                      ·
                        rfl

theorem cell23_2512684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 2, 3, 1, 1, 3].length) (baseStart_2512684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2512684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2512684 prefixEnd_2512684 := by exact prefixLift 2512684
  have htrace : WordTrace (prefixWord ++ tailWord_2512684) baseStart_2512684 baseEnd_2512684 := by
    simpa [prefixWord, tailWord_2512684, baseEnd_2512684] using wordTrace_append hprefix tailTrace_2512684
  have hstable : (prefixWord ++ tailWord_2512684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2512684).length < 2 ^ (prefixWord ++ tailWord_2512684).sum := by decide
  have hdescent : baseEnd_2512684 < baseStart_2512684 := by decide
  rcases family_descends (prefixWord ++ tailWord_2512684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2512707 : List Nat := [1, 1, 1, 3, 1, 5, 1, 3, 3, 2, 2]
def baseStart_2512707 : Nat := 118140960795 + 2512707 * 2 ^ 59
def prefixEnd_2512707 : Nat := 4983230072969 + 3 ^ 40 * 2512707 * 2
def baseEnd_2512707 : Nat := 1290226434917005756006777

theorem tailTrace_2512707 : CollatzResearch.WordTrace tailWord_2512707 prefixEnd_2512707 1290226434917005756006777 := by
  unfold tailWord_2512707
  simp only [CollatzResearch.WordTrace]
  refine ⟨91645953307899150035432375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61097302205266100023621583 91645953307899150035432375)
  ·
    refine ⟨137468929961848725053148563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91645953307899150035432375 137468929961848725053148563)
    ·
      refine ⟨206203394942773087579722845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137468929961848725053148563 206203394942773087579722845)
      ·
        refine ⟨77326273103539907842396067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 206203394942773087579722845 77326273103539907842396067)
        ·
          refine ⟨115989409655309861763594101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77326273103539907842396067 115989409655309861763594101)
          ·
            refine ⟨10874007155185299540336947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 115989409655309861763594101 10874007155185299540336947)
            ·
              refine ⟨16311010732777949310505421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10874007155185299540336947 16311010732777949310505421)
              ·
                refine ⟨6116629024791730991439533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16311010732777949310505421 6116629024791730991439533)
                ·
                  refine ⟨2293735884296899121789825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6116629024791730991439533 2293735884296899121789825)
                  ·
                    refine ⟨1720301913222674341342369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2293735884296899121789825 1720301913222674341342369)
                    ·
                      refine ⟨1290226434917005756006777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1720301913222674341342369 1290226434917005756006777)
                      ·
                        rfl

theorem cell23_2512707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 3, 3, 2, 2].length) (baseStart_2512707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2512707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2512707 prefixEnd_2512707 := by exact prefixLift 2512707
  have htrace : WordTrace (prefixWord ++ tailWord_2512707) baseStart_2512707 baseEnd_2512707 := by
    simpa [prefixWord, tailWord_2512707, baseEnd_2512707] using wordTrace_append hprefix tailTrace_2512707
  have hstable : (prefixWord ++ tailWord_2512707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2512707).length < 2 ^ (prefixWord ++ tailWord_2512707).sum := by decide
  have hdescent : baseEnd_2512707 < baseStart_2512707 := by decide
  rcases family_descends (prefixWord ++ tailWord_2512707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2512717 : List Nat := [1, 6, 1, 2, 1, 1, 3, 1, 1, 6]
def baseStart_2512717 : Nat := 118140960795 + 2512717 * 2 ^ 59
def prefixEnd_2512717 : Nat := 4983230072969 + 3 ^ 40 * 2512717 * 2
def baseEnd_2512717 : Nat := 430077189907850238960577

theorem tailTrace_2512717 : CollatzResearch.WordTrace tailWord_2512717 prefixEnd_2512717 430077189907850238960577 := by
  unfold tailWord_2512717
  simp only [CollatzResearch.WordTrace]
  refine ⟨91646318037862921743296405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61097545358575281162197603 91646318037862921743296405)
  ·
    refine ⟨4295921158024824456717019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 91646318037862921743296405 4295921158024824456717019)
    ·
      refine ⟨6443881737037236685075529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4295921158024824456717019 6443881737037236685075529)
      ·
        refine ⟨4832911302777927513806647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6443881737037236685075529 4832911302777927513806647)
        ·
          refine ⟨7249366954166891270709971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4832911302777927513806647 7249366954166891270709971)
          ·
            refine ⟨10874050431250336906064957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7249366954166891270709971 10874050431250336906064957)
            ·
              refine ⟨4077768911718876339774359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10874050431250336906064957 4077768911718876339774359)
              ·
                refine ⟨6116653367578314509661539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4077768911718876339774359 6116653367578314509661539)
                ·
                  refine ⟨9174980051367471764492309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6116653367578314509661539 9174980051367471764492309)
                  ·
                    refine ⟨430077189907850238960577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9174980051367471764492309 430077189907850238960577)
                    ·
                      rfl

theorem cell23_2512717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 3, 1, 1, 6].length) (baseStart_2512717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2512717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2512717 prefixEnd_2512717 := by exact prefixLift 2512717
  have htrace : WordTrace (prefixWord ++ tailWord_2512717) baseStart_2512717 baseEnd_2512717 := by
    simpa [prefixWord, tailWord_2512717, baseEnd_2512717] using wordTrace_append hprefix tailTrace_2512717
  have hstable : (prefixWord ++ tailWord_2512717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2512717).length < 2 ^ (prefixWord ++ tailWord_2512717).sum := by decide
  have hdescent : baseEnd_2512717 < baseStart_2512717 := by decide
  rcases family_descends (prefixWord ++ tailWord_2512717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2512724 : List Nat := [2, 4, 1, 1, 3, 1, 2, 2, 3, 2, 2]
def baseStart_2512724 : Nat := 118140960795 + 2512724 * 2 ^ 59
def prefixEnd_2512724 : Nat := 4983230072969 + 3 ^ 40 * 2512724 * 2
def baseEnd_2512724 : Nat := 1290235164088132189494199

theorem tailTrace_2512724 : CollatzResearch.WordTrace tailWord_2512724 prefixEnd_2512724 1290235164088132189494199 := by
  unfold tailWord_2512724
  simp only [CollatzResearch.WordTrace]
  refine ⟨45823286674418780969400613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61097715565891707959200817 45823286674418780969400613)
  ·
    refine ⟨8591866251453521431762615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45823286674418780969400613 8591866251453521431762615)
    ·
      refine ⟨12887799377180282147643923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8591866251453521431762615 12887799377180282147643923)
      ·
        refine ⟨19331699065770423221465885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12887799377180282147643923 19331699065770423221465885)
        ·
          refine ⟨7249387149663908708049707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19331699065770423221465885 7249387149663908708049707)
          ·
            refine ⟨10874080724495863062074561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7249387149663908708049707 10874080724495863062074561)
            ·
              refine ⟨8155560543371897296555921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10874080724495863062074561 8155560543371897296555921)
              ·
                refine ⟨6116670407528922972416941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8155560543371897296555921 6116670407528922972416941)
                ·
                  refine ⟨2293751402823346114656353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6116670407528922972416941 2293751402823346114656353)
                  ·
                    refine ⟨1720313552117509585992265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2293751402823346114656353 1720313552117509585992265)
                    ·
                      refine ⟨1290235164088132189494199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1720313552117509585992265 1290235164088132189494199)
                      ·
                        rfl

theorem cell23_2512724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 2, 3, 2, 2].length) (baseStart_2512724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2512724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2512724 prefixEnd_2512724 := by exact prefixLift 2512724
  have htrace : WordTrace (prefixWord ++ tailWord_2512724) baseStart_2512724 baseEnd_2512724 := by
    simpa [prefixWord, tailWord_2512724, baseEnd_2512724] using wordTrace_append hprefix tailTrace_2512724
  have hstable : (prefixWord ++ tailWord_2512724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2512724).length < 2 ^ (prefixWord ++ tailWord_2512724).sum := by decide
  have hdescent : baseEnd_2512724 < baseStart_2512724 := by decide
  rcases family_descends (prefixWord ++ tailWord_2512724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2512753 : List Nat := [1, 2, 2, 2, 1, 3, 1, 2, 2, 2, 5]
def baseStart_2512753 : Nat := 118140960795 + 2512753 * 2 ^ 59
def prefixEnd_2512753 : Nat := 4983230072969 + 3 ^ 40 * 2512753 * 2
def baseEnd_2512753 : Nat := 1290250055027112576031565

theorem tailTrace_2512753 : CollatzResearch.WordTrace tailWord_2512753 prefixEnd_2512753 1290250055027112576031565 := by
  unfold tailWord_2512753
  simp only [CollatzResearch.WordTrace]
  refine ⟨91647631065732499891606913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61098420710488333261071275 91647631065732499891606913)
  ·
    refine ⟨68735723299299374918705185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91647631065732499891606913 68735723299299374918705185)
    ·
      refine ⟨51551792474474531189028889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68735723299299374918705185 51551792474474531189028889)
      ·
        refine ⟨38663844355855898391771667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51551792474474531189028889 38663844355855898391771667)
        ·
          refine ⟨57995766533783847587657501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38663844355855898391771667 57995766533783847587657501)
          ·
            refine ⟨21748412450168942845371563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57995766533783847587657501 21748412450168942845371563)
            ·
              refine ⟨32622618675253414268057345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21748412450168942845371563 32622618675253414268057345)
              ·
                refine ⟨24466964006440060701043009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32622618675253414268057345 24466964006440060701043009)
                ·
                  refine ⟨18350223004830045525782257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24466964006440060701043009 18350223004830045525782257)
                  ·
                    refine ⟨13762667253622534144336693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18350223004830045525782257 13762667253622534144336693)
                    ·
                      refine ⟨1290250055027112576031565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13762667253622534144336693 1290250055027112576031565)
                      ·
                        rfl

theorem cell23_2512753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 2, 2, 2, 5].length) (baseStart_2512753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2512753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2512753 prefixEnd_2512753 := by exact prefixLift 2512753
  have htrace : WordTrace (prefixWord ++ tailWord_2512753) baseStart_2512753 baseEnd_2512753 := by
    simpa [prefixWord, tailWord_2512753, baseEnd_2512753] using wordTrace_append hprefix tailTrace_2512753
  have hstable : (prefixWord ++ tailWord_2512753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2512753).length < 2 ^ (prefixWord ++ tailWord_2512753).sum := by decide
  have hdescent : baseEnd_2512753 < baseStart_2512753 := by decide
  rcases family_descends (prefixWord ++ tailWord_2512753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2512757 : List Nat := [1, 3, 4, 1, 1, 1, 1, 3, 4, 1, 3]
def baseStart_2512757 : Nat := 118140960795 + 2512757 * 2 ^ 59
def prefixEnd_2512757 : Nat := 4983230072969 + 3 ^ 40 * 2512757 * 2
def baseEnd_2512757 : Nat := 1290252108949730560381547

theorem tailTrace_2512757 : CollatzResearch.WordTrace tailWord_2512757 prefixEnd_2512757 1290252108949730560381547 := by
  unfold tailWord_2512757
  simp only [CollatzResearch.WordTrace]
  refine ⟨91647776957718008574752525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61098517971812005716501683 91647776957718008574752525)
  ·
    refine ⟨34367916359144253215532197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91647776957718008574752525 34367916359144253215532197)
    ·
      refine ⟨6443984317339547477912287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34367916359144253215532197 6443984317339547477912287)
      ·
        refine ⟨9665976476009321216868431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6443984317339547477912287 9665976476009321216868431)
        ·
          refine ⟨14498964714013981825302647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9665976476009321216868431 14498964714013981825302647)
          ·
            refine ⟨21748447071020972737953971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14498964714013981825302647 21748447071020972737953971)
            ·
              refine ⟨32622670606531459106930957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21748447071020972737953971 32622670606531459106930957)
              ·
                refine ⟨12233501477449297165099109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32622670606531459106930957 12233501477449297165099109)
                ·
                  refine ⟨2293781527021743218456083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12233501477449297165099109 2293781527021743218456083)
                  ·
                    refine ⟨3440672290532614827684125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2293781527021743218456083 3440672290532614827684125)
                    ·
                      refine ⟨1290252108949730560381547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3440672290532614827684125 1290252108949730560381547)
                      ·
                        rfl

theorem cell23_2512757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 3, 4, 1, 3].length) (baseStart_2512757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2512757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2512757 prefixEnd_2512757 := by exact prefixLift 2512757
  have htrace : WordTrace (prefixWord ++ tailWord_2512757) baseStart_2512757 baseEnd_2512757 := by
    simpa [prefixWord, tailWord_2512757, baseEnd_2512757] using wordTrace_append hprefix tailTrace_2512757
  have hstable : (prefixWord ++ tailWord_2512757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2512757).length < 2 ^ (prefixWord ++ tailWord_2512757).sum := by decide
  have hdescent : baseEnd_2512757 < baseStart_2512757 := by decide
  rcases family_descends (prefixWord ++ tailWord_2512757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2512758 : List Nat := [5, 1, 1, 3, 2, 2, 1, 1, 3, 2, 2]
def baseStart_2512758 : Nat := 118140960795 + 2512758 * 2 ^ 59
def prefixEnd_2512758 : Nat := 4983230072969 + 3 ^ 40 * 2512758 * 2
def baseEnd_2512758 : Nat := 1290252622430385056469043

theorem tailTrace_2512758 : CollatzResearch.WordTrace tailWord_2512758 prefixEnd_2512758 1290252622430385056469043 := by
  unfold tailWord_2512758
  simp only [CollatzResearch.WordTrace]
  refine ⟨5727988339419649109096183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 61098542287142923830359285 5727988339419649109096183)
  ·
    refine ⟨8591982509129473663644275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5727988339419649109096183 8591982509129473663644275)
    ·
      refine ⟨12887973763694210495466413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8591982509129473663644275 12887973763694210495466413)
      ·
        refine ⟨4832990161385328935799905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12887973763694210495466413 4832990161385328935799905)
        ·
          refine ⟨3624742621038996701849929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4832990161385328935799905 3624742621038996701849929)
          ·
            refine ⟨2718556965779247526387447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3624742621038996701849929 2718556965779247526387447)
            ·
              refine ⟨4077835448668871289581171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2718556965779247526387447 4077835448668871289581171)
              ·
                refine ⟨6116753173003306934371757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4077835448668871289581171 6116753173003306934371757)
                ·
                  refine ⟨2293782439876240100389409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6116753173003306934371757 2293782439876240100389409)
                  ·
                    refine ⟨1720336829907180075292057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2293782439876240100389409 1720336829907180075292057)
                    ·
                      refine ⟨1290252622430385056469043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1720336829907180075292057 1290252622430385056469043)
                      ·
                        rfl

theorem cell23_2512758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 1, 1, 3, 2, 2].length) (baseStart_2512758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2512758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2512758 prefixEnd_2512758 := by exact prefixLift 2512758
  have htrace : WordTrace (prefixWord ++ tailWord_2512758) baseStart_2512758 baseEnd_2512758 := by
    simpa [prefixWord, tailWord_2512758, baseEnd_2512758] using wordTrace_append hprefix tailTrace_2512758
  have hstable : (prefixWord ++ tailWord_2512758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2512758).length < 2 ^ (prefixWord ++ tailWord_2512758).sum := by decide
  have hdescent : baseEnd_2512758 < baseStart_2512758 := by decide
  rcases family_descends (prefixWord ++ tailWord_2512758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2512763 : List Nat := [1, 1, 1, 1, 1, 5, 1, 3, 2, 3, 4]
def baseStart_2512763 : Nat := 118140960795 + 2512763 * 2 ^ 59
def prefixEnd_2512763 : Nat := 4983230072969 + 3 ^ 40 * 2512763 * 2
def baseEnd_2512763 : Nat := 1290255189833657536906519

theorem tailTrace_2512763 : CollatzResearch.WordTrace tailWord_2512763 prefixEnd_2512763 1290255189833657536906519 := by
  unfold tailWord_2512763
  simp only [CollatzResearch.WordTrace]
  refine ⟨91647995795696271599470943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61098663863797514399647295 91647995795696271599470943)
  ·
    refine ⟨137471993693544407399206415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91647995795696271599470943 137471993693544407399206415)
    ·
      refine ⟨206207990540316611098809623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137471993693544407399206415 206207990540316611098809623)
      ·
        refine ⟨309311985810474916648214435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206207990540316611098809623 309311985810474916648214435)
        ·
          refine ⟨463967978715712374972321653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 309311985810474916648214435 463967978715712374972321653)
          ·
            refine ⟨43496998004598035153655155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 463967978715712374972321653 43496998004598035153655155)
            ·
              refine ⟨65245497006897052730482733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43496998004598035153655155 65245497006897052730482733)
              ·
                refine ⟨24467061377586394773931025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65245497006897052730482733 24467061377586394773931025)
                ·
                  refine ⟨18350296033189796080448269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24467061377586394773931025 18350296033189796080448269)
                  ·
                    refine ⟨6881361012446173530168101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18350296033189796080448269 6881361012446173530168101)
                    ·
                      refine ⟨1290255189833657536906519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6881361012446173530168101 1290255189833657536906519)
                      ·
                        rfl

theorem cell23_2512763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 3, 2, 3, 4].length) (baseStart_2512763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2512763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2512763 prefixEnd_2512763 := by exact prefixLift 2512763
  have htrace : WordTrace (prefixWord ++ tailWord_2512763) baseStart_2512763 baseEnd_2512763 := by
    simpa [prefixWord, tailWord_2512763, baseEnd_2512763] using wordTrace_append hprefix tailTrace_2512763
  have hstable : (prefixWord ++ tailWord_2512763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2512763).length < 2 ^ (prefixWord ++ tailWord_2512763).sum := by decide
  have hdescent : baseEnd_2512763 < baseStart_2512763 := by decide
  rcases family_descends (prefixWord ++ tailWord_2512763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2512773 : List Nat := [1, 3, 1, 1, 3, 2, 2, 1, 1, 8]
def baseStart_2512773 : Nat := 118140960795 + 2512773 * 2 ^ 59
def prefixEnd_2512773 : Nat := 4983230072969 + 3 ^ 40 * 2512773 * 2
def baseEnd_2512773 : Nat := 430086774880067499260491

theorem tailTrace_2512773 : CollatzResearch.WordTrace tailWord_2512773 prefixEnd_2512773 430086774880067499260491 := by
  unfold tailWord_2512773
  simp only [CollatzResearch.WordTrace]
  refine ⟨91648360525660043307334973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61098907017106695538223315 91648360525660043307334973)
  ·
    refine ⟨34368135197122516240250615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91648360525660043307334973 34368135197122516240250615)
    ·
      refine ⟨51552202795683774360375923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34368135197122516240250615 51552202795683774360375923)
      ·
        refine ⟨77328304193525661540563885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51552202795683774360375923 77328304193525661540563885)
        ·
          refine ⟨28998114072572123077711457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77328304193525661540563885 28998114072572123077711457)
          ·
            refine ⟨21748585554429092308283593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28998114072572123077711457 21748585554429092308283593)
            ·
              refine ⟨16311439165821819231212695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21748585554429092308283593 16311439165821819231212695)
              ·
                refine ⟨24467158748732728846819043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16311439165821819231212695 24467158748732728846819043)
                ·
                  refine ⟨36700738123099093270228565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24467158748732728846819043 36700738123099093270228565)
                  ·
                    refine ⟨430086774880067499260491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 36700738123099093270228565 430086774880067499260491)
                    ·
                      rfl

theorem cell23_2512773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 1, 1, 8].length) (baseStart_2512773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2512773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2512773 prefixEnd_2512773 := by exact prefixLift 2512773
  have htrace : WordTrace (prefixWord ++ tailWord_2512773) baseStart_2512773 baseEnd_2512773 := by
    simpa [prefixWord, tailWord_2512773, baseEnd_2512773] using wordTrace_append hprefix tailTrace_2512773
  have hstable : (prefixWord ++ tailWord_2512773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2512773).length < 2 ^ (prefixWord ++ tailWord_2512773).sum := by decide
  have hdescent : baseEnd_2512773 < baseStart_2512773 := by decide
  rcases family_descends (prefixWord ++ tailWord_2512773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2512797 : List Nat := [1, 4, 2, 1, 2, 2, 1, 1, 3, 4, 2]
def baseStart_2512797 : Nat := 118140960795 + 2512797 * 2 ^ 59
def prefixEnd_2512797 : Nat := 4983230072969 + 3 ^ 40 * 2512797 * 2
def baseEnd_2512797 : Nat := 1290272648175910403881363

theorem tailTrace_2512797 : CollatzResearch.WordTrace tailWord_2512797 prefixEnd_2512797 1290272648175910403881363 := by
  unfold tailWord_2512797
  simp only [CollatzResearch.WordTrace]
  refine ⟨91649235877573095406208645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61099490585048730270805763 91649235877573095406208645)
  ·
    refine ⟨17184231727044955388664121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 91649235877573095406208645 17184231727044955388664121)
    ·
      refine ⟨12888173795283716541498091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17184231727044955388664121 12888173795283716541498091)
      ·
        refine ⟨19332260692925574812247137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12888173795283716541498091 19332260692925574812247137)
        ·
          refine ⟨14499195519694181109185353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19332260692925574812247137 14499195519694181109185353)
          ·
            refine ⟨10874396639770635831889015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14499195519694181109185353 10874396639770635831889015)
            ·
              refine ⟨16311594959655953747833523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10874396639770635831889015 16311594959655953747833523)
              ·
                refine ⟨24467392439483930621750285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16311594959655953747833523 24467392439483930621750285)
                ·
                  refine ⟨9175272164806473983156357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24467392439483930621750285 9175272164806473983156357)
                  ·
                    refine ⟨1720363530901213871841817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9175272164806473983156357 1720363530901213871841817)
                    ·
                      refine ⟨1290272648175910403881363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1720363530901213871841817 1290272648175910403881363)
                      ·
                        rfl

theorem cell23_2512797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 1, 3, 4, 2].length) (baseStart_2512797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2512797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2512797 prefixEnd_2512797 := by exact prefixLift 2512797
  have htrace : WordTrace (prefixWord ++ tailWord_2512797) baseStart_2512797 baseEnd_2512797 := by
    simpa [prefixWord, tailWord_2512797, baseEnd_2512797] using wordTrace_append hprefix tailTrace_2512797
  have hstable : (prefixWord ++ tailWord_2512797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2512797).length < 2 ^ (prefixWord ++ tailWord_2512797).sum := by decide
  have hdescent : baseEnd_2512797 < baseStart_2512797 := by decide
  rcases family_descends (prefixWord ++ tailWord_2512797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2512808 : List Nat := [2, 1, 6, 2, 1, 1, 2, 2, 2, 1, 3]
def baseStart_2512808 : Nat := 118140960795 + 2512808 * 2 ^ 59
def prefixEnd_2512808 : Nat := 4983230072969 + 3 ^ 40 * 2512808 * 2
def baseEnd_2512808 : Nat := 1290278296463109860843813

theorem tailTrace_2512808 : CollatzResearch.WordTrace tailWord_2512808 prefixEnd_2512808 1290278296463109860843813 := by
  unfold tailWord_2512808
  simp only [CollatzResearch.WordTrace]
  refine ⟨45824818540266622142429539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61099758053688829523239385 45824818540266622142429539)
  ·
    refine ⟨68737227810399933213644309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45824818540266622142429539 68737227810399933213644309)
    ·
      refine ⟨3222057553612496869389577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 68737227810399933213644309 3222057553612496869389577)
      ·
        refine ⟨2416543165209372652042183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3222057553612496869389577 2416543165209372652042183)
        ·
          refine ⟨3624814747814058978063275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2416543165209372652042183 3624814747814058978063275)
          ·
            refine ⟨5437222121721088467094913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3624814747814058978063275 5437222121721088467094913)
            ·
              refine ⟨4077916591290816350321185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5437222121721088467094913 4077916591290816350321185)
              ·
                refine ⟨3058437443468112262740889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4077916591290816350321185 3058437443468112262740889)
                ·
                  refine ⟨2293828082601084197055667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3058437443468112262740889 2293828082601084197055667)
                  ·
                    refine ⟨3440742123901626295583501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2293828082601084197055667 3440742123901626295583501)
                    ·
                      refine ⟨1290278296463109860843813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3440742123901626295583501 1290278296463109860843813)
                      ·
                        rfl

theorem cell23_2512808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_2512808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2512808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2512808 prefixEnd_2512808 := by exact prefixLift 2512808
  have htrace : WordTrace (prefixWord ++ tailWord_2512808) baseStart_2512808 baseEnd_2512808 := by
    simpa [prefixWord, tailWord_2512808, baseEnd_2512808] using wordTrace_append hprefix tailTrace_2512808
  have hstable : (prefixWord ++ tailWord_2512808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2512808).length < 2 ^ (prefixWord ++ tailWord_2512808).sum := by decide
  have hdescent : baseEnd_2512808 < baseStart_2512808 := by decide
  rcases family_descends (prefixWord ++ tailWord_2512808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2512823 : List Nat := [1, 1, 3, 1, 3, 1, 1, 1, 2, 1, 8]
def baseStart_2512823 : Nat := 118140960795 + 2512823 * 2 ^ 59
def prefixEnd_2512823 : Nat := 4983230072969 + 3 ^ 40 * 2512823 * 2
def baseEnd_2512823 : Nat := 1290285998672927302156243

theorem tailTrace_2512823 : CollatzResearch.WordTrace tailWord_2512823 prefixEnd_2512823 1290285998672927302156243 := by
  unfold tailWord_2512823
  simp only [CollatzResearch.WordTrace]
  refine ⟨91650184175478901846655123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61100122783652601231103415 91650184175478901846655123)
  ·
    refine ⟨137475276263218352769982685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91650184175478901846655123 137475276263218352769982685)
    ·
      refine ⟨51553228598706882288743507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137475276263218352769982685 51553228598706882288743507)
      ·
        refine ⟨77329842898060323433115261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51553228598706882288743507 77329842898060323433115261)
        ·
          refine ⟨28998691086772621287418223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77329842898060323433115261 28998691086772621287418223)
          ·
            refine ⟨43498036630158931931127335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28998691086772621287418223 43498036630158931931127335)
            ·
              refine ⟨65247054945238397896691003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43498036630158931931127335 65247054945238397896691003)
              ·
                refine ⟨97870582417857596845036505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65247054945238397896691003 97870582417857596845036505)
                ·
                  refine ⟨73402936813393197633777379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 97870582417857596845036505 73402936813393197633777379)
                  ·
                    refine ⟨110104405220089796450666069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 73402936813393197633777379 110104405220089796450666069)
                    ·
                      refine ⟨1290285998672927302156243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 110104405220089796450666069 1290285998672927302156243)
                      ·
                        rfl

theorem cell23_2512823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 2, 1, 8].length) (baseStart_2512823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2512823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2512823 prefixEnd_2512823 := by exact prefixLift 2512823
  have htrace : WordTrace (prefixWord ++ tailWord_2512823) baseStart_2512823 baseEnd_2512823 := by
    simpa [prefixWord, tailWord_2512823, baseEnd_2512823] using wordTrace_append hprefix tailTrace_2512823
  have hstable : (prefixWord ++ tailWord_2512823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2512823).length < 2 ^ (prefixWord ++ tailWord_2512823).sum := by decide
  have hdescent : baseEnd_2512823 < baseStart_2512823 := by decide
  rcases family_descends (prefixWord ++ tailWord_2512823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2512897 : List Nat := [1, 2, 4, 1, 2, 1, 1, 4, 3, 4]
def baseStart_2512897 : Nat := 118140960795 + 2512897 * 2 ^ 59
def prefixEnd_2512897 : Nat := 4983230072969 + 3 ^ 40 * 2512897 * 2
def baseEnd_2512897 : Nat := 430107998747120004210301

theorem tailTrace_2512897 : CollatzResearch.WordTrace tailWord_2512897 prefixEnd_2512897 430107998747120004210301 := by
  unfold tailWord_2512897
  simp only [CollatzResearch.WordTrace]
  refine ⟨91652883177210812484848945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61101922118140541656565963 91652883177210812484848945)
  ·
    refine ⟨68739662382908109363636709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91652883177210812484848945 68739662382908109363636709)
    ·
      refine ⟨12888686696795270505681883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68739662382908109363636709 12888686696795270505681883)
      ·
        refine ⟨19333030045192905758522825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12888686696795270505681883 19333030045192905758522825)
        ·
          refine ⟨14499772533894679318892119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19333030045192905758522825 14499772533894679318892119)
          ·
            refine ⟨21749658800842018978338179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14499772533894679318892119 21749658800842018978338179)
            ·
              refine ⟨32624488201263028467507269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21749658800842018978338179 32624488201263028467507269)
              ·
                refine ⟨6117091537736817837657613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32624488201263028467507269 6117091537736817837657613)
                ·
                  refine ⟨2293909326651306689121605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6117091537736817837657613 2293909326651306689121605)
                  ·
                    refine ⟨430107998747120004210301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2293909326651306689121605 430107998747120004210301)
                    ·
                      rfl

theorem cell23_2512897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 4, 3, 4].length) (baseStart_2512897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2512897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2512897 prefixEnd_2512897 := by exact prefixLift 2512897
  have htrace : WordTrace (prefixWord ++ tailWord_2512897) baseStart_2512897 baseEnd_2512897 := by
    simpa [prefixWord, tailWord_2512897, baseEnd_2512897] using wordTrace_append hprefix tailTrace_2512897
  have hstable : (prefixWord ++ tailWord_2512897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2512897).length < 2 ^ (prefixWord ++ tailWord_2512897).sum := by decide
  have hdescent : baseEnd_2512897 < baseStart_2512897 := by decide
  rcases family_descends (prefixWord ++ tailWord_2512897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2512907 : List Nat := [1, 1, 1, 1, 6, 1, 2, 3, 2, 2, 3]
def baseStart_2512907 : Nat := 118140960795 + 2512907 * 2 ^ 59
def prefixEnd_2512907 : Nat := 4983230072969 + 3 ^ 40 * 2512907 * 2
def baseEnd_2512907 : Nat := 1290329131047904973505857

theorem tailTrace_2512907 : CollatzResearch.WordTrace tailWord_2512907 prefixEnd_2512907 1290329131047904973505857 := by
  unfold tailWord_2512907
  simp only [CollatzResearch.WordTrace]
  refine ⟨91653247907174584192712975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61102165271449722795141983 91653247907174584192712975)
  ·
    refine ⟨137479871860761876289069463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91653247907174584192712975 137479871860761876289069463)
    ·
      refine ⟨206219807791142814433604195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137479871860761876289069463 206219807791142814433604195)
      ·
        refine ⟨309329711686714221650406293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206219807791142814433604195 309329711686714221650406293)
        ·
          refine ⟨14499830235314729139862795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 309329711686714221650406293 14499830235314729139862795)
          ·
            refine ⟨21749745352972093709794193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14499830235314729139862795 21749745352972093709794193)
            ·
              refine ⟨16312309014729070282345645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21749745352972093709794193 16312309014729070282345645)
              ·
                refine ⟨6117115880523401355879617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16312309014729070282345645 6117115880523401355879617)
                ·
                  refine ⟨4587836910392551016909713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6117115880523401355879617 4587836910392551016909713)
                  ·
                    refine ⟨3440877682794413262682285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4587836910392551016909713 3440877682794413262682285)
                    ·
                      refine ⟨1290329131047904973505857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3440877682794413262682285 1290329131047904973505857)
                      ·
                        rfl

theorem cell23_2512907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 3, 2, 2, 3].length) (baseStart_2512907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2512907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2512907 prefixEnd_2512907 := by exact prefixLift 2512907
  have htrace : WordTrace (prefixWord ++ tailWord_2512907) baseStart_2512907 baseEnd_2512907 := by
    simpa [prefixWord, tailWord_2512907, baseEnd_2512907] using wordTrace_append hprefix tailTrace_2512907
  have hstable : (prefixWord ++ tailWord_2512907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2512907).length < 2 ^ (prefixWord ++ tailWord_2512907).sum := by decide
  have hdescent : baseEnd_2512907 < baseStart_2512907 := by decide
  rcases family_descends (prefixWord ++ tailWord_2512907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2512910 : List Nat := [4, 1, 1, 2, 2, 1, 1, 1, 10]
def baseStart_2512910 : Nat := 118140960795 + 2512910 * 2 ^ 59
def prefixEnd_2512910 : Nat := 4983230072969 + 3 ^ 40 * 2512910 * 2
def baseEnd_2512910 : Nat := 143370074609985384640927

theorem tailTrace_2512910 : CollatzResearch.WordTrace tailWord_2512910 prefixEnd_2512910 143370074609985384640927 := by
  unfold tailWord_2512910
  simp only [CollatzResearch.WordTrace]
  refine ⟨11456669665770464463134023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61102238217442477136714789 11456669665770464463134023)
  ·
    refine ⟨17185004498655696694701035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11456669665770464463134023 17185004498655696694701035)
    ·
      refine ⟨25777506747983545042051553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17185004498655696694701035 25777506747983545042051553)
      ·
        refine ⟨19333130060987658781538665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25777506747983545042051553 19333130060987658781538665)
        ·
          refine ⟨14499847545740744086153999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19333130060987658781538665 14499847545740744086153999)
          ·
            refine ⟨21749771318611116129230999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14499847545740744086153999 21749771318611116129230999)
            ·
              refine ⟨32624656977916674193846499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21749771318611116129230999 32624656977916674193846499)
              ·
                refine ⟨48936985466875011290769749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32624656977916674193846499 48936985466875011290769749)
                ·
                  refine ⟨143370074609985384640927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 48936985466875011290769749 143370074609985384640927)
                  ·
                    rfl

theorem cell23_2512910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 1, 10].length) (baseStart_2512910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2512910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2512910 prefixEnd_2512910 := by exact prefixLift 2512910
  have htrace : WordTrace (prefixWord ++ tailWord_2512910) baseStart_2512910 baseEnd_2512910 := by
    simpa [prefixWord, tailWord_2512910, baseEnd_2512910] using wordTrace_append hprefix tailTrace_2512910
  have hstable : (prefixWord ++ tailWord_2512910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2512910).length < 2 ^ (prefixWord ++ tailWord_2512910).sum := by decide
  have hdescent : baseEnd_2512910 < baseStart_2512910 := by decide
  rcases family_descends (prefixWord ++ tailWord_2512910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2512924 : List Nat := [2, 2, 3, 1, 3, 2, 1, 2, 2, 2, 3]
def baseStart_2512924 : Nat := 118140960795 + 2512924 * 2 ^ 59
def prefixEnd_2512924 : Nat := 4983230072969 + 3 ^ 40 * 2512924 * 2
def baseEnd_2512924 : Nat := 1290337860219031406993279

theorem tailTrace_2512924 : CollatzResearch.WordTrace tailWord_2512924 prefixEnd_2512924 1290337860219031406993279 := by
  unfold tailWord_2512924
  simp only [CollatzResearch.WordTrace]
  refine ⟨45826933974056498048040913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61102578632075330730721217 45826933974056498048040913)
  ·
    refine ⟨34370200480542373536030685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45826933974056498048040913 34370200480542373536030685)
    ·
      refine ⟨12888825180203390076011507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34370200480542373536030685 12888825180203390076011507)
      ·
        refine ⟨19333237770305085114017261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12888825180203390076011507 19333237770305085114017261)
        ·
          refine ⟨7249964163864406917756473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19333237770305085114017261 7249964163864406917756473)
          ·
            refine ⟨5437473122898305188317355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7249964163864406917756473 5437473122898305188317355)
            ·
              refine ⟨8156209684347457782476033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5437473122898305188317355 8156209684347457782476033)
              ·
                refine ⟨6117157263260593336857025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8156209684347457782476033 6117157263260593336857025)
                ·
                  refine ⟨4587867947445445002642769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6117157263260593336857025 4587867947445445002642769)
                  ·
                    refine ⟨3440900960584083751982077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4587867947445445002642769 3440900960584083751982077)
                    ·
                      refine ⟨1290337860219031406993279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3440900960584083751982077 1290337860219031406993279)
                      ·
                        rfl

theorem cell23_2512924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 2, 2, 2, 3].length) (baseStart_2512924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2512924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2512924 prefixEnd_2512924 := by exact prefixLift 2512924
  have htrace : WordTrace (prefixWord ++ tailWord_2512924) baseStart_2512924 baseEnd_2512924 := by
    simpa [prefixWord, tailWord_2512924, baseEnd_2512924] using wordTrace_append hprefix tailTrace_2512924
  have hstable : (prefixWord ++ tailWord_2512924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2512924).length < 2 ^ (prefixWord ++ tailWord_2512924).sum := by decide
  have hdescent : baseEnd_2512924 < baseStart_2512924 := by decide
  rcases family_descends (prefixWord ++ tailWord_2512924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2512931 : List Nat := [1, 1, 1, 4, 3, 1, 5, 2, 1, 4]
def baseStart_2512931 : Nat := 118140960795 + 2512931 * 2 ^ 59
def prefixEnd_2512931 : Nat := 4983230072969 + 3 ^ 40 * 2512931 * 2
def baseEnd_2512931 : Nat := 430113818194537626535249

theorem tailTrace_2512931 : CollatzResearch.WordTrace tailWord_2512931 prefixEnd_2512931 430113818194537626535249 := by
  unfold tailWord_2512931
  simp only [CollatzResearch.WordTrace]
  refine ⟨91654123259087636291586647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61102748839391757527724431 91654123259087636291586647)
  ·
    refine ⟨137481184888631454437379971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91654123259087636291586647 137481184888631454437379971)
    ·
      refine ⟨206221777332947181656069957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137481184888631454437379971 206221777332947181656069957)
      ·
        refine ⟨38666583249927596560513117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 206221777332947181656069957 38666583249927596560513117)
        ·
          refine ⟨14499968718722848710192419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38666583249927596560513117 14499968718722848710192419)
          ·
            refine ⟨21749953078084273065288629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14499968718722848710192419 21749953078084273065288629)
            ·
              refine ⟨2039058101070400599870809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21749953078084273065288629 2039058101070400599870809)
              ·
                refine ⟨1529293575802800449903107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2039058101070400599870809 1529293575802800449903107)
                ·
                  refine ⟨2293940363704200674854661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1529293575802800449903107 2293940363704200674854661)
                  ·
                    refine ⟨430113818194537626535249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2293940363704200674854661 430113818194537626535249)
                    ·
                      rfl

theorem cell23_2512931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 5, 2, 1, 4].length) (baseStart_2512931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2512931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2512931 prefixEnd_2512931 := by exact prefixLift 2512931
  have htrace : WordTrace (prefixWord ++ tailWord_2512931) baseStart_2512931 baseEnd_2512931 := by
    simpa [prefixWord, tailWord_2512931, baseEnd_2512931] using wordTrace_append hprefix tailTrace_2512931
  have hstable : (prefixWord ++ tailWord_2512931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2512931).length < 2 ^ (prefixWord ++ tailWord_2512931).sum := by decide
  have hdescent : baseEnd_2512931 < baseStart_2512931 := by decide
  rcases family_descends (prefixWord ++ tailWord_2512931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2512944 : List Nat := [2, 1, 1, 1, 2, 7, 2, 1, 6]
def baseStart_2512944 : Nat := 118140960795 + 2512944 * 2 ^ 59
def prefixEnd_2512944 : Nat := 4983230072969 + 3 ^ 40 * 2512944 * 2
def baseEnd_2512944 : Nat := 143372014425791258749243

theorem tailTrace_2512944 : CollatzResearch.WordTrace tailWord_2512944 prefixEnd_2512944 143372014425791258749243 := by
  unfold tailWord_2512944
  simp only [CollatzResearch.WordTrace]
  refine ⟨45827298704020269755904943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61103064938693693007873257 45827298704020269755904943)
  ·
    refine ⟨68740948056030404633857415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45827298704020269755904943 68740948056030404633857415)
    ·
      refine ⟨103111422084045606950786123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68740948056030404633857415 103111422084045606950786123)
      ·
        refine ⟨154667133126068410426179185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103111422084045606950786123 154667133126068410426179185)
        ·
          refine ⟨116000349844551307819634389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 154667133126068410426179185 116000349844551307819634389)
          ·
            refine ⟨2718758199481671277022681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 116000349844551307819634389 2718758199481671277022681)
            ·
              refine ⟨2039068649611253457767011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2718758199481671277022681 2039068649611253457767011)
              ·
                refine ⟨3058602974416880186650517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2039068649611253457767011 3058602974416880186650517)
                ·
                  refine ⟨143372014425791258749243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3058602974416880186650517 143372014425791258749243)
                  ·
                    rfl

theorem cell23_2512944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 2, 1, 6].length) (baseStart_2512944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2512944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2512944 prefixEnd_2512944 := by exact prefixLift 2512944
  have htrace : WordTrace (prefixWord ++ tailWord_2512944) baseStart_2512944 baseEnd_2512944 := by
    simpa [prefixWord, tailWord_2512944, baseEnd_2512944] using wordTrace_append hprefix tailTrace_2512944
  have hstable : (prefixWord ++ tailWord_2512944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2512944).length < 2 ^ (prefixWord ++ tailWord_2512944).sum := by decide
  have hdescent : baseEnd_2512944 < baseStart_2512944 := by decide
  rcases family_descends (prefixWord ++ tailWord_2512944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2512947 : List Nat := [1, 1, 1, 2, 4, 1, 2, 1, 3, 5, 2]
def baseStart_2512947 : Nat := 118140960795 + 2512947 * 2 ^ 59
def prefixEnd_2512947 : Nat := 4983230072969 + 3 ^ 40 * 2512947 * 2
def baseEnd_2512947 : Nat := 1290349670274084817005673

theorem tailTrace_2512947 : CollatzResearch.WordTrace tailWord_2512947 prefixEnd_2512947 1290349670274084817005673 := by
  unfold tailWord_2512947
  simp only [CollatzResearch.WordTrace]
  refine ⟨91654706827029671024169095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61103137884686447349446063 91654706827029671024169095)
  ·
    refine ⟨137482060240544506536253643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91654706827029671024169095 137482060240544506536253643)
    ·
      refine ⟨206223090360816759804380465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137482060240544506536253643 206223090360816759804380465)
      ·
        refine ⟨154667317770612569853285349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 206223090360816759804380465 154667317770612569853285349)
        ·
          refine ⟨29000122081989856847491003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 154667317770612569853285349 29000122081989856847491003)
          ·
            refine ⟨43500183122984785271236505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29000122081989856847491003 43500183122984785271236505)
            ·
              refine ⟨32625137342238588953427379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43500183122984785271236505 32625137342238588953427379)
              ·
                refine ⟨48937706013357883430141069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32625137342238588953427379 48937706013357883430141069)
                ·
                  refine ⟨18351639755009206286302901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48937706013357883430141069 18351639755009206286302901)
                  ·
                    refine ⟨1720466227032113089340897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18351639755009206286302901 1720466227032113089340897)
                    ·
                      refine ⟨1290349670274084817005673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1720466227032113089340897 1290349670274084817005673)
                      ·
                        rfl

theorem cell23_2512947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 1, 3, 5, 2].length) (baseStart_2512947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2512947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2512947 prefixEnd_2512947 := by exact prefixLift 2512947
  have htrace : WordTrace (prefixWord ++ tailWord_2512947) baseStart_2512947 baseEnd_2512947 := by
    simpa [prefixWord, tailWord_2512947, baseEnd_2512947] using wordTrace_append hprefix tailTrace_2512947
  have hstable : (prefixWord ++ tailWord_2512947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2512947).length < 2 ^ (prefixWord ++ tailWord_2512947).sum := by decide
  have hdescent : baseEnd_2512947 < baseStart_2512947 := by decide
  rcases family_descends (prefixWord ++ tailWord_2512947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2512957 : List Nat := [1, 4, 1, 3, 1, 1, 3, 1, 3, 5]
def baseStart_2512957 : Nat := 118140960795 + 2512957 * 2 ^ 59
def prefixEnd_2512957 : Nat := 4983230072969 + 3 ^ 40 * 2512957 * 2
def baseEnd_2512957 : Nat := 430118268360209925960209

theorem tailTrace_2512957 : CollatzResearch.WordTrace tailWord_2512957 prefixEnd_2512957 430118268360209925960209 := by
  unfold tailWord_2512957
  simp only [CollatzResearch.WordTrace]
  refine ⟨91655071556993442732033125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61103381037995628488022083 91655071556993442732033125)
  ·
    refine ⟨17185325916936270512256211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 91655071556993442732033125 17185325916936270512256211)
    ·
      refine ⟨25777988875404405768384317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17185325916936270512256211 25777988875404405768384317)
      ·
        refine ⟨9666745828276652163144119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25777988875404405768384317 9666745828276652163144119)
        ·
          refine ⟨14500118742414978244716179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9666745828276652163144119 14500118742414978244716179)
          ·
            refine ⟨21750178113622467367074269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14500118742414978244716179 21750178113622467367074269)
            ·
              refine ⟨8156316792608425262652851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21750178113622467367074269 8156316792608425262652851)
              ·
                refine ⟨12234475188912637893979277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8156316792608425262652851 12234475188912637893979277)
                ·
                  refine ⟨4587928195842239210242229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12234475188912637893979277 4587928195842239210242229)
                  ·
                    refine ⟨430118268360209925960209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4587928195842239210242229 430118268360209925960209)
                    ·
                      rfl

theorem cell23_2512957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 1, 3, 5].length) (baseStart_2512957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2512957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2512957 prefixEnd_2512957 := by exact prefixLift 2512957
  have htrace : WordTrace (prefixWord ++ tailWord_2512957) baseStart_2512957 baseEnd_2512957 := by
    simpa [prefixWord, tailWord_2512957, baseEnd_2512957] using wordTrace_append hprefix tailTrace_2512957
  have hstable : (prefixWord ++ tailWord_2512957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2512957).length < 2 ^ (prefixWord ++ tailWord_2512957).sum := by decide
  have hdescent : baseEnd_2512957 < baseStart_2512957 := by decide
  rcases family_descends (prefixWord ++ tailWord_2512957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2512982 : List Nat := [5, 2, 2, 1, 1, 3, 2, 2, 1, 4]
def baseStart_2512982 : Nat := 118140960795 + 2512982 * 2 ^ 59
def prefixEnd_2512982 : Nat := 4983230072969 + 3 ^ 40 * 2512982 * 2
def baseEnd_2512982 : Nat := 430122547365664060022671

theorem tailTrace_2512982 : CollatzResearch.WordTrace tailWord_2512982 prefixEnd_2512982 430122547365664060022671 := by
  unfold tailWord_2512982
  simp only [CollatzResearch.WordTrace]
  refine ⟨5728498961368929500105825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 61103988921268581334462133 5728498961368929500105825)
  ·
    refine ⟨4296374221026697125079369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5728498961368929500105825 4296374221026697125079369)
    ·
      refine ⟨3222280665770022843809527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4296374221026697125079369 3222280665770022843809527)
      ·
        refine ⟨4833420998655034265714291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3222280665770022843809527 4833420998655034265714291)
        ·
          refine ⟨7250131497982551398571437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4833420998655034265714291 7250131497982551398571437)
          ·
            refine ⟨2718799311743456774464289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7250131497982551398571437 2718799311743456774464289)
            ·
              refine ⟨2039099483807592580848217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2718799311743456774464289 2039099483807592580848217)
              ·
                refine ⟨1529324612855694435636163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2039099483807592580848217 1529324612855694435636163)
                ·
                  refine ⟨2293986919283541653454245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1529324612855694435636163 2293986919283541653454245)
                  ·
                    refine ⟨430122547365664060022671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2293986919283541653454245 430122547365664060022671)
                    ·
                      rfl

theorem cell23_2512982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_2512982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2512982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2512982 prefixEnd_2512982 := by exact prefixLift 2512982
  have htrace : WordTrace (prefixWord ++ tailWord_2512982) baseStart_2512982 baseEnd_2512982 := by
    simpa [prefixWord, tailWord_2512982, baseEnd_2512982] using wordTrace_append hprefix tailTrace_2512982
  have hstable : (prefixWord ++ tailWord_2512982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2512982).length < 2 ^ (prefixWord ++ tailWord_2512982).sum := by decide
  have hdescent : baseEnd_2512982 < baseStart_2512982 := by decide
  rcases family_descends (prefixWord ++ tailWord_2512982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2512988 : List Nat := [2, 2, 4, 1, 1, 3, 1, 4, 1, 1, 3]
def baseStart_2512988 : Nat := 118140960795 + 2512988 * 2 ^ 59
def prefixEnd_2512988 : Nat := 4983230072969 + 3 ^ 40 * 2512988 * 2
def baseEnd_2512988 : Nat := 1290370722980919156592985

theorem tailTrace_2512988 : CollatzResearch.WordTrace tailWord_2512988 prefixEnd_2512988 1290370722980919156592985 := by
  unfold tailWord_2512988
  simp only [CollatzResearch.WordTrace]
  refine ⟨45828101109940567513205809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61104134813254090017607745 45828101109940567513205809)
  ·
    refine ⟨34371075832455425634904357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45828101109940567513205809 34371075832455425634904357)
    ·
      refine ⟨6444576718585392306544567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34371075832455425634904357 6444576718585392306544567)
      ·
        refine ⟨9666865077878088459816851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6444576718585392306544567 9666865077878088459816851)
        ·
          refine ⟨14500297616817132689725277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9666865077878088459816851 14500297616817132689725277)
          ·
            refine ⟨5437611606306424758646979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14500297616817132689725277 5437611606306424758646979)
            ·
              refine ⟨8156417409459637137970469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5437611606306424758646979 8156417409459637137970469)
              ·
                refine ⟨1529328264273681963369463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8156417409459637137970469 1529328264273681963369463)
                ·
                  refine ⟨2293992396410522945054195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1529328264273681963369463 2293992396410522945054195)
                  ·
                    refine ⟨3440988594615784417581293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2293992396410522945054195 3440988594615784417581293)
                    ·
                      refine ⟨1290370722980919156592985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3440988594615784417581293 1290370722980919156592985)
                      ·
                        rfl

theorem cell23_2512988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 4, 1, 1, 3].length) (baseStart_2512988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2512988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2512988 prefixEnd_2512988 := by exact prefixLift 2512988
  have htrace : WordTrace (prefixWord ++ tailWord_2512988) baseStart_2512988 baseEnd_2512988 := by
    simpa [prefixWord, tailWord_2512988, baseEnd_2512988] using wordTrace_append hprefix tailTrace_2512988
  have hstable : (prefixWord ++ tailWord_2512988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2512988).length < 2 ^ (prefixWord ++ tailWord_2512988).sum := by decide
  have hdescent : baseEnd_2512988 < baseStart_2512988 := by decide
  rcases family_descends (prefixWord ++ tailWord_2512988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2513004 : List Nat := [2, 2, 1, 1, 3, 3, 2, 3, 2, 4]
def baseStart_2513004 : Nat := 118140960795 + 2513004 * 2 ^ 59
def prefixEnd_2513004 : Nat := 4983230072969 + 3 ^ 40 * 2513004 * 2
def baseEnd_2513004 : Nat := 430126312890463697997637

theorem tailTrace_2513004 : CollatzResearch.WordTrace tailWord_2513004 prefixEnd_2513004 430126312890463697997637 := by
  unfold tailWord_2513004
  simp only [CollatzResearch.WordTrace]
  refine ⟨45828392893911584879497033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61104523858548779839329377 45828392893911584879497033)
  ·
    refine ⟨34371294670433688659622775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45828392893911584879497033 34371294670433688659622775)
    ·
      refine ⟨51556942005650532989434163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34371294670433688659622775 51556942005650532989434163)
      ·
        refine ⟨77335413008475799484151245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51556942005650532989434163 77335413008475799484151245)
        ·
          refine ⟨29000779878178424806556717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77335413008475799484151245 29000779878178424806556717)
          ·
            refine ⟨10875292454316909302458769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29000779878178424806556717 10875292454316909302458769)
            ·
              refine ⟨8156469340737681976844077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10875292454316909302458769 8156469340737681976844077)
              ·
                refine ⟨3058676002776630741316529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8156469340737681976844077 3058676002776630741316529)
                ·
                  refine ⟨2294007002082473055987397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3058676002776630741316529 2294007002082473055987397)
                  ·
                    refine ⟨430126312890463697997637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2294007002082473055987397 430126312890463697997637)
                    ·
                      rfl

theorem cell23_2513004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 4].length) (baseStart_2513004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2513004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2513004 prefixEnd_2513004 := by exact prefixLift 2513004
  have htrace : WordTrace (prefixWord ++ tailWord_2513004) baseStart_2513004 baseEnd_2513004 := by
    simpa [prefixWord, tailWord_2513004, baseEnd_2513004] using wordTrace_append hprefix tailTrace_2513004
  have hstable : (prefixWord ++ tailWord_2513004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2513004).length < 2 ^ (prefixWord ++ tailWord_2513004).sum := by decide
  have hdescent : baseEnd_2513004 < baseStart_2513004 := by decide
  rcases family_descends (prefixWord ++ tailWord_2513004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2513007 : List Nat := [1, 1, 2, 1, 3, 4, 1, 3, 1, 2, 4]
def baseStart_2513007 : Nat := 118140960795 + 2513007 * 2 ^ 59
def prefixEnd_2513007 : Nat := 4983230072969 + 3 ^ 40 * 2513007 * 2
def baseEnd_2513007 : Nat := 1290380479113354582255397

theorem tailTrace_2513007 : CollatzResearch.WordTrace tailWord_2513007 prefixEnd_2513007 1290380479113354582255397 := by
  unfold tailWord_2513007
  simp only [CollatzResearch.WordTrace]
  refine ⟨91656895206812301271353275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61104596804541534180902183 91656895206812301271353275)
  ·
    refine ⟨137485342810218451907029913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91656895206812301271353275 137485342810218451907029913)
    ·
      refine ⟨103114007107663838930272435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137485342810218451907029913 103114007107663838930272435)
      ·
        refine ⟨154671010661495758395408653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103114007107663838930272435 154671010661495758395408653)
        ·
          refine ⟨58001628998060909398278245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 154671010661495758395408653 58001628998060909398278245)
          ·
            refine ⟨10875305437136420512177171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58001628998060909398278245 10875305437136420512177171)
            ·
              refine ⟨16312958155704630768265757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10875305437136420512177171 16312958155704630768265757)
              ·
                refine ⟨6117359308389236538099659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16312958155704630768265757 6117359308389236538099659)
                ·
                  refine ⟨9176038962583854807149489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6117359308389236538099659 9176038962583854807149489)
                  ·
                    refine ⟨6882029221937891105362117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9176038962583854807149489 6882029221937891105362117)
                    ·
                      refine ⟨1290380479113354582255397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6882029221937891105362117 1290380479113354582255397)
                      ·
                        rfl

theorem cell23_2513007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 3, 1, 2, 4].length) (baseStart_2513007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2513007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2513007 prefixEnd_2513007 := by exact prefixLift 2513007
  have htrace : WordTrace (prefixWord ++ tailWord_2513007) baseStart_2513007 baseEnd_2513007 := by
    simpa [prefixWord, tailWord_2513007, baseEnd_2513007] using wordTrace_append hprefix tailTrace_2513007
  have hstable : (prefixWord ++ tailWord_2513007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2513007).length < 2 ^ (prefixWord ++ tailWord_2513007).sum := by decide
  have hdescent : baseEnd_2513007 < baseStart_2513007 := by decide
  rcases family_descends (prefixWord ++ tailWord_2513007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2513031 : List Nat := [1, 1, 4, 2, 1, 1, 6, 1, 1, 2, 3]
def baseStart_2513031 : Nat := 118140960795 + 2513031 * 2 ^ 59
def prefixEnd_2513031 : Nat := 4983230072969 + 3 ^ 40 * 2513031 * 2
def baseEnd_2513031 : Nat := 1290392802649062488355287

theorem tailTrace_2513031 : CollatzResearch.WordTrace tailWord_2513031 prefixEnd_2513031 1290392802649062488355287 := by
  unfold tailWord_2513031
  simp only [CollatzResearch.WordTrace]
  refine ⟨91657770558725353370226947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61105180372483568913484631 91657770558725353370226947)
  ·
    refine ⟨137486655838088030055340421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91657770558725353370226947 137486655838088030055340421)
    ·
      refine ⟨25778747969641505635376329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 137486655838088030055340421 25778747969641505635376329)
      ·
        refine ⟨19334060977231129226532247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25778747969641505635376329 19334060977231129226532247)
        ·
          refine ⟨29001091465846693839798371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19334060977231129226532247 29001091465846693839798371)
          ·
            refine ⟨43501637198770040759697557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29001091465846693839798371 43501637198770040759697557)
            ·
              refine ⟨2039139243692345660610823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 43501637198770040759697557 2039139243692345660610823)
              ·
                refine ⟨3058708865538518490916235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2039139243692345660610823 3058708865538518490916235)
                ·
                  refine ⟨4588063298307777736374353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3058708865538518490916235 4588063298307777736374353)
                  ·
                    refine ⟨3441047473730833302280765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4588063298307777736374353 3441047473730833302280765)
                    ·
                      refine ⟨1290392802649062488355287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3441047473730833302280765 1290392802649062488355287)
                      ·
                        rfl

theorem cell23_2513031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 6, 1, 1, 2, 3].length) (baseStart_2513031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2513031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2513031 prefixEnd_2513031 := by exact prefixLift 2513031
  have htrace : WordTrace (prefixWord ++ tailWord_2513031) baseStart_2513031 baseEnd_2513031 := by
    simpa [prefixWord, tailWord_2513031, baseEnd_2513031] using wordTrace_append hprefix tailTrace_2513031
  have hstable : (prefixWord ++ tailWord_2513031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2513031).length < 2 ^ (prefixWord ++ tailWord_2513031).sum := by decide
  have hdescent : baseEnd_2513031 < baseStart_2513031 := by decide
  rcases family_descends (prefixWord ++ tailWord_2513031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2513038 : List Nat := [4, 1, 1, 3, 3, 2, 1, 2, 2, 4]
def baseStart_2513038 : Nat := 118140960795 + 2513038 * 2 ^ 59
def prefixEnd_2513038 : Nat := 4983230072969 + 3 ^ 40 * 2513038 * 2
def baseEnd_2513038 : Nat := 430132132337881320322585

theorem tailTrace_2513038 : CollatzResearch.WordTrace tailWord_2513038 prefixEnd_2513038 430132132337881320322585 := by
  unfold tailWord_2513038
  simp only [CollatzResearch.WordTrace]
  refine ⟨11457253233712499195716471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61105350579799995710487845 11457253233712499195716471)
  ·
    refine ⟨17185879850568748793574707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11457253233712499195716471 17185879850568748793574707)
    ·
      refine ⟨25778819775853123190362061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17185879850568748793574707 25778819775853123190362061)
      ·
        refine ⟨9667057415944921196385773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25778819775853123190362061 9667057415944921196385773)
        ·
          refine ⟨3625146530979345448644665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9667057415944921196385773 3625146530979345448644665)
          ·
            refine ⟨2718859898234509086483499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3625146530979345448644665 2718859898234509086483499)
            ·
              refine ⟨4078289847351763629725249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2718859898234509086483499 4078289847351763629725249)
              ·
                refine ⟨3058717385513822722293937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4078289847351763629725249 3058717385513822722293937)
                ·
                  refine ⟨2294038039135367041720453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3058717385513822722293937 2294038039135367041720453)
                  ·
                    refine ⟨430132132337881320322585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2294038039135367041720453 430132132337881320322585)
                    ·
                      rfl

theorem cell23_2513038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 1, 2, 2, 4].length) (baseStart_2513038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2513038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2513038 prefixEnd_2513038 := by exact prefixLift 2513038
  have htrace : WordTrace (prefixWord ++ tailWord_2513038) baseStart_2513038 baseEnd_2513038 := by
    simpa [prefixWord, tailWord_2513038, baseEnd_2513038] using wordTrace_append hprefix tailTrace_2513038
  have hstable : (prefixWord ++ tailWord_2513038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2513038).length < 2 ^ (prefixWord ++ tailWord_2513038).sum := by decide
  have hdescent : baseEnd_2513038 < baseStart_2513038 := by decide
  rcases family_descends (prefixWord ++ tailWord_2513038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2513087 : List Nat := [1, 1, 2, 2, 2, 2, 1, 2, 1, 6, 3]
def baseStart_2513087 : Nat := 118140960795 + 2513087 * 2 ^ 59
def prefixEnd_2513087 : Nat := 4983230072969 + 3 ^ 40 * 2513087 * 2
def baseEnd_2513087 : Nat := 1290421557565714269255029

theorem tailTrace_2513087 : CollatzResearch.WordTrace tailWord_2513087 prefixEnd_2513087 1290421557565714269255029 := by
  unfold tailWord_2513087
  simp only [CollatzResearch.WordTrace]
  refine ⟨91659813046522474934265515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61106542031014983289510343 91659813046522474934265515)
  ·
    refine ⟨137489719569783712401398273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91659813046522474934265515 137489719569783712401398273)
    ·
      refine ⟨103117289677337784301048705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137489719569783712401398273 103117289677337784301048705)
      ·
        refine ⟨77337967258003338225786529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103117289677337784301048705 77337967258003338225786529)
        ·
          refine ⟨58003475443502503669339897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77337967258003338225786529 58003475443502503669339897)
          ·
            refine ⟨43502606582626877752004923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58003475443502503669339897 43502606582626877752004923)
            ·
              refine ⟨65253909873940316628007385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43502606582626877752004923 65253909873940316628007385)
              ·
                refine ⟨48940432405455237471005539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65253909873940316628007385 48940432405455237471005539)
                ·
                  refine ⟨73410648608182856206508309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48940432405455237471005539 73410648608182856206508309)
                  ·
                    refine ⟨3441124153508571384680077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 73410648608182856206508309 3441124153508571384680077)
                    ·
                      refine ⟨1290421557565714269255029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3441124153508571384680077 1290421557565714269255029)
                      ·
                        rfl

theorem cell23_2513087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 6, 3].length) (baseStart_2513087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2513087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2513087 prefixEnd_2513087 := by exact prefixLift 2513087
  have htrace : WordTrace (prefixWord ++ tailWord_2513087) baseStart_2513087 baseEnd_2513087 := by
    simpa [prefixWord, tailWord_2513087, baseEnd_2513087] using wordTrace_append hprefix tailTrace_2513087
  have hstable : (prefixWord ++ tailWord_2513087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2513087).length < 2 ^ (prefixWord ++ tailWord_2513087).sum := by decide
  have hdescent : baseEnd_2513087 < baseStart_2513087 := by decide
  rcases family_descends (prefixWord ++ tailWord_2513087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2513097 : List Nat := [1, 2, 1, 1, 2, 1, 1, 6, 2, 2, 4]
def baseStart_2513097 : Nat := 118140960795 + 2513097 * 2 ^ 59
def prefixEnd_2513097 : Nat := 4983230072969 + 3 ^ 40 * 2513097 * 2
def baseEnd_2513097 : Nat := 1290426692372259230129983

theorem tailTrace_2513097 : CollatzResearch.WordTrace tailWord_2513097 prefixEnd_2513097 1290426692372259230129983 := by
  unfold tailWord_2513097
  simp only [CollatzResearch.WordTrace]
  refine ⟨91660177776486246642129545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61106785184324164428086363 91660177776486246642129545)
  ·
    refine ⟨68745133332364684981597159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91660177776486246642129545 68745133332364684981597159)
    ·
      refine ⟨103117699998547027472395739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68745133332364684981597159 103117699998547027472395739)
      ·
        refine ⟨154676549997820541208593609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103117699998547027472395739 154676549997820541208593609)
        ·
          refine ⟨116007412498365405906445207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 154676549997820541208593609 116007412498365405906445207)
          ·
            refine ⟨174011118747548108859667811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116007412498365405906445207 174011118747548108859667811)
            ·
              refine ⟨261016678121322163289501717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 174011118747548108859667811 261016678121322163289501717)
              ·
                refine ⟨12235156786936976404195393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 261016678121322163289501717 12235156786936976404195393)
                ·
                  refine ⟨9176367590202732303146545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12235156786936976404195393 9176367590202732303146545)
                  ·
                    refine ⟨6882275692652049227359909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9176367590202732303146545 6882275692652049227359909)
                    ·
                      refine ⟨1290426692372259230129983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6882275692652049227359909 1290426692372259230129983)
                      ·
                        rfl

theorem cell23_2513097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 6, 2, 2, 4].length) (baseStart_2513097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2513097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2513097 prefixEnd_2513097 := by exact prefixLift 2513097
  have htrace : WordTrace (prefixWord ++ tailWord_2513097) baseStart_2513097 baseEnd_2513097 := by
    simpa [prefixWord, tailWord_2513097, baseEnd_2513097] using wordTrace_append hprefix tailTrace_2513097
  have hstable : (prefixWord ++ tailWord_2513097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2513097).length < 2 ^ (prefixWord ++ tailWord_2513097).sum := by decide
  have hdescent : baseEnd_2513097 < baseStart_2513097 := by decide
  rcases family_descends (prefixWord ++ tailWord_2513097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2513122 : List Nat := [3, 3, 4, 1, 1, 1, 1, 1, 3, 3, 2]
def baseStart_2513122 : Nat := 118140960795 + 2513122 * 2 ^ 59
def prefixEnd_2513122 : Nat := 4983230072969 + 3 ^ 40 * 2513122 * 2
def baseEnd_2513122 : Nat := 1290439529388621632317369

theorem tailTrace_2513122 : CollatzResearch.WordTrace tailWord_2513122 prefixEnd_2513122 1290439529388621632317369 := by
  unfold tailWord_2513122
  simp only [CollatzResearch.WordTrace]
  refine ⟨22915272400348918977947405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61107393067597117274526413 22915272400348918977947405)
  ·
    refine ⟨8593227150130844616730277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22915272400348918977947405 8593227150130844616730277)
    ·
      refine ⟨1611230090649533365636927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8593227150130844616730277 1611230090649533365636927)
      ·
        refine ⟨2416845135974300048455391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1611230090649533365636927 2416845135974300048455391)
        ·
          refine ⟨3625267703961450072683087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2416845135974300048455391 3625267703961450072683087)
          ·
            refine ⟨5437901555942175109024631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3625267703961450072683087 5437901555942175109024631)
            ·
              refine ⟨8156852333913262663536947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5437901555942175109024631 8156852333913262663536947)
              ·
                refine ⟨12235278500869893995305421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8156852333913262663536947 12235278500869893995305421)
                ·
                  refine ⟨4588229437826210248239533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12235278500869893995305421 4588229437826210248239533)
                  ·
                    refine ⟨1720586039184828843089825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4588229437826210248239533 1720586039184828843089825)
                    ·
                      refine ⟨1290439529388621632317369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1720586039184828843089825 1290439529388621632317369)
                      ·
                        rfl

theorem cell23_2513122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_2513122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2513122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2513122 prefixEnd_2513122 := by exact prefixLift 2513122
  have htrace : WordTrace (prefixWord ++ tailWord_2513122) baseStart_2513122 baseEnd_2513122 := by
    simpa [prefixWord, tailWord_2513122, baseEnd_2513122] using wordTrace_append hprefix tailTrace_2513122
  have hstable : (prefixWord ++ tailWord_2513122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2513122).length < 2 ^ (prefixWord ++ tailWord_2513122).sum := by decide
  have hdescent : baseEnd_2513122 < baseStart_2513122 := by decide
  rcases family_descends (prefixWord ++ tailWord_2513122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2513134 : List Nat := [4, 1, 2, 1, 1, 1, 1, 2, 4, 3, 3]
def baseStart_2513134 : Nat := 118140960795 + 2513134 * 2 ^ 59
def prefixEnd_2513134 : Nat := 4983230072969 + 3 ^ 40 * 2513134 * 2
def baseEnd_2513134 : Nat := 1290445691156475585367313

theorem tailTrace_2513134 : CollatzResearch.WordTrace tailWord_2513134 prefixEnd_2513134 1290445691156475585367313 := by
  unfold tailWord_2513134
  simp only [CollatzResearch.WordTrace]
  refine ⟨11457690909669025245153307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61107684851568134640817637 11457690909669025245153307)
  ·
    refine ⟨17186536364503537867729961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11457690909669025245153307 17186536364503537867729961)
    ·
      refine ⟨12889902273377653400797471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17186536364503537867729961 12889902273377653400797471)
      ·
        refine ⟨19334853410066480101196207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12889902273377653400797471 19334853410066480101196207)
        ·
          refine ⟨29002280115099720151794311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19334853410066480101196207 29002280115099720151794311)
          ·
            refine ⟨43503420172649580227691467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29002280115099720151794311 43503420172649580227691467)
            ·
              refine ⟨65255130258974370341537201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43503420172649580227691467 65255130258974370341537201)
              ·
                refine ⟨48941347694230777756152901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65255130258974370341537201 48941347694230777756152901)
                ·
                  refine ⟨9176502692668270829278669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48941347694230777756152901 9176502692668270829278669)
                  ·
                    refine ⟨3441188509750601560979501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9176502692668270829278669 3441188509750601560979501)
                    ·
                      refine ⟨1290445691156475585367313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3441188509750601560979501 1290445691156475585367313)
                      ·
                        rfl

theorem cell23_2513134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 2, 4, 3, 3].length) (baseStart_2513134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2513134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2513134 prefixEnd_2513134 := by exact prefixLift 2513134
  have htrace : WordTrace (prefixWord ++ tailWord_2513134) baseStart_2513134 baseEnd_2513134 := by
    simpa [prefixWord, tailWord_2513134, baseEnd_2513134] using wordTrace_append hprefix tailTrace_2513134
  have hstable : (prefixWord ++ tailWord_2513134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2513134).length < 2 ^ (prefixWord ++ tailWord_2513134).sum := by decide
  have hdescent : baseEnd_2513134 < baseStart_2513134 := by decide
  rcases family_descends (prefixWord ++ tailWord_2513134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2513137 : List Nat := [1, 2, 2, 2, 2, 1, 2, 3, 1, 7]
def baseStart_2513137 : Nat := 118140960795 + 2513137 * 2 ^ 59
def prefixEnd_2513137 : Nat := 4983230072969 + 3 ^ 40 * 2513137 * 2
def baseEnd_2513137 : Nat := 430149077199479691209933

theorem tailTrace_2513137 : CollatzResearch.WordTrace tailWord_2513137 prefixEnd_2513137 430149077199479691209933 := by
  unfold tailWord_2513137
  simp only [CollatzResearch.WordTrace]
  refine ⟨91661636696341333473585665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61107757797560888982390443 91661636696341333473585665)
  ·
    refine ⟨68746227522256000105189249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91661636696341333473585665 68746227522256000105189249)
    ·
      refine ⟨51559670641692000078891937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68746227522256000105189249 51559670641692000078891937)
      ·
        refine ⟨38669752981269000059168953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51559670641692000078891937 38669752981269000059168953)
        ·
          refine ⟨29002314735951750044376715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38669752981269000059168953 29002314735951750044376715)
          ·
            refine ⟨43503472103927625066565073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29002314735951750044376715 43503472103927625066565073)
            ·
              refine ⟨32627604077945718799923805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43503472103927625066565073 32627604077945718799923805)
              ·
                refine ⟨12235351529229644549971427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32627604077945718799923805 12235351529229644549971427)
                ·
                  refine ⟨18353027293844466824957141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12235351529229644549971427 18353027293844466824957141)
                  ·
                    refine ⟨430149077199479691209933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18353027293844466824957141 430149077199479691209933)
                    ·
                      rfl

theorem cell23_2513137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 3, 1, 7].length) (baseStart_2513137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2513137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2513137 prefixEnd_2513137 := by exact prefixLift 2513137
  have htrace : WordTrace (prefixWord ++ tailWord_2513137) baseStart_2513137 baseEnd_2513137 := by
    simpa [prefixWord, tailWord_2513137, baseEnd_2513137] using wordTrace_append hprefix tailTrace_2513137
  have hstable : (prefixWord ++ tailWord_2513137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2513137).length < 2 ^ (prefixWord ++ tailWord_2513137).sum := by decide
  have hdescent : baseEnd_2513137 < baseStart_2513137 := by decide
  rcases family_descends (prefixWord ++ tailWord_2513137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2513144 : List Nat := [2, 1, 2, 1, 1, 2, 1, 2, 4, 5, 2]
def baseStart_2513144 : Nat := 118140960795 + 2513144 * 2 ^ 59
def prefixEnd_2513144 : Nat := 4983230072969 + 3 ^ 40 * 2513144 * 2
def baseEnd_2513144 : Nat := 1290450825963020546242267

theorem tailTrace_2513144 : CollatzResearch.WordTrace tailWord_2513144 prefixEnd_2513144 1290450825963020546242267 := by
  unfold tailWord_2513144
  simp only [CollatzResearch.WordTrace]
  refine ⟨45830946003657986834545243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61107928004877315779393657 45830946003657986834545243)
  ·
    refine ⟨68746419005486980251817865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45830946003657986834545243 68746419005486980251817865)
    ·
      refine ⟨51559814254115235188863399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68746419005486980251817865 51559814254115235188863399)
      ·
        refine ⟨77339721381172852783295099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51559814254115235188863399 77339721381172852783295099)
        ·
          refine ⟨116009582071759279174942649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77339721381172852783295099 116009582071759279174942649)
          ·
            refine ⟨87007186553819459381206987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116009582071759279174942649 87007186553819459381206987)
            ·
              refine ⟨130510779830729189071810481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87007186553819459381206987 130510779830729189071810481)
              ·
                refine ⟨97883084873046891803857861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 130510779830729189071810481 97883084873046891803857861)
                ·
                  refine ⟨18353078413696292213223349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 97883084873046891803857861 18353078413696292213223349)
                  ·
                    refine ⟨1720601101284027394989689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18353078413696292213223349 1720601101284027394989689)
                    ·
                      refine ⟨1290450825963020546242267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1720601101284027394989689 1290450825963020546242267)
                      ·
                        rfl

theorem cell23_2513144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 4, 5, 2].length) (baseStart_2513144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2513144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2513144 prefixEnd_2513144 := by exact prefixLift 2513144
  have htrace : WordTrace (prefixWord ++ tailWord_2513144) baseStart_2513144 baseEnd_2513144 := by
    simpa [prefixWord, tailWord_2513144, baseEnd_2513144] using wordTrace_append hprefix tailTrace_2513144
  have hstable : (prefixWord ++ tailWord_2513144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2513144).length < 2 ^ (prefixWord ++ tailWord_2513144).sum := by decide
  have hdescent : baseEnd_2513144 < baseStart_2513144 := by decide
  rcases family_descends (prefixWord ++ tailWord_2513144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2513227 : List Nat := [1, 1, 1, 1, 3, 1, 1, 3, 2, 9]
def baseStart_2513227 : Nat := 118140960795 + 2513227 * 2 ^ 59
def prefixEnd_2513227 : Nat := 4983230072969 + 3 ^ 40 * 2513227 * 2
def baseEnd_2513227 : Nat := 430164481619114573834795

theorem tailTrace_2513227 : CollatzResearch.WordTrace tailWord_2513227 prefixEnd_2513227 430164481619114573834795 := by
  unfold tailWord_2513227
  simp only [CollatzResearch.WordTrace]
  refine ⟨91664919266015278844361935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61109946177343519229574623 91664919266015278844361935)
  ·
    refine ⟨137497378899022918266542903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91664919266015278844361935 137497378899022918266542903)
    ·
      refine ⟨206246068348534377399814355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137497378899022918266542903 206246068348534377399814355)
      ·
        refine ⟨309369102522801566099721533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206246068348534377399814355 309369102522801566099721533)
        ·
          refine ⟨116013413446050587287395575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 309369102522801566099721533 116013413446050587287395575)
          ·
            refine ⟨174020120169075880931093363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116013413446050587287395575 174020120169075880931093363)
            ·
              refine ⟨261030180253613821396640045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 174020120169075880931093363 261030180253613821396640045)
              ·
                refine ⟨97886317595105183023740017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 261030180253613821396640045 97886317595105183023740017)
                ·
                  refine ⟨73414738196328887267805013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 97886317595105183023740017 73414738196328887267805013)
                  ·
                    refine ⟨430164481619114573834795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 73414738196328887267805013 430164481619114573834795)
                    ·
                      rfl

theorem cell23_2513227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 2, 9].length) (baseStart_2513227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2513227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2513227 prefixEnd_2513227 := by exact prefixLift 2513227
  have htrace : WordTrace (prefixWord ++ tailWord_2513227) baseStart_2513227 baseEnd_2513227 := by
    simpa [prefixWord, tailWord_2513227, baseEnd_2513227] using wordTrace_append hprefix tailTrace_2513227
  have hstable : (prefixWord ++ tailWord_2513227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2513227).length < 2 ^ (prefixWord ++ tailWord_2513227).sum := by decide
  have hdescent : baseEnd_2513227 < baseStart_2513227 := by decide
  rcases family_descends (prefixWord ++ tailWord_2513227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2513251 : List Nat := [1, 1, 1, 5, 2, 1, 1, 3, 1, 5, 2]
def baseStart_2513251 : Nat := 118140960795 + 2513251 * 2 ^ 59
def prefixEnd_2513251 : Nat := 4983230072969 + 3 ^ 40 * 2513251 * 2
def baseEnd_2513251 : Nat := 1290505768393051627604275

theorem tailTrace_2513251 : CollatzResearch.WordTrace tailWord_2513251 prefixEnd_2513251 1290505768393051627604275 := by
  unfold tailWord_2513251
  simp only [CollatzResearch.WordTrace]
  refine ⟨91665794617928330943235607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61110529745285553962157071 91665794617928330943235607)
  ·
    refine ⟨137498691926892496414853411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91665794617928330943235607 137498691926892496414853411)
    ·
      refine ⟨206248037890338744622280117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137498691926892496414853411 206248037890338744622280117)
      ·
        refine ⟨19335753552219257308338761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 206248037890338744622280117 19335753552219257308338761)
        ·
          refine ⟨14501815164164442981254071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19335753552219257308338761 14501815164164442981254071)
          ·
            refine ⟨21752722746246664471881107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14501815164164442981254071 21752722746246664471881107)
            ·
              refine ⟨32629084119369996707821661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21752722746246664471881107 32629084119369996707821661)
              ·
                refine ⟨12235906544763748765433123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32629084119369996707821661 12235906544763748765433123)
                ·
                  refine ⟨18353859817145623148149685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12235906544763748765433123 18353859817145623148149685)
                  ·
                    refine ⟨1720674357857402170139033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18353859817145623148149685 1720674357857402170139033)
                    ·
                      refine ⟨1290505768393051627604275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1720674357857402170139033 1290505768393051627604275)
                      ·
                        rfl

theorem cell23_2513251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 3, 1, 5, 2].length) (baseStart_2513251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2513251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2513251 prefixEnd_2513251 := by exact prefixLift 2513251
  have htrace : WordTrace (prefixWord ++ tailWord_2513251) baseStart_2513251 baseEnd_2513251 := by
    simpa [prefixWord, tailWord_2513251, baseEnd_2513251] using wordTrace_append hprefix tailTrace_2513251
  have hstable : (prefixWord ++ tailWord_2513251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2513251).length < 2 ^ (prefixWord ++ tailWord_2513251).sum := by decide
  have hdescent : baseEnd_2513251 < baseStart_2513251 := by decide
  rcases family_descends (prefixWord ++ tailWord_2513251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2513261 : List Nat := [1, 5, 1, 1, 1, 2, 1, 5, 1, 5]
def baseStart_2513261 : Nat := 118140960795 + 2513261 * 2 ^ 59
def prefixEnd_2513261 : Nat := 4983230072969 + 3 ^ 40 * 2513261 * 2
def baseEnd_2513261 : Nat := 430170301066532196159743

theorem tailTrace_2513261 : CollatzResearch.WordTrace tailWord_2513261 prefixEnd_2513261 430170301066532196159743 := by
  unfold tailWord_2513261
  simp only [CollatzResearch.WordTrace]
  refine ⟨91666159347892102651099637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61110772898594735100733091 91666159347892102651099637)
  ·
    refine ⟨8593702438864884623540591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 91666159347892102651099637 8593702438864884623540591)
    ·
      refine ⟨12890553658297326935310887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8593702438864884623540591 12890553658297326935310887)
      ·
        refine ⟨19335830487445990402966331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12890553658297326935310887 19335830487445990402966331)
        ·
          refine ⟨29003745731168985604449497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19335830487445990402966331 29003745731168985604449497)
          ·
            refine ⟨21752809298376739203337123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29003745731168985604449497 21752809298376739203337123)
            ·
              refine ⟨32629213947565108805005685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21752809298376739203337123 32629213947565108805005685)
              ·
                refine ⟨3058988807584228950469283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32629213947565108805005685 3058988807584228950469283)
                ·
                  refine ⟨4588483211376343425703925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3058988807584228950469283 4588483211376343425703925)
                  ·
                    refine ⟨430170301066532196159743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4588483211376343425703925 430170301066532196159743)
                    ·
                      rfl

theorem cell23_2513261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 5, 1, 5].length) (baseStart_2513261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2513261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2513261 prefixEnd_2513261 := by exact prefixLift 2513261
  have htrace : WordTrace (prefixWord ++ tailWord_2513261) baseStart_2513261 baseEnd_2513261 := by
    simpa [prefixWord, tailWord_2513261, baseEnd_2513261] using wordTrace_append hprefix tailTrace_2513261
  have hstable : (prefixWord ++ tailWord_2513261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2513261).length < 2 ^ (prefixWord ++ tailWord_2513261).sum := by decide
  have hdescent : baseEnd_2513261 < baseStart_2513261 := by decide
  rcases family_descends (prefixWord ++ tailWord_2513261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2513282 : List Nat := [3, 4, 2, 1, 2, 2, 2, 1, 6]
def baseStart_2513282 : Nat := 118140960795 + 2513282 * 2 ^ 59
def prefixEnd_2513282 : Nat := 4983230072969 + 3 ^ 40 * 2513282 * 2
def baseEnd_2513282 : Nat := 143391298477037889590737

theorem tailTrace_2513282 : CollatzResearch.WordTrace tailWord_2513282 prefixEnd_2513282 143391298477037889590737 := by
  unfold tailWord_2513282
  simp only [CollatzResearch.WordTrace]
  refine ⟨22916731320204005809403525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61111283520544015491742733 22916731320204005809403525)
  ·
    refine ⟨4296887122538251089263161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22916731320204005809403525 4296887122538251089263161)
    ·
      refine ⟨3222665341903688316947371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4296887122538251089263161 3222665341903688316947371)
      ·
        refine ⟨4833998012855532475421057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3222665341903688316947371 4833998012855532475421057)
        ·
          refine ⟨3625498509641649356565793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4833998012855532475421057 3625498509641649356565793)
          ·
            refine ⟨2719123882231237017424345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3625498509641649356565793 2719123882231237017424345)
            ·
              refine ⟨2039342911673427763068259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2719123882231237017424345 2039342911673427763068259)
              ·
                refine ⟨3059014367510141644602389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2039342911673427763068259 3059014367510141644602389)
                ·
                  refine ⟨143391298477037889590737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3059014367510141644602389 143391298477037889590737)
                  ·
                    rfl

theorem cell23_2513282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 2, 1, 6].length) (baseStart_2513282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2513282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2513282 prefixEnd_2513282 := by exact prefixLift 2513282
  have htrace : WordTrace (prefixWord ++ tailWord_2513282) baseStart_2513282 baseEnd_2513282 := by
    simpa [prefixWord, tailWord_2513282, baseEnd_2513282] using wordTrace_append hprefix tailTrace_2513282
  have hstable : (prefixWord ++ tailWord_2513282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2513282).length < 2 ^ (prefixWord ++ tailWord_2513282).sum := by decide
  have hdescent : baseEnd_2513282 < baseStart_2513282 := by decide
  rcases family_descends (prefixWord ++ tailWord_2513282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2513311 : List Nat := [1, 1, 2, 5, 1, 1, 3, 2, 1, 2, 4]
def baseStart_2513311 : Nat := 118140960795 + 2513311 * 2 ^ 59
def prefixEnd_2513311 : Nat := 4983230072969 + 3 ^ 40 * 2513311 * 2
def baseEnd_2513311 : Nat := 1290536577232321392853999

theorem tailTrace_2513311 : CollatzResearch.WordTrace tailWord_2513311 prefixEnd_2513311 1290536577232321392853999 := by
  unfold tailWord_2513311
  simp only [CollatzResearch.WordTrace]
  refine ⟨91667982997710961190419787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61111988665140640793613191 91667982997710961190419787)
  ·
    refine ⟨137501974496566441785629681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91667982997710961190419787 137501974496566441785629681)
    ·
      refine ⟨103126480872424831339222261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137501974496566441785629681 103126480872424831339222261)
      ·
        refine ⟨9668107581789827938052087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 103126480872424831339222261 9668107581789827938052087)
        ·
          refine ⟨14502161372684741907078131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9668107581789827938052087 14502161372684741907078131)
          ·
            refine ⟨21753242059027112860617197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14502161372684741907078131 21753242059027112860617197)
            ·
              refine ⟨8157465772135167322731449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21753242059027112860617197 8157465772135167322731449)
              ·
                refine ⟨6118099329101375492048587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8157465772135167322731449 6118099329101375492048587)
                ·
                  refine ⟨9177148993652063238072881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6118099329101375492048587 9177148993652063238072881)
                  ·
                    refine ⟨6882861745239047428554661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9177148993652063238072881 6882861745239047428554661)
                    ·
                      refine ⟨1290536577232321392853999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6882861745239047428554661 1290536577232321392853999)
                      ·
                        rfl

theorem cell23_2513311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_2513311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2513311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2513311 prefixEnd_2513311 := by exact prefixLift 2513311
  have htrace : WordTrace (prefixWord ++ tailWord_2513311) baseStart_2513311 baseEnd_2513311 := by
    simpa [prefixWord, tailWord_2513311, baseEnd_2513311] using wordTrace_append hprefix tailTrace_2513311
  have hstable : (prefixWord ++ tailWord_2513311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2513311).length < 2 ^ (prefixWord ++ tailWord_2513311).sum := by decide
  have hdescent : baseEnd_2513311 < baseStart_2513311 := by decide
  rcases family_descends (prefixWord ++ tailWord_2513311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2513344 : List Nat := [2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 5]
def baseStart_2513344 : Nat := 118140960795 + 2513344 * 2 ^ 59
def prefixEnd_2513344 : Nat := 4983230072969 + 3 ^ 40 * 2513344 * 2
def baseEnd_2513344 : Nat := 1290553522093919763741347

theorem tailTrace_2513344 : CollatzResearch.WordTrace tailWord_2513344 prefixEnd_2513344 1290553522093919763741347 := by
  unfold tailWord_2513344
  simp only [CollatzResearch.WordTrace]
  refine ⟨45834593303295703913185543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61112791071060938550914057 45834593303295703913185543)
  ·
    refine ⟨68751889954943555869778315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45834593303295703913185543 68751889954943555869778315)
    ·
      refine ⟨103127834932415333804667473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68751889954943555869778315 103127834932415333804667473)
      ·
        refine ⟨77345876199311500353500605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103127834932415333804667473 77345876199311500353500605)
        ·
          refine ⟨29004703574741812632562727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77345876199311500353500605 29004703574741812632562727)
          ·
            refine ⟨43507055362112718948844091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29004703574741812632562727 43507055362112718948844091)
            ·
              refine ⟨65260583043169078423266137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43507055362112718948844091 65260583043169078423266137)
              ·
                refine ⟨48945437282376808817449603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65260583043169078423266137 48945437282376808817449603)
                ·
                  refine ⟨73418155923565213226174405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48945437282376808817449603 73418155923565213226174405)
                  ·
                    refine ⟨13765904235668477479907701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 73418155923565213226174405 13765904235668477479907701)
                    ·
                      refine ⟨1290553522093919763741347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13765904235668477479907701 1290553522093919763741347)
                      ·
                        rfl

theorem cell23_2513344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 5].length) (baseStart_2513344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2513344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2513344 prefixEnd_2513344 := by exact prefixLift 2513344
  have htrace : WordTrace (prefixWord ++ tailWord_2513344) baseStart_2513344 baseEnd_2513344 := by
    simpa [prefixWord, tailWord_2513344, baseEnd_2513344] using wordTrace_append hprefix tailTrace_2513344
  have hstable : (prefixWord ++ tailWord_2513344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2513344).length < 2 ^ (prefixWord ++ tailWord_2513344).sum := by decide
  have hdescent : baseEnd_2513344 < baseStart_2513344 := by decide
  rcases family_descends (prefixWord ++ tailWord_2513344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2513375 : List Nat := [1, 1, 2, 3, 3, 3, 1, 3, 1, 3, 2]
def baseStart_2513375 : Nat := 118140960795 + 2513375 * 2 ^ 59
def prefixEnd_2513375 : Nat := 4983230072969 + 3 ^ 40 * 2513375 * 2
def baseEnd_2513375 : Nat := 1290569439994209142453705

theorem tailTrace_2513375 : CollatzResearch.WordTrace tailWord_2513375 prefixEnd_2513375 1290569439994209142453705 := by
  unfold tailWord_2513375
  simp only [CollatzResearch.WordTrace]
  refine ⟨91670317269479100120749579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61113544846319400080499719 91670317269479100120749579)
  ·
    refine ⟨137505475904218650181124369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91670317269479100120749579 137505475904218650181124369)
    ·
      refine ⟨103129106928163987635843277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137505475904218650181124369 103129106928163987635843277)
      ·
        refine ⟨38673415098061495363441229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103129106928163987635843277 38673415098061495363441229)
        ·
          refine ⟨14502530661773060761290461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38673415098061495363441229 14502530661773060761290461)
          ·
            refine ⟨5438448998164897785483923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14502530661773060761290461 5438448998164897785483923)
            ·
              refine ⟨8157673497247346678225885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5438448998164897785483923 8157673497247346678225885)
              ·
                refine ⟨3059127561467755004334707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8157673497247346678225885 3059127561467755004334707)
                ·
                  refine ⟨4588691342201632506502061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3059127561467755004334707 4588691342201632506502061)
                  ·
                    refine ⟨1720759253325612189938273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4588691342201632506502061 1720759253325612189938273)
                    ·
                      refine ⟨1290569439994209142453705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1720759253325612189938273 1290569439994209142453705)
                      ·
                        rfl

theorem cell23_2513375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 3, 1, 3, 2].length) (baseStart_2513375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2513375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2513375 prefixEnd_2513375 := by exact prefixLift 2513375
  have htrace : WordTrace (prefixWord ++ tailWord_2513375) baseStart_2513375 baseEnd_2513375 := by
    simpa [prefixWord, tailWord_2513375, baseEnd_2513375] using wordTrace_append hprefix tailTrace_2513375
  have hstable : (prefixWord ++ tailWord_2513375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2513375).length < 2 ^ (prefixWord ++ tailWord_2513375).sum := by decide
  have hdescent : baseEnd_2513375 < baseStart_2513375 := by decide
  rcases family_descends (prefixWord ++ tailWord_2513375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2513401 : List Nat := [1, 2, 1, 3, 1, 2, 4, 1, 2, 2, 4]
def baseStart_2513401 : Nat := 118140960795 + 2513401 * 2 ^ 59
def prefixEnd_2513401 : Nat := 4983230072969 + 3 ^ 40 * 2513401 * 2
def baseEnd_2513401 : Nat := 1290582790491226040728585

theorem tailTrace_2513401 : CollatzResearch.WordTrace tailWord_2513401 prefixEnd_2513401 1290582790491226040728585 := by
  unfold tailWord_2513401
  simp only [CollatzResearch.WordTrace]
  refine ⟨91671265567384906561196057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61114177044923271040797371 91671265567384906561196057)
  ·
    refine ⟨68753449175538679920897043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91671265567384906561196057 68753449175538679920897043)
    ·
      refine ⟨103130173763308019881345565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68753449175538679920897043 103130173763308019881345565)
      ·
        refine ⟨38673815161240507455504587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103130173763308019881345565 38673815161240507455504587)
        ·
          refine ⟨58010722741860761183256881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38673815161240507455504587 58010722741860761183256881)
          ·
            refine ⟨43508042056395570887442661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58010722741860761183256881 43508042056395570887442661)
            ·
              refine ⟨8157757885574169541395499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43508042056395570887442661 8157757885574169541395499)
              ·
                refine ⟨12236636828361254312093249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8157757885574169541395499 12236636828361254312093249)
                ·
                  refine ⟨9177477621270940734069937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12236636828361254312093249 9177477621270940734069937)
                  ·
                    refine ⟨6883108215953205550552453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9177477621270940734069937 6883108215953205550552453)
                    ·
                      refine ⟨1290582790491226040728585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6883108215953205550552453 1290582790491226040728585)
                      ·
                        rfl

theorem cell23_2513401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 1, 2, 2, 4].length) (baseStart_2513401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2513401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2513401 prefixEnd_2513401 := by exact prefixLift 2513401
  have htrace : WordTrace (prefixWord ++ tailWord_2513401) baseStart_2513401 baseEnd_2513401 := by
    simpa [prefixWord, tailWord_2513401, baseEnd_2513401] using wordTrace_append hprefix tailTrace_2513401
  have hstable : (prefixWord ++ tailWord_2513401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2513401).length < 2 ^ (prefixWord ++ tailWord_2513401).sum := by decide
  have hdescent : baseEnd_2513401 < baseStart_2513401 := by decide
  rcases family_descends (prefixWord ++ tailWord_2513401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2513512 : List Nat := [2, 1, 4, 3, 2, 1, 1, 1, 2, 4, 2]
def baseStart_2513512 : Nat := 118140960795 + 2513512 * 2 ^ 59
def prefixEnd_2513512 : Nat := 4983230072969 + 3 ^ 40 * 2513512 * 2
def baseEnd_2513512 : Nat := 1290639786843875106440575

theorem tailTrace_2513512 : CollatzResearch.WordTrace tailWord_2513512 prefixEnd_2513512 1290639786843875106440575 := by
  unfold tailWord_2513512
  simp only [CollatzResearch.WordTrace]
  refine ⟨45837657034991386259243395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61116876046655181678991193 45837657034991386259243395)
  ·
    refine ⟨68756485552487079388865093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45837657034991386259243395 68756485552487079388865093)
    ·
      refine ⟨12891841041091327385412205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68756485552487079388865093 12891841041091327385412205)
      ·
        refine ⟨4834440390409247769529577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12891841041091327385412205 4834440390409247769529577)
        ·
          refine ⟨3625830292806935827147183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4834440390409247769529577 3625830292806935827147183)
          ·
            refine ⟨5438745439210403740720775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3625830292806935827147183 5438745439210403740720775)
            ·
              refine ⟨8158118158815605611081163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5438745439210403740720775 8158118158815605611081163)
              ·
                refine ⟨12237177238223408416621745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8158118158815605611081163 12237177238223408416621745)
                ·
                  refine ⟨9177882928667556312466309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12237177238223408416621745 9177882928667556312466309)
                  ·
                    refine ⟨1720853049125166808587433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9177882928667556312466309 1720853049125166808587433)
                    ·
                      refine ⟨1290639786843875106440575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1720853049125166808587433 1290639786843875106440575)
                      ·
                        rfl

theorem cell23_2513512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 1, 2, 4, 2].length) (baseStart_2513512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2513512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2513512 prefixEnd_2513512 := by exact prefixLift 2513512
  have htrace : WordTrace (prefixWord ++ tailWord_2513512) baseStart_2513512 baseEnd_2513512 := by
    simpa [prefixWord, tailWord_2513512, baseEnd_2513512] using wordTrace_append hprefix tailTrace_2513512
  have hstable : (prefixWord ++ tailWord_2513512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2513512).length < 2 ^ (prefixWord ++ tailWord_2513512).sum := by decide
  have hdescent : baseEnd_2513512 < baseStart_2513512 := by decide
  rcases family_descends (prefixWord ++ tailWord_2513512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2513582 : List Nat := [4, 1, 4, 1, 1, 1, 1, 4, 1, 5]
def baseStart_2513582 : Nat := 118140960795 + 2513582 * 2 ^ 59
def prefixEnd_2513582 : Nat := 4983230072969 + 3 ^ 40 * 2513582 * 2
def baseEnd_2513582 : Nat := 430225243496563277521751

theorem tailTrace_2513582 : CollatzResearch.WordTrace tailWord_2513582 prefixEnd_2513582 430225243496563277521751 := by
  unfold tailWord_2513582
  simp only [CollatzResearch.WordTrace]
  refine ⟨11459733397466146809191875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61118578119819449649023333 11459733397466146809191875)
  ·
    refine ⟨17189600096199220213787813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11459733397466146809191875 17189600096199220213787813)
    ·
      refine ⟨3223050018037353790085215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17189600096199220213787813 3223050018037353790085215)
      ·
        refine ⟨4834575027056030685127823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3223050018037353790085215 4834575027056030685127823)
        ·
          refine ⟨7251862540584046027691735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4834575027056030685127823 7251862540584046027691735)
          ·
            refine ⟨10877793810876069041537603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7251862540584046027691735 10877793810876069041537603)
            ·
              refine ⟨16316690716314103562306405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10877793810876069041537603 16316690716314103562306405)
              ·
                refine ⟨3059379509308894417932451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16316690716314103562306405 3059379509308894417932451)
                ·
                  refine ⟨4589069263963341626898677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3059379509308894417932451 4589069263963341626898677)
                  ·
                    refine ⟨430225243496563277521751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4589069263963341626898677 430225243496563277521751)
                    ·
                      rfl

theorem cell23_2513582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_2513582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2513582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2513582 prefixEnd_2513582 := by exact prefixLift 2513582
  have htrace : WordTrace (prefixWord ++ tailWord_2513582) baseStart_2513582 baseEnd_2513582 := by
    simpa [prefixWord, tailWord_2513582, baseEnd_2513582] using wordTrace_append hprefix tailTrace_2513582
  have hstable : (prefixWord ++ tailWord_2513582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2513582).length < 2 ^ (prefixWord ++ tailWord_2513582).sum := by decide
  have hdescent : baseEnd_2513582 < baseStart_2513582 := by decide
  rcases family_descends (prefixWord ++ tailWord_2513582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2513608 : List Nat := [2, 1, 3, 1, 2, 5, 9]
def baseStart_2513608 : Nat := 118140960795 + 2513608 * 2 ^ 59
def prefixEnd_2513608 : Nat := 4983230072969 + 3 ^ 40 * 2513608 * 2
def baseEnd_2513608 : Nat := 15934433098601317664693

theorem tailTrace_2513608 : CollatzResearch.WordTrace tailWord_2513608 prefixEnd_2513608 15934433098601317664693 := by
  unfold tailWord_2513608
  simp only [CollatzResearch.WordTrace]
  refine ⟨45839407738817490456990739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61119210318423320609320985 45839407738817490456990739)
  ·
    refine ⟨68759111608226235685486109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45839407738817490456990739 68759111608226235685486109)
    ·
      refine ⟨25784666853084838382057291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68759111608226235685486109 25784666853084838382057291)
      ·
        refine ⟨38677000279627257573085937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25784666853084838382057291 38677000279627257573085937)
        ·
          refine ⟨29007750209720443179814453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38677000279627257573085937 29007750209720443179814453)
          ·
            refine ⟨2719476582161291548107605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29007750209720443179814453 2719476582161291548107605)
            ·
              refine ⟨15934433098601317664693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2719476582161291548107605 15934433098601317664693)
              ·
                rfl

theorem cell23_2513608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 9].length) (baseStart_2513608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2513608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2513608 prefixEnd_2513608 := by exact prefixLift 2513608
  have htrace : WordTrace (prefixWord ++ tailWord_2513608) baseStart_2513608 baseEnd_2513608 := by
    simpa [prefixWord, tailWord_2513608, baseEnd_2513608] using wordTrace_append hprefix tailTrace_2513608
  have hstable : (prefixWord ++ tailWord_2513608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2513608).length < 2 ^ (prefixWord ++ tailWord_2513608).sum := by decide
  have hdescent : baseEnd_2513608 < baseStart_2513608 := by decide
  rcases family_descends (prefixWord ++ tailWord_2513608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2513613 : List Nat := [1, 6, 2, 1, 3, 1, 1, 1, 3, 1, 3]
def baseStart_2513613 : Nat := 118140960795 + 2513613 * 2 ^ 59
def prefixEnd_2513613 : Nat := 4983230072969 + 3 ^ 40 * 2513613 * 2
def baseEnd_2513613 : Nat := 1290691648389979211277611

theorem tailTrace_2513613 : CollatzResearch.WordTrace tailWord_2513613 prefixEnd_2513613 1290691648389979211277611 := by
  unfold tailWord_2513613
  simp only [CollatzResearch.WordTrace]
  refine ⟨91678997842616866767913493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61119331895077911178608995 91678997842616866767913493)
  ·
    refine ⟨4297453023872665629745945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 91678997842616866767913493 4297453023872665629745945)
    ·
      refine ⟨3223089767904499222309459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4297453023872665629745945 3223089767904499222309459)
      ·
        refine ⟨4834634651856748833464189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3223089767904499222309459 4834634651856748833464189)
        ·
          refine ⟨1812987994446280812549071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4834634651856748833464189 1812987994446280812549071)
          ·
            refine ⟨2719481991669421218823607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1812987994446280812549071 2719481991669421218823607)
            ·
              refine ⟨4079222987504131828235411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2719481991669421218823607 4079222987504131828235411)
              ·
                refine ⟨6118834481256197742353117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4079222987504131828235411 6118834481256197742353117)
                ·
                  refine ⟨2294562930471074153382419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6118834481256197742353117 2294562930471074153382419)
                  ·
                    refine ⟨3441844395706611230073629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2294562930471074153382419 3441844395706611230073629)
                    ·
                      refine ⟨1290691648389979211277611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3441844395706611230073629 1290691648389979211277611)
                      ·
                        rfl

theorem cell23_2513613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 1, 1, 3, 1, 3].length) (baseStart_2513613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2513613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2513613 prefixEnd_2513613 := by exact prefixLift 2513613
  have htrace : WordTrace (prefixWord ++ tailWord_2513613) baseStart_2513613 baseEnd_2513613 := by
    simpa [prefixWord, tailWord_2513613, baseEnd_2513613] using wordTrace_append hprefix tailTrace_2513613
  have hstable : (prefixWord ++ tailWord_2513613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2513613).length < 2 ^ (prefixWord ++ tailWord_2513613).sum := by decide
  have hdescent : baseEnd_2513613 < baseStart_2513613 := by decide
  rcases family_descends (prefixWord ++ tailWord_2513613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2513653 : List Nat := [1, 3, 6, 1, 1, 1, 3, 1, 1, 1, 4]
def baseStart_2513653 : Nat := 118140960795 + 2513653 * 2 ^ 59
def prefixEnd_2513653 : Nat := 4983230072969 + 3 ^ 40 * 2513653 * 2
def baseEnd_2513653 : Nat := 1290712187616159054777427

theorem tailTrace_2513653 : CollatzResearch.WordTrace tailWord_2513653 prefixEnd_2513653 1290712187616159054777427 := by
  unfold tailWord_2513653
  simp only [CollatzResearch.WordTrace]
  refine ⟨91680456762471953599369613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61120304508314635732913075 91680456762471953599369613)
  ·
    refine ⟨34380171285926982599763605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91680456762471953599369613 34380171285926982599763605)
    ·
      refine ⟨1611570529027827309363919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 34380171285926982599763605 1611570529027827309363919)
      ·
        refine ⟨2417355793541740964045879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1611570529027827309363919 2417355793541740964045879)
        ·
          refine ⟨3626033690312611446068819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2417355793541740964045879 3626033690312611446068819)
          ·
            refine ⟨5439050535468917169103229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3626033690312611446068819 5439050535468917169103229)
            ·
              refine ⟨2039643950800843938413711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5439050535468917169103229 2039643950800843938413711)
              ·
                refine ⟨3059465926201265907620567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2039643950800843938413711 3059465926201265907620567)
                ·
                  refine ⟨4589198889301898861430851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3059465926201265907620567 4589198889301898861430851)
                  ·
                    refine ⟨6883798333952848292146277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4589198889301898861430851 6883798333952848292146277)
                    ·
                      refine ⟨1290712187616159054777427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6883798333952848292146277 1290712187616159054777427)
                      ·
                        rfl

theorem cell23_2513653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_2513653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2513653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2513653 prefixEnd_2513653 := by exact prefixLift 2513653
  have htrace : WordTrace (prefixWord ++ tailWord_2513653) baseStart_2513653 baseEnd_2513653 := by
    simpa [prefixWord, tailWord_2513653, baseEnd_2513653] using wordTrace_append hprefix tailTrace_2513653
  have hstable : (prefixWord ++ tailWord_2513653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2513653).length < 2 ^ (prefixWord ++ tailWord_2513653).sum := by decide
  have hdescent : baseEnd_2513653 < baseStart_2513653 := by decide
  rcases family_descends (prefixWord ++ tailWord_2513653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2513675 : List Nat := [1, 1, 1, 1, 5, 1, 1, 1, 5, 4, 2]
def baseStart_2513675 : Nat := 118140960795 + 2513675 * 2 ^ 59
def prefixEnd_2513675 : Nat := 4983230072969 + 3 ^ 40 * 2513675 * 2
def baseEnd_2513675 : Nat := 1290723484190557968702325

theorem tailTrace_2513675 : CollatzResearch.WordTrace tailWord_2513675 prefixEnd_2513675 1290723484190557968702325 := by
  unfold tailWord_2513675
  simp only [CollatzResearch.WordTrace]
  refine ⟨91681259168392251356670479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61120839445594834237780319 91681259168392251356670479)
  ·
    refine ⟨137521888752588377035005719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91681259168392251356670479 137521888752588377035005719)
    ·
      refine ⟨206282833128882565552508579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137521888752588377035005719 206282833128882565552508579)
      ·
        refine ⟨309424249693323848328762869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206282833128882565552508579 309424249693323848328762869)
        ·
          refine ⟨29008523408749110780821519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 309424249693323848328762869 29008523408749110780821519)
          ·
            refine ⟨43512785113123666171232279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29008523408749110780821519 43512785113123666171232279)
            ·
              refine ⟨65269177669685499256848419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43512785113123666171232279 65269177669685499256848419)
              ·
                refine ⟨97903766504528248885272629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65269177669685499256848419 97903766504528248885272629)
                ·
                  refine ⟨9178478109799523332994309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 97903766504528248885272629 9178478109799523332994309)
                  ·
                    refine ⟨1720964645587410624936433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9178478109799523332994309 1720964645587410624936433)
                    ·
                      refine ⟨1290723484190557968702325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1720964645587410624936433 1290723484190557968702325)
                      ·
                        rfl

theorem cell23_2513675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 5, 4, 2].length) (baseStart_2513675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2513675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2513675 prefixEnd_2513675 := by exact prefixLift 2513675
  have htrace : WordTrace (prefixWord ++ tailWord_2513675) baseStart_2513675 baseEnd_2513675 := by
    simpa [prefixWord, tailWord_2513675, baseEnd_2513675] using wordTrace_append hprefix tailTrace_2513675
  have hstable : (prefixWord ++ tailWord_2513675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2513675).length < 2 ^ (prefixWord ++ tailWord_2513675).sum := by decide
  have hdescent : baseEnd_2513675 < baseStart_2513675 := by decide
  rcases family_descends (prefixWord ++ tailWord_2513675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2513692 : List Nat := [2, 2, 3, 1, 1, 3, 1, 3, 1, 4, 2]
def baseStart_2513692 : Nat := 118140960795 + 2513692 * 2 ^ 59
def prefixEnd_2513692 : Nat := 4983230072969 + 3 ^ 40 * 2513692 * 2
def baseEnd_2513692 : Nat := 1290732213361684402189747

theorem tailTrace_2513692 : CollatzResearch.WordTrace tailWord_2513692 prefixEnd_2513692 1290732213361684402189747 := by
  unfold tailWord_2513692
  simp only [CollatzResearch.WordTrace]
  refine ⟨45840939604665331630019665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61121252806220442173359553 45840939604665331630019665)
  ·
    refine ⟨34380704703498998722514749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45840939604665331630019665 34380704703498998722514749)
    ·
      refine ⟨12892764263812124520943031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34380704703498998722514749 12892764263812124520943031)
      ·
        refine ⟨19339146395718186781414547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12892764263812124520943031 19339146395718186781414547)
        ·
          refine ⟨29008719593577280172121821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19339146395718186781414547 29008719593577280172121821)
          ·
            refine ⟨10878269847591480064545683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29008719593577280172121821 10878269847591480064545683)
            ·
              refine ⟨16317404771387220096818525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10878269847591480064545683 16317404771387220096818525)
              ·
                refine ⟨6119026789270207536306947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16317404771387220096818525 6119026789270207536306947)
                ·
                  refine ⟨9178540183905311304460421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6119026789270207536306947 9178540183905311304460421)
                  ·
                    refine ⟨1720976284482245869586329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9178540183905311304460421 1720976284482245869586329)
                    ·
                      refine ⟨1290732213361684402189747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1720976284482245869586329 1290732213361684402189747)
                      ·
                        rfl

theorem cell23_2513692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 3, 1, 4, 2].length) (baseStart_2513692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2513692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2513692 prefixEnd_2513692 := by exact prefixLift 2513692
  have htrace : WordTrace (prefixWord ++ tailWord_2513692) baseStart_2513692 baseEnd_2513692 := by
    simpa [prefixWord, tailWord_2513692, baseEnd_2513692] using wordTrace_append hprefix tailTrace_2513692
  have hstable : (prefixWord ++ tailWord_2513692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2513692).length < 2 ^ (prefixWord ++ tailWord_2513692).sum := by decide
  have hdescent : baseEnd_2513692 < baseStart_2513692 := by decide
  rcases family_descends (prefixWord ++ tailWord_2513692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2513726 : List Nat := [4, 2, 1, 2, 3, 1, 1, 1, 4, 2, 2]
def baseStart_2513726 : Nat := 118140960795 + 2513726 * 2 ^ 59
def prefixEnd_2513726 : Nat := 4983230072969 + 3 ^ 40 * 2513726 * 2
def baseEnd_2513726 : Nat := 1290749671703937269164591

theorem tailTrace_2513726 : CollatzResearch.WordTrace tailWord_2513726 prefixEnd_2513726 1290749671703937269164591 := by
  unfold tailWord_2513726
  simp only [CollatzResearch.WordTrace]
  refine ⟨11460389911400935883347129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61122079527471658044518021 11460389911400935883347129)
  ·
    refine ⟨8595292433550701912510347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11460389911400935883347129 8595292433550701912510347)
    ·
      refine ⟨12892938650326052868765521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8595292433550701912510347 12892938650326052868765521)
      ·
        refine ⟨9669703987744539651574141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12892938650326052868765521 9669703987744539651574141)
        ·
          refine ⟨3626138995404202369340303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9669703987744539651574141 3626138995404202369340303)
          ·
            refine ⟨5439208493106303554010455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3626138995404202369340303 5439208493106303554010455)
            ·
              refine ⟨8158812739659455331015683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5439208493106303554010455 8158812739659455331015683)
              ·
                refine ⟨12238219109489182996523525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8158812739659455331015683 12238219109489182996523525)
                ·
                  refine ⟨2294666083029221811848161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12238219109489182996523525 2294666083029221811848161)
                  ·
                    refine ⟨1720999562271916358886121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2294666083029221811848161 1720999562271916358886121)
                    ·
                      refine ⟨1290749671703937269164591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1720999562271916358886121 1290749671703937269164591)
                      ·
                        rfl

theorem cell23_2513726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 1, 4, 2, 2].length) (baseStart_2513726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2513726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2513726 prefixEnd_2513726 := by exact prefixLift 2513726
  have htrace : WordTrace (prefixWord ++ tailWord_2513726) baseStart_2513726 baseEnd_2513726 := by
    simpa [prefixWord, tailWord_2513726, baseEnd_2513726] using wordTrace_append hprefix tailTrace_2513726
  have hstable : (prefixWord ++ tailWord_2513726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2513726).length < 2 ^ (prefixWord ++ tailWord_2513726).sum := by decide
  have hdescent : baseEnd_2513726 < baseStart_2513726 := by decide
  rcases family_descends (prefixWord ++ tailWord_2513726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2513765 : List Nat := [1, 3, 1, 3, 1, 1, 4, 1, 1, 3, 4]
def baseStart_2513765 : Nat := 118140960795 + 2513765 * 2 ^ 59
def prefixEnd_2513765 : Nat := 4983230072969 + 3 ^ 40 * 2513765 * 2
def baseEnd_2513765 : Nat := 1290769697449462616576911

theorem tailTrace_2513765 : CollatzResearch.WordTrace tailWord_2513765 prefixEnd_2513765 1290769697449462616576911 := by
  unfold tailWord_2513765
  simp only [CollatzResearch.WordTrace]
  refine ⟨91684541738066196727446749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61123027825377464484964499 91684541738066196727446749)
  ·
    refine ⟨34381703151774823772792531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91684541738066196727446749 34381703151774823772792531)
    ·
      refine ⟨51572554727662235659188797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34381703151774823772792531 51572554727662235659188797)
      ·
        refine ⟨19339708022873338372195799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51572554727662235659188797 19339708022873338372195799)
        ·
          refine ⟨29009562034310007558293699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19339708022873338372195799 29009562034310007558293699)
          ·
            refine ⟨43514343051465011337440549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29009562034310007558293699 43514343051465011337440549)
            ·
              refine ⟨8158939322149689625770103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43514343051465011337440549 8158939322149689625770103)
              ·
                refine ⟨12238408983224534438655155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8158939322149689625770103 12238408983224534438655155)
                ·
                  refine ⟨18357613474836801657982733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12238408983224534438655155 18357613474836801657982733)
                  ·
                    refine ⟨6884105053063800621743525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18357613474836801657982733 6884105053063800621743525)
                    ·
                      refine ⟨1290769697449462616576911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6884105053063800621743525 1290769697449462616576911)
                      ·
                        rfl

theorem cell23_2513765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 1, 1, 3, 4].length) (baseStart_2513765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2513765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2513765 prefixEnd_2513765 := by exact prefixLift 2513765
  have htrace : WordTrace (prefixWord ++ tailWord_2513765) baseStart_2513765 baseEnd_2513765 := by
    simpa [prefixWord, tailWord_2513765, baseEnd_2513765] using wordTrace_append hprefix tailTrace_2513765
  have hstable : (prefixWord ++ tailWord_2513765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2513765).length < 2 ^ (prefixWord ++ tailWord_2513765).sum := by decide
  have hdescent : baseEnd_2513765 < baseStart_2513765 := by decide
  rcases family_descends (prefixWord ++ tailWord_2513765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2513775 : List Nat := [1, 1, 2, 1, 3, 1, 1, 4, 5, 4]
def baseStart_2513775 : Nat := 118140960795 + 2513775 * 2 ^ 59
def prefixEnd_2513775 : Nat := 4983230072969 + 3 ^ 40 * 2513775 * 2
def baseEnd_2513775 : Nat := 430258277418669192483955

theorem tailTrace_2513775 : CollatzResearch.WordTrace tailWord_2513775 prefixEnd_2513775 430258277418669192483955 := by
  unfold tailWord_2513775
  simp only [CollatzResearch.WordTrace]
  refine ⟨91684906468029968435310779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61123270978686645623540519 91684906468029968435310779)
  ·
    refine ⟨137527359702044952652966169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91684906468029968435310779 137527359702044952652966169)
    ·
      refine ⟨103145519776533714489724627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137527359702044952652966169 103145519776533714489724627)
      ·
        refine ⟨154718279664800571734586941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103145519776533714489724627 154718279664800571734586941)
        ·
          refine ⟨58019354874300214400470103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 154718279664800571734586941 58019354874300214400470103)
          ·
            refine ⟨87029032311450321600705155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58019354874300214400470103 87029032311450321600705155)
            ·
              refine ⟨130543548467175482401057733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87029032311450321600705155 130543548467175482401057733)
              ·
                refine ⟨24476915337595402950198325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 130543548467175482401057733 24476915337595402950198325)
                ·
                  refine ⟨2294710812899569026581093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24476915337595402950198325 2294710812899569026581093)
                  ·
                    refine ⟨430258277418669192483955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2294710812899569026581093 430258277418669192483955)
                    ·
                      rfl

theorem cell23_2513775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 4, 5, 4].length) (baseStart_2513775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2513775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2513775 prefixEnd_2513775 := by exact prefixLift 2513775
  have htrace : WordTrace (prefixWord ++ tailWord_2513775) baseStart_2513775 baseEnd_2513775 := by
    simpa [prefixWord, tailWord_2513775, baseEnd_2513775] using wordTrace_append hprefix tailTrace_2513775
  have hstable : (prefixWord ++ tailWord_2513775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2513775).length < 2 ^ (prefixWord ++ tailWord_2513775).sum := by decide
  have hdescent : baseEnd_2513775 < baseStart_2513775 := by decide
  rcases family_descends (prefixWord ++ tailWord_2513775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2513794 : List Nat := [3, 4, 2, 2, 2, 1, 2, 1, 2, 2, 2]
def baseStart_2513794 : Nat := 118140960795 + 2513794 * 2 ^ 59
def prefixEnd_2513794 : Nat := 4983230072969 + 3 ^ 40 * 2513794 * 2
def baseEnd_2513794 : Nat := 1290784588388443003114279

theorem tailTrace_2513794 : CollatzResearch.WordTrace tailWord_2513794 prefixEnd_2513794 1290784588388443003114279 := by
  unfold tailWord_2513794
  simp only [CollatzResearch.WordTrace]
  refine ⟨22921399863740283670063109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61123732969974089786834957 22921399863740283670063109)
  ·
    refine ⟨4297762474451303188136833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22921399863740283670063109 4297762474451303188136833)
    ·
      refine ⟨3223321855838477391102625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4297762474451303188136833 3223321855838477391102625)
      ·
        refine ⟨2417491391878858043326969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3223321855838477391102625 2417491391878858043326969)
        ·
          refine ⟨1813118543909143532495227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2417491391878858043326969 1813118543909143532495227)
          ·
            refine ⟨2719677815863715298742841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1813118543909143532495227 2719677815863715298742841)
            ·
              refine ⟨2039758361897786474057131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2719677815863715298742841 2039758361897786474057131)
              ·
                refine ⟨3059637542846679711085697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2039758361897786474057131 3059637542846679711085697)
                ·
                  refine ⟨2294728157135009783314273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3059637542846679711085697 2294728157135009783314273)
                  ·
                    refine ⟨1721046117851257337485705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2294728157135009783314273 1721046117851257337485705)
                    ·
                      refine ⟨1290784588388443003114279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1721046117851257337485705 1290784588388443003114279)
                      ·
                        rfl

theorem cell23_2513794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_2513794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2513794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2513794 prefixEnd_2513794 := by exact prefixLift 2513794
  have htrace : WordTrace (prefixWord ++ tailWord_2513794) baseStart_2513794 baseEnd_2513794 := by
    simpa [prefixWord, tailWord_2513794, baseEnd_2513794] using wordTrace_append hprefix tailTrace_2513794
  have hstable : (prefixWord ++ tailWord_2513794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2513794).length < 2 ^ (prefixWord ++ tailWord_2513794).sum := by decide
  have hdescent : baseEnd_2513794 < baseStart_2513794 := by decide
  rcases family_descends (prefixWord ++ tailWord_2513794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2513842 : List Nat := [3, 2, 1, 1, 1, 1, 1, 1, 5, 5, 2]
def baseStart_2513842 : Nat := 118140960795 + 2513842 * 2 ^ 59
def prefixEnd_2513842 : Nat := 4983230072969 + 3 ^ 40 * 2513842 * 2
def baseEnd_2513842 : Nat := 1290809235459858815314057

theorem tailTrace_2513842 : CollatzResearch.WordTrace tailWord_2513842 prefixEnd_2513842 1290809235459858815314057 := by
  unfold tailWord_2513842
  simp only [CollatzResearch.WordTrace]
  refine ⟨22921837539696809719499945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61124900105858159251999853 22921837539696809719499945)
  ·
    refine ⟨17191378154772607289624959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22921837539696809719499945 17191378154772607289624959)
    ·
      refine ⟨25787067232158910934437439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17191378154772607289624959 25787067232158910934437439)
      ·
        refine ⟨38680600848238366401656159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25787067232158910934437439 38680600848238366401656159)
        ·
          refine ⟨58020901272357549602484239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38680600848238366401656159 58020901272357549602484239)
          ·
            refine ⟨87031351908536324403726359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58020901272357549602484239 87031351908536324403726359)
            ·
              refine ⟨130547027862804486605589539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87031351908536324403726359 130547027862804486605589539)
              ·
                refine ⟨195820541794206729908384309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 130547027862804486605589539 195820541794206729908384309)
                ·
                  refine ⟨18358175793206880928911029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 195820541794206729908384309 18358175793206880928911029)
                  ·
                    refine ⟨1721078980613145087085409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18358175793206880928911029 1721078980613145087085409)
                    ·
                      refine ⟨1290809235459858815314057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1721078980613145087085409 1290809235459858815314057)
                      ·
                        rfl

theorem cell23_2513842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 5, 5, 2].length) (baseStart_2513842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2513842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2513842 prefixEnd_2513842 := by exact prefixLift 2513842
  have htrace : WordTrace (prefixWord ++ tailWord_2513842) baseStart_2513842 baseEnd_2513842 := by
    simpa [prefixWord, tailWord_2513842, baseEnd_2513842] using wordTrace_append hprefix tailTrace_2513842
  have hstable : (prefixWord ++ tailWord_2513842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2513842).length < 2 ^ (prefixWord ++ tailWord_2513842).sum := by decide
  have hdescent : baseEnd_2513842 < baseStart_2513842 := by decide
  rcases family_descends (prefixWord ++ tailWord_2513842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2513872 : List Nat := [2, 1, 1, 1, 1, 2, 3, 6, 1, 1, 4]
def baseStart_2513872 : Nat := 118140960795 + 2513872 * 2 ^ 59
def prefixEnd_2513872 : Nat := 4983230072969 + 3 ^ 40 * 2513872 * 2
def baseEnd_2513872 : Nat := 1290824639879493697938919

theorem tailTrace_2513872 : CollatzResearch.WordTrace tailWord_2513872 prefixEnd_2513872 1290824639879493697938919 := by
  unfold tailWord_2513872
  simp only [CollatzResearch.WordTrace]
  refine ⟨45844222174339277000795935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61125629565785702667727913 45844222174339277000795935)
  ·
    refine ⟨68766333261508915501193903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45844222174339277000795935 68766333261508915501193903)
    ·
      refine ⟨103149499892263373251790855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68766333261508915501193903 103149499892263373251790855)
      ·
        refine ⟨154724249838395059877686283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103149499892263373251790855 154724249838395059877686283)
        ·
          refine ⟨232086374757592589816529425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154724249838395059877686283 232086374757592589816529425)
          ·
            refine ⟨174064781068194442362397069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 232086374757592589816529425 174064781068194442362397069)
            ·
              refine ⟨65274292900572915885898901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 174064781068194442362397069 65274292900572915885898901)
              ·
                refine ⟨3059732479714355432151511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 65274292900572915885898901 3059732479714355432151511)
                ·
                  refine ⟨4589598719571533148227267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3059732479714355432151511 4589598719571533148227267)
                  ·
                    refine ⟨6884398079357299722340901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4589598719571533148227267 6884398079357299722340901)
                    ·
                      refine ⟨1290824639879493697938919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6884398079357299722340901 1290824639879493697938919)
                      ·
                        rfl

theorem cell23_2513872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 6, 1, 1, 4].length) (baseStart_2513872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2513872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2513872 prefixEnd_2513872 := by exact prefixLift 2513872
  have htrace : WordTrace (prefixWord ++ tailWord_2513872) baseStart_2513872 baseEnd_2513872 := by
    simpa [prefixWord, tailWord_2513872, baseEnd_2513872] using wordTrace_append hprefix tailTrace_2513872
  have hstable : (prefixWord ++ tailWord_2513872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2513872).length < 2 ^ (prefixWord ++ tailWord_2513872).sum := by decide
  have hdescent : baseEnd_2513872 < baseStart_2513872 := by decide
  rcases family_descends (prefixWord ++ tailWord_2513872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2513876 : List Nat := [2, 4, 1, 2, 1, 2, 3, 1, 2, 3, 2]
def baseStart_2513876 : Nat := 118140960795 + 2513876 * 2 ^ 59
def prefixEnd_2513876 : Nat := 4983230072969 + 3 ^ 40 * 2513876 * 2
def baseEnd_2513876 : Nat := 1290826693802111682288901

theorem tailTrace_2513876 : CollatzResearch.WordTrace tailWord_2513876 prefixEnd_2513876 1290826693802111682288901 := by
  unfold tailWord_2513876
  simp only [CollatzResearch.WordTrace]
  refine ⟨45844295120332031342368741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61125726827109375123158321 45844295120332031342368741)
  ·
    refine ⟨8595805335062255876694139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45844295120332031342368741 8595805335062255876694139)
    ·
      refine ⟨12893708002593383815041209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8595805335062255876694139 12893708002593383815041209)
      ·
        refine ⟨9670281001945037861280907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12893708002593383815041209 9670281001945037861280907)
        ·
          refine ⟨14505421502917556791921361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9670281001945037861280907 14505421502917556791921361)
          ·
            refine ⟨10879066127188167593941021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14505421502917556791921361 10879066127188167593941021)
            ·
              refine ⟨4079649797695562847727883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10879066127188167593941021 4079649797695562847727883)
              ·
                refine ⟨6119474696543344271591825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4079649797695562847727883 6119474696543344271591825)
                ·
                  refine ⟨4589606022407508203693869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6119474696543344271591825 4589606022407508203693869)
                  ·
                    refine ⟨1721102258402815576385201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4589606022407508203693869 1721102258402815576385201)
                    ·
                      refine ⟨1290826693802111682288901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1721102258402815576385201 1290826693802111682288901)
                      ·
                        rfl

theorem cell23_2513876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 3, 1, 2, 3, 2].length) (baseStart_2513876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2513876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2513876 prefixEnd_2513876 := by exact prefixLift 2513876
  have htrace : WordTrace (prefixWord ++ tailWord_2513876) baseStart_2513876 baseEnd_2513876 := by
    simpa [prefixWord, tailWord_2513876, baseEnd_2513876] using wordTrace_append hprefix tailTrace_2513876
  have hstable : (prefixWord ++ tailWord_2513876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2513876).length < 2 ^ (prefixWord ++ tailWord_2513876).sum := by decide
  have hdescent : baseEnd_2513876 < baseStart_2513876 := by decide
  rcases family_descends (prefixWord ++ tailWord_2513876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2513882 : List Nat := [3, 1, 1, 2, 4, 1, 2, 2, 1, 6]
def baseStart_2513882 : Nat := 118140960795 + 2513882 * 2 ^ 59
def prefixEnd_2513882 : Nat := 4983230072969 + 3 ^ 40 * 2513882 * 2
def baseEnd_2513882 : Nat := 430276591562012886271291

theorem tailTrace_2513882 : CollatzResearch.WordTrace tailWord_2513882 prefixEnd_2513882 430276591562012886271291 := by
  unfold tailWord_2513882
  simp only [CollatzResearch.WordTrace]
  refine ⟨22922202269660581427363975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61125872719094883806303933 22922202269660581427363975)
  ·
    refine ⟨34383303404490872141045963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22922202269660581427363975 34383303404490872141045963)
    ·
      refine ⟨51574955106736308211568945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34383303404490872141045963 51574955106736308211568945)
      ·
        refine ⟨38681216330052231158676709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51574955106736308211568945 38681216330052231158676709)
        ·
          refine ⟨7252728061884793342251883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38681216330052231158676709 7252728061884793342251883)
          ·
            refine ⟨10879092092827190013377825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7252728061884793342251883 10879092092827190013377825)
            ·
              refine ⟨8159319069620392510033369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10879092092827190013377825 8159319069620392510033369)
              ·
                refine ⟨6119489302215294382525027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8159319069620392510033369 6119489302215294382525027)
                ·
                  refine ⟨9179233953322941573787541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6119489302215294382525027 9179233953322941573787541)
                  ·
                    refine ⟨430276591562012886271291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9179233953322941573787541 430276591562012886271291)
                    ·
                      rfl

theorem cell23_2513882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 2, 1, 6].length) (baseStart_2513882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2513882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2513882 prefixEnd_2513882 := by exact prefixLift 2513882
  have htrace : WordTrace (prefixWord ++ tailWord_2513882) baseStart_2513882 baseEnd_2513882 := by
    simpa [prefixWord, tailWord_2513882, baseEnd_2513882] using wordTrace_append hprefix tailTrace_2513882
  have hstable : (prefixWord ++ tailWord_2513882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2513882).length < 2 ^ (prefixWord ++ tailWord_2513882).sum := by decide
  have hdescent : baseEnd_2513882 < baseStart_2513882 := by decide
  rcases family_descends (prefixWord ++ tailWord_2513882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2513889 : List Nat := [1, 2, 3, 1, 2, 1, 1, 1, 7, 2, 2]
def baseStart_2513889 : Nat := 118140960795 + 2513889 * 2 ^ 59
def prefixEnd_2513889 : Nat := 4983230072969 + 3 ^ 40 * 2513889 * 2
def baseEnd_2513889 : Nat := 1290833369050620131426341

theorem tailTrace_2513889 : CollatzResearch.WordTrace tailWord_2513889 prefixEnd_2513889 1290833369050620131426341 := by
  unfold tailWord_2513889
  simp only [CollatzResearch.WordTrace]
  refine ⟨91689064389616965904960721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61126042926411310603307147 91689064389616965904960721)
  ·
    refine ⟨68766798292212724428720541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91689064389616965904960721 68766798292212724428720541)
    ·
      refine ⟨25787549359579771660770203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68766798292212724428720541 25787549359579771660770203)
      ·
        refine ⟨38681324039369657491155305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25787549359579771660770203 38681324039369657491155305)
        ·
          refine ⟨29010993029527243118366479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38681324039369657491155305 29010993029527243118366479)
          ·
            refine ⟨43516489544290864677549719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29010993029527243118366479 43516489544290864677549719)
            ·
              refine ⟨65274734316436297016324579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43516489544290864677549719 65274734316436297016324579)
              ·
                refine ⟨97912101474654445524486869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65274734316436297016324579 97912101474654445524486869)
                ·
                  refine ⟨2294814878312213566980161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 97912101474654445524486869 2294814878312213566980161)
                  ·
                    refine ⟨1721111158734160175235121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2294814878312213566980161 1721111158734160175235121)
                    ·
                      refine ⟨1290833369050620131426341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1721111158734160175235121 1290833369050620131426341)
                      ·
                        rfl

theorem cell23_2513889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 7, 2, 2].length) (baseStart_2513889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2513889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2513889 prefixEnd_2513889 := by exact prefixLift 2513889
  have htrace : WordTrace (prefixWord ++ tailWord_2513889) baseStart_2513889 baseEnd_2513889 := by
    simpa [prefixWord, tailWord_2513889, baseEnd_2513889] using wordTrace_append hprefix tailTrace_2513889
  have hstable : (prefixWord ++ tailWord_2513889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2513889).length < 2 ^ (prefixWord ++ tailWord_2513889).sum := by decide
  have hdescent : baseEnd_2513889 < baseStart_2513889 := by decide
  rcases family_descends (prefixWord ++ tailWord_2513889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2513892 : List Nat := [2, 3, 1, 1, 1, 1, 2, 2, 5, 2, 3]
def baseStart_2513892 : Nat := 118140960795 + 2513892 * 2 ^ 59
def prefixEnd_2513892 : Nat := 4983230072969 + 3 ^ 40 * 2513892 * 2
def baseEnd_2513892 : Nat := 1290834909492583619688827

theorem tailTrace_2513892 : CollatzResearch.WordTrace tailWord_2513892 prefixEnd_2513892 1290834909492583619688827 := by
  unfold tailWord_2513892
  simp only [CollatzResearch.WordTrace]
  refine ⟨45844586904303048708659965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61126115872404064944879953 45844586904303048708659965)
  ·
    refine ⟨17191720089113643265747487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45844586904303048708659965 17191720089113643265747487)
    ·
      refine ⟨25787580133670464898621231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17191720089113643265747487 25787580133670464898621231)
      ·
        refine ⟨38681370200505697347931847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25787580133670464898621231 38681370200505697347931847)
        ·
          refine ⟨58022055300758546021897771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38681370200505697347931847 58022055300758546021897771)
          ·
            refine ⟨87033082951137819032846657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58022055300758546021897771 87033082951137819032846657)
            ·
              refine ⟨65274812213353364274634993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87033082951137819032846657 65274812213353364274634993)
              ·
                refine ⟨48956109160015023205976245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65274812213353364274634993 48956109160015023205976245)
                ·
                  refine ⟨4589635233751408425560273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 48956109160015023205976245 4589635233751408425560273)
                  ·
                    refine ⟨3442226425313556319170205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4589635233751408425560273 3442226425313556319170205)
                    ·
                      refine ⟨1290834909492583619688827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3442226425313556319170205 1290834909492583619688827)
                      ·
                        rfl

theorem cell23_2513892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 5, 2, 3].length) (baseStart_2513892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2513892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2513892 prefixEnd_2513892 := by exact prefixLift 2513892
  have htrace : WordTrace (prefixWord ++ tailWord_2513892) baseStart_2513892 baseEnd_2513892 := by
    simpa [prefixWord, tailWord_2513892, baseEnd_2513892] using wordTrace_append hprefix tailTrace_2513892
  have hstable : (prefixWord ++ tailWord_2513892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2513892).length < 2 ^ (prefixWord ++ tailWord_2513892).sum := by decide
  have hdescent : baseEnd_2513892 < baseStart_2513892 := by decide
  rcases family_descends (prefixWord ++ tailWord_2513892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2513916 : List Nat := [2, 2, 2, 1, 2, 4, 3, 1, 2, 4]
def baseStart_2513916 : Nat := 118140960795 + 2513916 * 2 ^ 59
def prefixEnd_2513916 : Nat := 4983230072969 + 3 ^ 40 * 2513916 * 2
def baseEnd_2513916 : Nat := 430282411009430508596239

theorem tailTrace_2513916 : CollatzResearch.WordTrace tailWord_2513916 prefixEnd_2513916 430282411009430508596239 := by
  unfold tailWord_2513916
  simp only [CollatzResearch.WordTrace]
  refine ⟨45845024580259574758096801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61126699440346099677462401 45845024580259574758096801)
  ·
    refine ⟨34383768435194681068572601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45845024580259574758096801 34383768435194681068572601)
    ·
      refine ⟨25787826326396010801429451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34383768435194681068572601 25787826326396010801429451)
      ·
        refine ⟨38681739489594016202144177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25787826326396010801429451 38681739489594016202144177)
        ·
          refine ⟨29011304617195512151608133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38681739489594016202144177 29011304617195512151608133)
          ·
            refine ⟨5439619615724158528426525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29011304617195512151608133 5439619615724158528426525)
            ·
              refine ⟨2039857355896559448159947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5439619615724158528426525 2039857355896559448159947)
              ·
                refine ⟨3059786033844839172239921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2039857355896559448159947 3059786033844839172239921)
                ·
                  refine ⟨2294839525383629379179941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3059786033844839172239921 2294839525383629379179941)
                  ·
                    refine ⟨430282411009430508596239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2294839525383629379179941 430282411009430508596239)
                    ·
                      rfl

theorem cell23_2513916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 3, 1, 2, 4].length) (baseStart_2513916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2513916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2513916 prefixEnd_2513916 := by exact prefixLift 2513916
  have htrace : WordTrace (prefixWord ++ tailWord_2513916) baseStart_2513916 baseEnd_2513916 := by
    simpa [prefixWord, tailWord_2513916, baseEnd_2513916] using wordTrace_append hprefix tailTrace_2513916
  have hstable : (prefixWord ++ tailWord_2513916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2513916).length < 2 ^ (prefixWord ++ tailWord_2513916).sum := by decide
  have hdescent : baseEnd_2513916 < baseStart_2513916 := by decide
  rcases family_descends (prefixWord ++ tailWord_2513916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2513956 : List Nat := [2, 3, 1, 4, 1, 1, 2, 1, 4, 1, 3]
def baseStart_2513956 : Nat := 118140960795 + 2513956 * 2 ^ 59
def prefixEnd_2513956 : Nat := 4983230072969 + 3 ^ 40 * 2513956 * 2
def baseEnd_2513956 : Nat := 1290867772254471369288533

theorem tailTrace_2513956 : CollatzResearch.WordTrace tailWord_2513956 prefixEnd_2513956 1290867772254471369288533 := by
  unfold tailWord_2513956
  simp only [CollatzResearch.WordTrace]
  refine ⟨45845754040187118173824861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61127672053582824231766481 45845754040187118173824861)
  ·
    refine ⟨17192157765070169315184323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45845754040187118173824861 17192157765070169315184323)
    ·
      refine ⟨25788236647605253972776485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17192157765070169315184323 25788236647605253972776485)
      ·
        refine ⟨4835294371425985119895591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25788236647605253972776485 4835294371425985119895591)
        ·
          refine ⟨7252941557138977679843387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4835294371425985119895591 7252941557138977679843387)
          ·
            refine ⟨10879412335708466519765081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7252941557138977679843387 10879412335708466519765081)
            ·
              refine ⟨8159559251781349889823811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10879412335708466519765081 8159559251781349889823811)
              ·
                refine ⟨12239338877672024834735717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8159559251781349889823811 12239338877672024834735717)
                ·
                  refine ⟨2294876039563504656512947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12239338877672024834735717 2294876039563504656512947)
                  ·
                    refine ⟨3442314059345256984769421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2294876039563504656512947 3442314059345256984769421)
                    ·
                      refine ⟨1290867772254471369288533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3442314059345256984769421 1290867772254471369288533)
                      ·
                        rfl

theorem cell23_2513956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_2513956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2513956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2513956 prefixEnd_2513956 := by exact prefixLift 2513956
  have htrace : WordTrace (prefixWord ++ tailWord_2513956) baseStart_2513956 baseEnd_2513956 := by
    simpa [prefixWord, tailWord_2513956, baseEnd_2513956] using wordTrace_append hprefix tailTrace_2513956
  have hstable : (prefixWord ++ tailWord_2513956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2513956).length < 2 ^ (prefixWord ++ tailWord_2513956).sum := by decide
  have hdescent : baseEnd_2513956 < baseStart_2513956 := by decide
  rcases family_descends (prefixWord ++ tailWord_2513956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2513966 : List Nat := [4, 1, 3, 1, 1, 1, 2, 2, 3, 3, 2]
def baseStart_2513966 : Nat := 118140960795 + 2513966 * 2 ^ 59
def prefixEnd_2513966 : Nat := 4983230072969 + 3 ^ 40 * 2513966 * 2
def baseEnd_2513966 : Nat := 1290872907061016330163487

theorem tailTrace_2513966 : CollatzResearch.WordTrace tailWord_2513966 prefixEnd_2513966 1290872907061016330163487 := by
  unfold tailWord_2513966
  simp only [CollatzResearch.WordTrace]
  refine ⟨11461484101292251006939219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61127915206892005370342501 11461484101292251006939219)
  ·
    refine ⟨17192226151938376510408829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11461484101292251006939219 17192226151938376510408829)
    ·
      refine ⟨6447084806976891191403311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17192226151938376510408829 6447084806976891191403311)
      ·
        refine ⟨9670627210465336787104967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6447084806976891191403311 9670627210465336787104967)
        ·
          refine ⟨14505940815698005180657451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9670627210465336787104967 14505940815698005180657451)
          ·
            refine ⟨21758911223547007770986177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14505940815698005180657451 21758911223547007770986177)
            ·
              refine ⟨16319183417660255828239633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21758911223547007770986177 16319183417660255828239633)
              ·
                refine ⟨12239387563245191871179725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16319183417660255828239633 12239387563245191871179725)
                ·
                  refine ⟨4589770336216946951692397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12239387563245191871179725 4589770336216946951692397)
                  ·
                    refine ⟨1721163876081355106884649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4589770336216946951692397 1721163876081355106884649)
                    ·
                      refine ⟨1290872907061016330163487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1721163876081355106884649 1290872907061016330163487)
                      ·
                        rfl

theorem cell23_2513966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 2, 3, 3, 2].length) (baseStart_2513966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2513966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2513966 prefixEnd_2513966 := by exact prefixLift 2513966
  have htrace : WordTrace (prefixWord ++ tailWord_2513966) baseStart_2513966 baseEnd_2513966 := by
    simpa [prefixWord, tailWord_2513966, baseEnd_2513966] using wordTrace_append hprefix tailTrace_2513966
  have hstable : (prefixWord ++ tailWord_2513966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2513966).length < 2 ^ (prefixWord ++ tailWord_2513966).sum := by decide
  have hdescent : baseEnd_2513966 < baseStart_2513966 := by decide
  rcases family_descends (prefixWord ++ tailWord_2513966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2514029 : List Nat := [1, 5, 1, 1, 2, 2, 1, 1, 1, 5, 3]
def baseStart_2514029 : Nat := 118140960795 + 2514029 * 2 ^ 59
def prefixEnd_2514029 : Nat := 4983230072969 + 3 ^ 40 * 2514029 * 2
def baseEnd_2514029 : Nat := 1290905256342249583675697

theorem tailTrace_2514029 : CollatzResearch.WordTrace tailWord_2514029 prefixEnd_2514029 1290905256342249583675697 := by
  unfold tailWord_2514029
  simp only [CollatzResearch.WordTrace]
  refine ⟨91694170609109769815057141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61129447072739846543371427 91694170609109769815057141)
  ·
    refine ⟨8596328494604040920161607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 91694170609109769815057141 8596328494604040920161607)
    ·
      refine ⟨12894492741906061380242411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8596328494604040920161607 12894492741906061380242411)
      ·
        refine ⟨19341739112859092070363617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12894492741906061380242411 19341739112859092070363617)
        ·
          refine ⟨14506304334644319052772713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19341739112859092070363617 14506304334644319052772713)
          ·
            refine ⟨10879728250983239289579535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14506304334644319052772713 10879728250983239289579535)
            ·
              refine ⟨16319592376474858934369303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10879728250983239289579535 16319592376474858934369303)
              ·
                refine ⟨24479388564712288401553955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16319592376474858934369303 24479388564712288401553955)
                ·
                  refine ⟨36719082847068432602330933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24479388564712288401553955 36719082847068432602330933)
                  ·
                    refine ⟨3442414016912665556468525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36719082847068432602330933 3442414016912665556468525)
                    ·
                      refine ⟨1290905256342249583675697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3442414016912665556468525 1290905256342249583675697)
                      ·
                        rfl

theorem cell23_2514029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 1, 1, 5, 3].length) (baseStart_2514029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2514029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2514029 prefixEnd_2514029 := by exact prefixLift 2514029
  have htrace : WordTrace (prefixWord ++ tailWord_2514029) baseStart_2514029 baseEnd_2514029 := by
    simpa [prefixWord, tailWord_2514029, baseEnd_2514029] using wordTrace_append hprefix tailTrace_2514029
  have hstable : (prefixWord ++ tailWord_2514029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2514029).length < 2 ^ (prefixWord ++ tailWord_2514029).sum := by decide
  have hdescent : baseEnd_2514029 < baseStart_2514029 := by decide
  rcases family_descends (prefixWord ++ tailWord_2514029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2514032 : List Nat := [2, 1, 1, 1, 5, 1, 2, 2, 1, 7]
def baseStart_2514032 : Nat := 118140960795 + 2514032 * 2 ^ 59
def prefixEnd_2514032 : Nat := 4983230072969 + 3 ^ 40 * 2514032 * 2
def baseEnd_2514032 : Nat := 430302265594737690646061

theorem tailTrace_2514032 : CollatzResearch.WordTrace tailWord_2514032 prefixEnd_2514032 430302265594737690646061 := by
  unfold tailWord_2514032
  simp only [CollatzResearch.WordTrace]
  refine ⟨45847140014049450663708175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61129520018732600884944233 45847140014049450663708175)
  ·
    refine ⟨68770710021074175995562263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45847140014049450663708175 68770710021074175995562263)
    ·
      refine ⟨103156065031611263993343395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68770710021074175995562263 103156065031611263993343395)
      ·
        refine ⟨154734097547416895990015093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103156065031611263993343395 154734097547416895990015093)
        ·
          refine ⟨14506321645070333999063915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 154734097547416895990015093 14506321645070333999063915)
          ·
            refine ⟨21759482467605500998595873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14506321645070333999063915 21759482467605500998595873)
            ·
              refine ⟨16319611850704125748946905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21759482467605500998595873 16319611850704125748946905)
              ·
                refine ⟨12239708888028094311710179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16319611850704125748946905 12239708888028094311710179)
                ·
                  refine ⟨18359563332042141467565269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12239708888028094311710179 18359563332042141467565269)
                  ·
                    refine ⟨430302265594737690646061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18359563332042141467565269 430302265594737690646061)
                    ·
                      rfl

theorem cell23_2514032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 2, 1, 7].length) (baseStart_2514032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2514032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2514032 prefixEnd_2514032 := by exact prefixLift 2514032
  have htrace : WordTrace (prefixWord ++ tailWord_2514032) baseStart_2514032 baseEnd_2514032 := by
    simpa [prefixWord, tailWord_2514032, baseEnd_2514032] using wordTrace_append hprefix tailTrace_2514032
  have hstable : (prefixWord ++ tailWord_2514032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2514032).length < 2 ^ (prefixWord ++ tailWord_2514032).sum := by decide
  have hdescent : baseEnd_2514032 < baseStart_2514032 := by decide
  rcases family_descends (prefixWord ++ tailWord_2514032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2514039 : List Nat := [1, 1, 3, 1, 1, 4, 1, 2, 2, 5, 2]
def baseStart_2514039 : Nat := 118140960795 + 2514039 * 2 ^ 59
def prefixEnd_2514039 : Nat := 4983230072969 + 3 ^ 40 * 2514039 * 2
def baseEnd_2514039 : Nat := 1290910391148794544550651

theorem tailTrace_2514039 : CollatzResearch.WordTrace tailWord_2514039 prefixEnd_2514039 1290910391148794544550651 := by
  unfold tailWord_2514039
  simp only [CollatzResearch.WordTrace]
  refine ⟨91694535339073541522921171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61129690226049027681947447 91694535339073541522921171)
  ·
    refine ⟨137541803008610312284381757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91694535339073541522921171 137541803008610312284381757)
    ·
      refine ⟨51578176128228867106643159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137541803008610312284381757 51578176128228867106643159)
      ·
        refine ⟨77367264192343300659964739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51578176128228867106643159 77367264192343300659964739)
        ·
          refine ⟨116050896288514950989947109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77367264192343300659964739 116050896288514950989947109)
          ·
            refine ⟨21759543054096553310615083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 116050896288514950989947109 21759543054096553310615083)
            ·
              refine ⟨32639314581144829965922625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21759543054096553310615083 32639314581144829965922625)
              ·
                refine ⟨24479485935858622474441969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32639314581144829965922625 24479485935858622474441969)
                ·
                  refine ⟨18359614451893966855831477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24479485935858622474441969 18359614451893966855831477)
                  ·
                    refine ⟨1721213854865059392734201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18359614451893966855831477 1721213854865059392734201)
                    ·
                      refine ⟨1290910391148794544550651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1721213854865059392734201 1290910391148794544550651)
                      ·
                        rfl

theorem cell23_2514039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 2, 2, 5, 2].length) (baseStart_2514039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2514039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2514039 prefixEnd_2514039 := by exact prefixLift 2514039
  have htrace : WordTrace (prefixWord ++ tailWord_2514039) baseStart_2514039 baseEnd_2514039 := by
    simpa [prefixWord, tailWord_2514039, baseEnd_2514039] using wordTrace_append hprefix tailTrace_2514039
  have hstable : (prefixWord ++ tailWord_2514039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2514039).length < 2 ^ (prefixWord ++ tailWord_2514039).sum := by decide
  have hdescent : baseEnd_2514039 < baseStart_2514039 := by decide
  rcases family_descends (prefixWord ++ tailWord_2514039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2514049 : List Nat := [1, 2, 4, 2, 2, 2, 1, 1, 1, 7]
def baseStart_2514049 : Nat := 118140960795 + 2514049 * 2 ^ 59
def prefixEnd_2514049 : Nat := 4983230072969 + 3 ^ 40 * 2514049 * 2
def baseEnd_2514049 : Nat := 430305175318446501808535

theorem tailTrace_2514049 : CollatzResearch.WordTrace tailWord_2514049 prefixEnd_2514049 430305175318446501808535 := by
  unfold tailWord_2514049
  simp only [CollatzResearch.WordTrace]
  refine ⟨91694900069037313230785201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61129933379358208820523467 91694900069037313230785201)
  ·
    refine ⟨68771175051777984923088901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91694900069037313230785201 68771175051777984923088901)
    ·
      refine ⟨12894595322208372173079169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68771175051777984923088901 12894595322208372173079169)
      ·
        refine ⟨9670946491656279129809377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12894595322208372173079169 9670946491656279129809377)
        ·
          refine ⟨7253209868742209347357033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9670946491656279129809377 7253209868742209347357033)
          ·
            refine ⟨5439907401556657010517775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7253209868742209347357033 5439907401556657010517775)
            ·
              refine ⟨8159861102334985515776663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5439907401556657010517775 8159861102334985515776663)
              ·
                refine ⟨12239791653502478273664995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8159861102334985515776663 12239791653502478273664995)
                ·
                  refine ⟨18359687480253717410497493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12239791653502478273664995 18359687480253717410497493)
                  ·
                    refine ⟨430305175318446501808535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18359687480253717410497493 430305175318446501808535)
                    ·
                      rfl

theorem cell23_2514049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 1, 1, 7].length) (baseStart_2514049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2514049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2514049 prefixEnd_2514049 := by exact prefixLift 2514049
  have htrace : WordTrace (prefixWord ++ tailWord_2514049) baseStart_2514049 baseEnd_2514049 := by
    simpa [prefixWord, tailWord_2514049, baseEnd_2514049] using wordTrace_append hprefix tailTrace_2514049
  have hstable : (prefixWord ++ tailWord_2514049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2514049).length < 2 ^ (prefixWord ++ tailWord_2514049).sum := by decide
  have hdescent : baseEnd_2514049 < baseStart_2514049 := by decide
  rcases family_descends (prefixWord ++ tailWord_2514049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2514130 : List Nat := [3, 2, 2, 2, 1, 1, 5, 2, 1, 4]
def baseStart_2514130 : Nat := 118140960795 + 2514130 * 2 ^ 59
def prefixEnd_2514130 : Nat := 4983230072969 + 3 ^ 40 * 2514130 * 2
def baseEnd_2514130 : Nat := 430319039296117896170911

theorem tailTrace_2514130 : CollatzResearch.WordTrace tailWord_2514130 prefixEnd_2514130 430319039296117896170911 := by
  unfold tailWord_2514130
  simp only [CollatzResearch.WordTrace]
  refine ⟨22924463595435966016120961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61131902921162576042989229 22924463595435966016120961)
  ·
    refine ⟨17193347696576974512090721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22924463595435966016120961 17193347696576974512090721)
    ·
      refine ⟨12895010772432730884068041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17193347696576974512090721 12895010772432730884068041)
      ·
        refine ⟨9671258079324548163051031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12895010772432730884068041 9671258079324548163051031)
        ·
          refine ⟨14506887118986822244576547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9671258079324548163051031 14506887118986822244576547)
          ·
            refine ⟨21760330678480233366864821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14506887118986822244576547 21760330678480233366864821)
            ·
              refine ⟨2040031001107521878143577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21760330678480233366864821 2040031001107521878143577)
              ·
                refine ⟨1530023250830641408607683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2040031001107521878143577 1530023250830641408607683)
                ·
                  refine ⟨2295034876245962112911525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1530023250830641408607683 2295034876245962112911525)
                  ·
                    refine ⟨430319039296117896170911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2295034876245962112911525 430319039296117896170911)
                    ·
                      rfl

theorem cell23_2514130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 5, 2, 1, 4].length) (baseStart_2514130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2514130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2514130 prefixEnd_2514130 := by exact prefixLift 2514130
  have htrace : WordTrace (prefixWord ++ tailWord_2514130) baseStart_2514130 baseEnd_2514130 := by
    simpa [prefixWord, tailWord_2514130, baseEnd_2514130] using wordTrace_append hprefix tailTrace_2514130
  have hstable : (prefixWord ++ tailWord_2514130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2514130).length < 2 ^ (prefixWord ++ tailWord_2514130).sum := by decide
  have hdescent : baseEnd_2514130 < baseStart_2514130 := by decide
  rcases family_descends (prefixWord ++ tailWord_2514130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2514156 : List Nat := [2, 2, 1, 1, 2, 4, 3, 2, 1, 5]
def baseStart_2514156 : Nat := 118140960795 + 2514156 * 2 ^ 59
def prefixEnd_2514156 : Nat := 4983230072969 + 3 ^ 40 * 2514156 * 2
def baseEnd_2514156 : Nat := 430323489461790195595871

theorem tailTrace_2514156 : CollatzResearch.WordTrace tailWord_2514156 prefixEnd_2514156 430323489461790195595871 := by
  unfold tailWord_2514156
  simp only [CollatzResearch.WordTrace]
  refine ⟨45849401339824835252465161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61132535119766447003286881 45849401339824835252465161)
  ·
    refine ⟨34387051004868626439348871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45849401339824835252465161 34387051004868626439348871)
    ·
      refine ⟨51580576507302939659023307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34387051004868626439348871 51580576507302939659023307)
      ·
        refine ⟨77370864760954409488534961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51580576507302939659023307 77370864760954409488534961)
        ·
          refine ⟨58028148570715807116401221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77370864760954409488534961 58028148570715807116401221)
          ·
            refine ⟨10880277857009213834325229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58028148570715807116401221 10880277857009213834325229)
            ·
              refine ⟨4080104196378455187871961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10880277857009213834325229 4080104196378455187871961)
              ·
                refine ⟨3060078147283841390903971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4080104196378455187871961 3060078147283841390903971)
                ·
                  refine ⟨4590117220925762086355957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3060078147283841390903971 4590117220925762086355957)
                  ·
                    refine ⟨430323489461790195595871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4590117220925762086355957 430323489461790195595871)
                    ·
                      rfl

theorem cell23_2514156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 5].length) (baseStart_2514156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2514156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2514156 prefixEnd_2514156 := by exact prefixLift 2514156
  have htrace : WordTrace (prefixWord ++ tailWord_2514156) baseStart_2514156 baseEnd_2514156 := by
    simpa [prefixWord, tailWord_2514156, baseEnd_2514156] using wordTrace_append hprefix tailTrace_2514156
  have hstable : (prefixWord ++ tailWord_2514156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2514156).length < 2 ^ (prefixWord ++ tailWord_2514156).sum := by decide
  have hdescent : baseEnd_2514156 < baseStart_2514156 := by decide
  rcases family_descends (prefixWord ++ tailWord_2514156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2514163 : List Nat := [1, 1, 1, 2, 2, 6, 2, 1, 2, 3, 2]
def baseStart_2514163 : Nat := 118140960795 + 2514163 * 2 ^ 59
def prefixEnd_2514163 : Nat := 4983230072969 + 3 ^ 40 * 2514163 * 2
def baseEnd_2514163 : Nat := 1290974062749952059400081

theorem tailTrace_2514163 : CollatzResearch.WordTrace tailWord_2514163 prefixEnd_2514163 1290974062749952059400081 := by
  unfold tailWord_2514163
  simp only [CollatzResearch.WordTrace]
  refine ⟨91699057990624310700435143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61132705327082873800290095 91699057990624310700435143)
  ·
    refine ⟨137548586985936466050652715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91699057990624310700435143 137548586985936466050652715)
    ·
      refine ⟨206322880478904699075979073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137548586985936466050652715 206322880478904699075979073)
      ·
        refine ⟨154742160359178524306984305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 206322880478904699075979073 154742160359178524306984305)
        ·
          refine ⟨116056620269383893230238229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 154742160359178524306984305 116056620269383893230238229)
          ·
            refine ⟨5440154075127369995167417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 116056620269383893230238229 5440154075127369995167417)
            ·
              refine ⟨4080115556345527496375563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5440154075127369995167417 4080115556345527496375563)
              ·
                refine ⟨6120173334518291244563345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4080115556345527496375563 6120173334518291244563345)
                ·
                  refine ⟨4590130000888718433422509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6120173334518291244563345 4590130000888718433422509)
                  ·
                    refine ⟨1721298750333269412533441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4590130000888718433422509 1721298750333269412533441)
                    ·
                      refine ⟨1290974062749952059400081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1721298750333269412533441 1290974062749952059400081)
                      ·
                        rfl

theorem cell23_2514163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 2, 1, 2, 3, 2].length) (baseStart_2514163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2514163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2514163 prefixEnd_2514163 := by exact prefixLift 2514163
  have htrace : WordTrace (prefixWord ++ tailWord_2514163) baseStart_2514163 baseEnd_2514163 := by
    simpa [prefixWord, tailWord_2514163, baseEnd_2514163] using wordTrace_append hprefix tailTrace_2514163
  have hstable : (prefixWord ++ tailWord_2514163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2514163).length < 2 ^ (prefixWord ++ tailWord_2514163).sum := by decide
  have hdescent : baseEnd_2514163 < baseStart_2514163 := by decide
  rcases family_descends (prefixWord ++ tailWord_2514163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2514169 : List Nat := [1, 2, 1, 3, 1, 1, 5, 2, 1, 6]
def baseStart_2514169 : Nat := 118140960795 + 2514169 * 2 ^ 59
def prefixEnd_2514169 : Nat := 4983230072969 + 3 ^ 40 * 2514169 * 2
def baseEnd_2514169 : Nat := 430325714544626345308351

theorem tailTrace_2514169 : CollatzResearch.WordTrace tailWord_2514169 prefixEnd_2514169 430325714544626345308351 := by
  unfold tailWord_2514169
  simp only [CollatzResearch.WordTrace]
  refine ⟨91699276828602573725153561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61132851219068382483435707 91699276828602573725153561)
  ·
    refine ⟨68774457621451930293865171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91699276828602573725153561 68774457621451930293865171)
    ·
      refine ⟨103161686432177895440797757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68774457621451930293865171 103161686432177895440797757)
      ·
        refine ⟨38685632412066710790299159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103161686432177895440797757 38685632412066710790299159)
        ·
          refine ⟨58028448618100066185448739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38685632412066710790299159 58028448618100066185448739)
          ·
            refine ⟨87042672927150099278173109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58028448618100066185448739 87042672927150099278173109)
            ·
              refine ⟨8160250586920321807328729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 87042672927150099278173109 8160250586920321807328729)
              ·
                refine ⟨6120187940190241355496547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8160250586920321807328729 6120187940190241355496547)
                ·
                  refine ⟨9180281910285362033244821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6120187940190241355496547 9180281910285362033244821)
                  ·
                    refine ⟨430325714544626345308351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9180281910285362033244821 430325714544626345308351)
                    ·
                      rfl

theorem cell23_2514169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 2, 1, 6].length) (baseStart_2514169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2514169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2514169 prefixEnd_2514169 := by exact prefixLift 2514169
  have htrace : WordTrace (prefixWord ++ tailWord_2514169) baseStart_2514169 baseEnd_2514169 := by
    simpa [prefixWord, tailWord_2514169, baseEnd_2514169] using wordTrace_append hprefix tailTrace_2514169
  have hstable : (prefixWord ++ tailWord_2514169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2514169).length < 2 ^ (prefixWord ++ tailWord_2514169).sum := by decide
  have hdescent : baseEnd_2514169 < baseStart_2514169 := by decide
  rcases family_descends (prefixWord ++ tailWord_2514169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2514187 : List Nat := [1, 1, 1, 1, 5, 5, 2, 2, 1, 1, 3]
def baseStart_2514187 : Nat := 118140960795 + 2514187 * 2 ^ 59
def prefixEnd_2514187 : Nat := 4983230072969 + 3 ^ 40 * 2514187 * 2
def baseEnd_2514187 : Nat := 1290986386285659965499971

theorem tailTrace_2514187 : CollatzResearch.WordTrace tailWord_2514187 prefixEnd_2514187 1290986386285659965499971 := by
  unfold tailWord_2514187
  simp only [CollatzResearch.WordTrace]
  refine ⟨91699933342537362799308815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61133288895024908532872543 91699933342537362799308815)
  ·
    refine ⟨137549900013806044198963223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91699933342537362799308815 137549900013806044198963223)
    ·
      refine ⟨206324850020709066298444835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137549900013806044198963223 206324850020709066298444835)
      ·
        refine ⟨309487275031063599447667253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206324850020709066298444835 309487275031063599447667253)
        ·
          refine ⟨29014432034162212448218805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 309487275031063599447667253 29014432034162212448218805)
          ·
            refine ⟨2720103003202707417020513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29014432034162212448218805 2720103003202707417020513)
            ·
              refine ⟨2040077252402030562765385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2720103003202707417020513 2040077252402030562765385)
              ·
                refine ⟨1530057939301522922074039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2040077252402030562765385 1530057939301522922074039)
                ·
                  refine ⟨2295086908952284383111059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1530057939301522922074039 2295086908952284383111059)
                  ·
                    refine ⟨3442630363428426574666589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2295086908952284383111059 3442630363428426574666589)
                    ·
                      refine ⟨1290986386285659965499971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3442630363428426574666589 1290986386285659965499971)
                      ·
                        rfl

theorem cell23_2514187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 2, 2, 1, 1, 3].length) (baseStart_2514187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2514187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2514187 prefixEnd_2514187 := by exact prefixLift 2514187
  have htrace : WordTrace (prefixWord ++ tailWord_2514187) baseStart_2514187 baseEnd_2514187 := by
    simpa [prefixWord, tailWord_2514187, baseEnd_2514187] using wordTrace_append hprefix tailTrace_2514187
  have hstable : (prefixWord ++ tailWord_2514187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2514187).length < 2 ^ (prefixWord ++ tailWord_2514187).sum := by decide
  have hdescent : baseEnd_2514187 < baseStart_2514187 := by decide
  rcases family_descends (prefixWord ++ tailWord_2514187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2514193 : List Nat := [1, 2, 2, 1, 1, 4, 2, 3, 3, 2, 2]
def baseStart_2514193 : Nat := 118140960795 + 2514193 * 2 ^ 59
def prefixEnd_2514193 : Nat := 4983230072969 + 3 ^ 40 * 2514193 * 2
def baseEnd_2514193 : Nat := 1290989467169586942024943

theorem tailTrace_2514193 : CollatzResearch.WordTrace tailWord_2514193 prefixEnd_2514193 1290989467169586942024943 := by
  unfold tailWord_2514193
  simp only [CollatzResearch.WordTrace]
  refine ⟨91700152180515625824027233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61133434787010417216018155 91700152180515625824027233)
  ·
    refine ⟨68775114135386719368020425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91700152180515625824027233 68775114135386719368020425)
    ·
      refine ⟨51581335601540039526015319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68775114135386719368020425 51581335601540039526015319)
      ·
        refine ⟨77372003402310059289022979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51581335601540039526015319 77372003402310059289022979)
        ·
          refine ⟨116058005103465088933534469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77372003402310059289022979 116058005103465088933534469)
          ·
            refine ⟨21760875956899704175037713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 116058005103465088933534469 21760875956899704175037713)
            ·
              refine ⟨16320656967674778131278285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21760875956899704175037713 16320656967674778131278285)
              ·
                refine ⟨6120246362878041799229357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16320656967674778131278285 6120246362878041799229357)
                ·
                  refine ⟨2295092386079265674711009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6120246362878041799229357 2295092386079265674711009)
                  ·
                    refine ⟨1721319289559449256033257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2295092386079265674711009 1721319289559449256033257)
                    ·
                      refine ⟨1290989467169586942024943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1721319289559449256033257 1290989467169586942024943)
                      ·
                        rfl

theorem cell23_2514193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 3, 3, 2, 2].length) (baseStart_2514193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2514193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2514193 prefixEnd_2514193 := by exact prefixLift 2514193
  have htrace : WordTrace (prefixWord ++ tailWord_2514193) baseStart_2514193 baseEnd_2514193 := by
    simpa [prefixWord, tailWord_2514193, baseEnd_2514193] using wordTrace_append hprefix tailTrace_2514193
  have hstable : (prefixWord ++ tailWord_2514193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2514193).length < 2 ^ (prefixWord ++ tailWord_2514193).sum := by decide
  have hdescent : baseEnd_2514193 < baseStart_2514193 := by decide
  rcases family_descends (prefixWord ++ tailWord_2514193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2514227 : List Nat := [1, 1, 1, 2, 5, 3, 2, 3, 1, 2, 2]
def baseStart_2514227 : Nat := 118140960795 + 2514227 * 2 ^ 59
def prefixEnd_2514227 : Nat := 4983230072969 + 3 ^ 40 * 2514227 * 2
def baseEnd_2514227 : Nat := 1291006925511839808999787

theorem tailTrace_2514227 : CollatzResearch.WordTrace tailWord_2514227 prefixEnd_2514227 1291006925511839808999787 := by
  unfold tailWord_2514227
  simp only [CollatzResearch.WordTrace]
  refine ⟨91701392262392449630764935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61134261508261633087176623 91701392262392449630764935)
  ·
    refine ⟨137552088393588674446147403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91701392262392449630764935 137552088393588674446147403)
    ·
      refine ⟨206328132590383011669221105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137552088393588674446147403 206328132590383011669221105)
      ·
        refine ⟨154746099442787258751915829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 206328132590383011669221105 154746099442787258751915829)
        ·
          refine ⟨14507446822761305507992109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 154746099442787258751915829 14507446822761305507992109)
          ·
            refine ⟨5440292558535489565497041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14507446822761305507992109 5440292558535489565497041)
            ·
              refine ⟨4080219418901617174122781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5440292558535489565497041 4080219418901617174122781)
              ·
                refine ⟨1530082282088106440296043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4080219418901617174122781 1530082282088106440296043)
                ·
                  refine ⟨2295123423132159660444065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1530082282088106440296043 2295123423132159660444065)
                  ·
                    refine ⟨1721342567349119745333049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2295123423132159660444065 1721342567349119745333049)
                    ·
                      refine ⟨1291006925511839808999787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1721342567349119745333049 1291006925511839808999787)
                      ·
                        rfl

theorem cell23_2514227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 2, 3, 1, 2, 2].length) (baseStart_2514227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2514227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2514227 prefixEnd_2514227 := by exact prefixLift 2514227
  have htrace : WordTrace (prefixWord ++ tailWord_2514227) baseStart_2514227 baseEnd_2514227 := by
    simpa [prefixWord, tailWord_2514227, baseEnd_2514227] using wordTrace_append hprefix tailTrace_2514227
  have hstable : (prefixWord ++ tailWord_2514227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2514227).length < 2 ^ (prefixWord ++ tailWord_2514227).sum := by decide
  have hdescent : baseEnd_2514227 < baseStart_2514227 := by decide
  rcases family_descends (prefixWord ++ tailWord_2514227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2514237 : List Nat := [1, 4, 1, 5, 1, 2, 1, 2, 2, 4]
def baseStart_2514237 : Nat := 118140960795 + 2514237 * 2 ^ 59
def prefixEnd_2514237 : Nat := 4983230072969 + 3 ^ 40 * 2514237 * 2
def baseEnd_2514237 : Nat := 430337353439461589958247

theorem tailTrace_2514237 : CollatzResearch.WordTrace tailWord_2514237 prefixEnd_2514237 430337353439461589958247 := by
  unfold tailWord_2514237
  simp only [CollatzResearch.WordTrace]
  refine ⟨91701756992356221338628965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61134504661570814225752643 91701756992356221338628965)
  ·
    refine ⟨17194079436066791500992931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 91701756992356221338628965 17194079436066791500992931)
    ·
      refine ⟨25791119154100187251489397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17194079436066791500992931 25791119154100187251489397)
      ·
        refine ⟨2417917420696892554827131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25791119154100187251489397 2417917420696892554827131)
        ·
          refine ⟨3626876131045338832240697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2417917420696892554827131 3626876131045338832240697)
          ·
            refine ⟨2720157098284004124180523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3626876131045338832240697 2720157098284004124180523)
            ·
              refine ⟨4080235647426006186270785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2720157098284004124180523 4080235647426006186270785)
              ·
                refine ⟨3060176735569504639703089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4080235647426006186270785 3060176735569504639703089)
                ·
                  refine ⟨2295132551677128479777317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3060176735569504639703089 2295132551677128479777317)
                  ·
                    refine ⟨430337353439461589958247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2295132551677128479777317 430337353439461589958247)
                    ·
                      rfl

theorem cell23_2514237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 1, 2, 2, 4].length) (baseStart_2514237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2514237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2514237 prefixEnd_2514237 := by exact prefixLift 2514237
  have htrace : WordTrace (prefixWord ++ tailWord_2514237) baseStart_2514237 baseEnd_2514237 := by
    simpa [prefixWord, tailWord_2514237, baseEnd_2514237] using wordTrace_append hprefix tailTrace_2514237
  have hstable : (prefixWord ++ tailWord_2514237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2514237).length < 2 ^ (prefixWord ++ tailWord_2514237).sum := by decide
  have hdescent : baseEnd_2514237 < baseStart_2514237 := by decide
  rcases family_descends (prefixWord ++ tailWord_2514237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2514244 : List Nat := [2, 3, 4, 1, 1, 1, 2, 4, 1, 2, 2]
def baseStart_2514244 : Nat := 118140960795 + 2514244 * 2 ^ 59
def prefixEnd_2514244 : Nat := 4983230072969 + 3 ^ 40 * 2514244 * 2
def baseEnd_2514244 : Nat := 1291015654682966242487209

theorem tailTrace_2514244 : CollatzResearch.WordTrace tailWord_2514244 prefixEnd_2514244 1291015654682966242487209 := by
  unfold tailWord_2514244
  simp only [CollatzResearch.WordTrace]
  refine ⟨45851006151665430767066893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61134674868887241022755857 45851006151665430767066893)
  ·
    refine ⟨17194127306874536537650085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45851006151665430767066893 17194127306874536537650085)
    ·
      refine ⟨3223898870038975600809391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17194127306874536537650085 3223898870038975600809391)
      ·
        refine ⟨4835848305058463401214087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3223898870038975600809391 4835848305058463401214087)
        ·
          refine ⟨7253772457587695101821131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4835848305058463401214087 7253772457587695101821131)
          ·
            refine ⟨10880658686381542652731697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7253772457587695101821131 10880658686381542652731697)
            ·
              refine ⟨8160494014786156989548773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10880658686381542652731697 8160494014786156989548773)
              ·
                refine ⟨1530092627772404435540395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8160494014786156989548773 1530092627772404435540395)
                ·
                  refine ⟨2295138941658606653310593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1530092627772404435540395 2295138941658606653310593)
                  ·
                    refine ⟨1721354206243954989982945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2295138941658606653310593 1721354206243954989982945)
                    ·
                      refine ⟨1291015654682966242487209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1721354206243954989982945 1291015654682966242487209)
                      ·
                        rfl

theorem cell23_2514244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 4, 1, 2, 2].length) (baseStart_2514244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2514244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2514244 prefixEnd_2514244 := by exact prefixLift 2514244
  have htrace : WordTrace (prefixWord ++ tailWord_2514244) baseStart_2514244 baseEnd_2514244 := by
    simpa [prefixWord, tailWord_2514244, baseEnd_2514244] using wordTrace_append hprefix tailTrace_2514244
  have hstable : (prefixWord ++ tailWord_2514244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2514244).length < 2 ^ (prefixWord ++ tailWord_2514244).sum := by decide
  have hdescent : baseEnd_2514244 < baseStart_2514244 := by decide
  rcases family_descends (prefixWord ++ tailWord_2514244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2514249 : List Nat := [1, 2, 1, 1, 2, 3, 2, 1, 1, 5, 4]
def baseStart_2514249 : Nat := 118140960795 + 2514249 * 2 ^ 59
def prefixEnd_2514249 : Nat := 4983230072969 + 3 ^ 40 * 2514249 * 2
def baseEnd_2514249 : Nat := 1291018222086238722924685

theorem tailTrace_2514249 : CollatzResearch.WordTrace tailWord_2514249 prefixEnd_2514249 1291018222086238722924685 := by
  unfold tailWord_2514249
  simp only [CollatzResearch.WordTrace]
  refine ⟨91702194668312747388065801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61134796445541831592043867 91702194668312747388065801)
  ·
    refine ⟨68776646001234560541049351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91702194668312747388065801 68776646001234560541049351)
    ·
      refine ⟨103164969001851840811574027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68776646001234560541049351 103164969001851840811574027)
      ·
        refine ⟨154747453502777761217361041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103164969001851840811574027 154747453502777761217361041)
        ·
          refine ⟨116060590127083320913020781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 154747453502777761217361041 116060590127083320913020781)
          ·
            refine ⟨43522721297656245342382793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 116060590127083320913020781 43522721297656245342382793)
            ·
              refine ⟨32642040973242184006787095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43522721297656245342382793 32642040973242184006787095)
              ·
                refine ⟨48963061459863276010180643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32642040973242184006787095 48963061459863276010180643)
                ·
                  refine ⟨73444592189794914015270965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48963061459863276010180643 73444592189794914015270965)
                  ·
                    refine ⟨6885430517793273188931653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 73444592189794914015270965 6885430517793273188931653)
                    ·
                      refine ⟨1291018222086238722924685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6885430517793273188931653 1291018222086238722924685)
                      ·
                        rfl

theorem cell23_2514249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 1, 1, 5, 4].length) (baseStart_2514249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2514249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2514249 prefixEnd_2514249 := by exact prefixLift 2514249
  have htrace : WordTrace (prefixWord ++ tailWord_2514249) baseStart_2514249 baseEnd_2514249 := by
    simpa [prefixWord, tailWord_2514249, baseEnd_2514249] using wordTrace_append hprefix tailTrace_2514249
  have hstable : (prefixWord ++ tailWord_2514249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2514249).length < 2 ^ (prefixWord ++ tailWord_2514249).sum := by decide
  have hdescent : baseEnd_2514249 < baseStart_2514249 := by decide
  rcases family_descends (prefixWord ++ tailWord_2514249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2514259 : List Nat := [1, 1, 1, 2, 1, 1, 5, 3, 2, 6]
def baseStart_2514259 : Nat := 118140960795 + 2514259 * 2 ^ 59
def prefixEnd_2514259 : Nat := 4983230072969 + 3 ^ 40 * 2514259 * 2
def baseEnd_2514259 : Nat := 430341118964261227933213

theorem tailTrace_2514259 : CollatzResearch.WordTrace tailWord_2514259 prefixEnd_2514259 430341118964261227933213 := by
  unfold tailWord_2514259
  simp only [CollatzResearch.WordTrace]
  refine ⟨91702559398276519095929831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61135039598851012730619887 91702559398276519095929831)
  ·
    refine ⟨137553839097414778643894747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91702559398276519095929831 137553839097414778643894747)
    ·
      refine ⟨206330758646122167965842121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137553839097414778643894747 206330758646122167965842121)
      ·
        refine ⟨154748068984591625974381591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 206330758646122167965842121 154748068984591625974381591)
        ·
          refine ⟨232122103476887438961572387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154748068984591625974381591 232122103476887438961572387)
          ·
            refine ⟨348183155215331158442358581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 232122103476887438961572387 348183155215331158442358581)
            ·
              refine ⟨32642170801437296103971117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 348183155215331158442358581 32642170801437296103971117)
              ·
                refine ⟨12240814050538986038989169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32642170801437296103971117 12240814050538986038989169)
                ·
                  refine ⟨9180610537904239529241877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12240814050538986038989169 9180610537904239529241877)
                  ·
                    refine ⟨430341118964261227933213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9180610537904239529241877 430341118964261227933213)
                    ·
                      rfl

theorem cell23_2514259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 3, 2, 6].length) (baseStart_2514259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2514259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2514259 prefixEnd_2514259 := by exact prefixLift 2514259
  have htrace : WordTrace (prefixWord ++ tailWord_2514259) baseStart_2514259 baseEnd_2514259 := by
    simpa [prefixWord, tailWord_2514259, baseEnd_2514259] using wordTrace_append hprefix tailTrace_2514259
  have hstable : (prefixWord ++ tailWord_2514259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2514259).length < 2 ^ (prefixWord ++ tailWord_2514259).sum := by decide
  have hdescent : baseEnd_2514259 < baseStart_2514259 := by decide
  rcases family_descends (prefixWord ++ tailWord_2514259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2514289 : List Nat := [1, 2, 2, 2, 1, 2, 2, 2, 9]
def baseStart_2514289 : Nat := 118140960795 + 2514289 * 2 ^ 59
def prefixEnd_2514289 : Nat := 4983230072969 + 3 ^ 40 * 2514289 * 2
def baseEnd_2514289 : Nat := 143448751256935396269389

theorem tailTrace_2514289 : CollatzResearch.WordTrace tailWord_2514289 prefixEnd_2514289 143448751256935396269389 := by
  unfold tailWord_2514289
  simp only [CollatzResearch.WordTrace]
  refine ⟨91703653588167834219521921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61135769058778556146347947 91703653588167834219521921)
  ·
    refine ⟨68777740191125875664641441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91703653588167834219521921 68777740191125875664641441)
    ·
      refine ⟨51583305143344406748481081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68777740191125875664641441 51583305143344406748481081)
      ·
        refine ⟨38687478857508305061360811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51583305143344406748481081 38687478857508305061360811)
        ·
          refine ⟨58031218286262457592041217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38687478857508305061360811 58031218286262457592041217)
          ·
            refine ⟨43523413714696843194030913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58031218286262457592041217 43523413714696843194030913)
            ·
              refine ⟨32642560286022632395523185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43523413714696843194030913 32642560286022632395523185)
              ·
                refine ⟨24481920214516974296642389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32642560286022632395523185 24481920214516974296642389)
                ·
                  refine ⟨143448751256935396269389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 24481920214516974296642389 143448751256935396269389)
                  ·
                    rfl

theorem cell23_2514289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 2, 9].length) (baseStart_2514289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2514289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2514289 prefixEnd_2514289 := by exact prefixLift 2514289
  have htrace : WordTrace (prefixWord ++ tailWord_2514289) baseStart_2514289 baseEnd_2514289 := by
    simpa [prefixWord, tailWord_2514289, baseEnd_2514289] using wordTrace_append hprefix tailTrace_2514289
  have hstable : (prefixWord ++ tailWord_2514289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2514289).length < 2 ^ (prefixWord ++ tailWord_2514289).sum := by decide
  have hdescent : baseEnd_2514289 < baseStart_2514289 := by decide
  rcases family_descends (prefixWord ++ tailWord_2514289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2514299 : List Nat := [1, 1, 1, 1, 1, 6, 1, 1, 1, 2, 7]
def baseStart_2514299 : Nat := 118140960795 + 2514299 * 2 ^ 59
def prefixEnd_2514299 : Nat := 4983230072969 + 3 ^ 40 * 2514299 * 2
def baseEnd_2514299 : Nat := 1291043896118963527299455

theorem tailTrace_2514299 : CollatzResearch.WordTrace tailWord_2514299 prefixEnd_2514299 1291043896118963527299455 := by
  unfold tailWord_2514299
  simp only [CollatzResearch.WordTrace]
  refine ⟨91704018318131605927385951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61136012212087737284923967 91704018318131605927385951)
  ·
    refine ⟨137556027477197408891078927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91704018318131605927385951 137556027477197408891078927)
    ·
      refine ⟨206334041215796113336618391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137556027477197408891078927 206334041215796113336618391)
      ·
        refine ⟨309501061823694170004927587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206334041215796113336618391 309501061823694170004927587)
        ·
          refine ⟨464251592735541255007391381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 309501061823694170004927587 464251592735541255007391381)
          ·
            refine ⟨21761793409478496328471471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 464251592735541255007391381 21761793409478496328471471)
            ·
              refine ⟨32642690114217744492707207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21761793409478496328471471 32642690114217744492707207)
              ·
                refine ⟨48964035171326616739060811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32642690114217744492707207 48964035171326616739060811)
                ·
                  refine ⟨73446052756989925108591217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48964035171326616739060811 73446052756989925108591217)
                  ·
                    refine ⟨55084539567742443831443413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 73446052756989925108591217 55084539567742443831443413)
                    ·
                      refine ⟨1291043896118963527299455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 55084539567742443831443413 1291043896118963527299455)
                      ·
                        rfl

theorem cell23_2514299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 1, 1, 2, 7].length) (baseStart_2514299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2514299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2514299 prefixEnd_2514299 := by exact prefixLift 2514299
  have htrace : WordTrace (prefixWord ++ tailWord_2514299) baseStart_2514299 baseEnd_2514299 := by
    simpa [prefixWord, tailWord_2514299, baseEnd_2514299] using wordTrace_append hprefix tailTrace_2514299
  have hstable : (prefixWord ++ tailWord_2514299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2514299).length < 2 ^ (prefixWord ++ tailWord_2514299).sum := by decide
  have hdescent : baseEnd_2514299 < baseStart_2514299 := by decide
  rcases family_descends (prefixWord ++ tailWord_2514299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2514300 : List Nat := [2, 2, 2, 1, 1, 1, 4, 4, 2, 2, 2]
def baseStart_2514300 : Nat := 118140960795 + 2514300 * 2 ^ 59
def prefixEnd_2514300 : Nat := 4983230072969 + 3 ^ 40 * 2514300 * 2
def baseEnd_2514300 : Nat := 1291044409599618023386951

theorem tailTrace_2514300 : CollatzResearch.WordTrace tailWord_2514300 prefixEnd_2514300 1291044409599618023386951 := by
  unfold tailWord_2514300
  simp only [CollatzResearch.WordTrace]
  refine ⟨45852027395563991549086177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61136036527418655398781569 45852027395563991549086177)
  ·
    refine ⟨34389020546672993661814633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45852027395563991549086177 34389020546672993661814633)
    ·
      refine ⟨25791765410004745246360975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34389020546672993661814633 25791765410004745246360975)
      ·
        refine ⟨38687648115007117869541463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25791765410004745246360975 38687648115007117869541463)
        ·
          refine ⟨58031472172510676804312195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38687648115007117869541463 58031472172510676804312195)
          ·
            refine ⟨87047208258766015206468293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58031472172510676804312195 87047208258766015206468293)
            ·
              refine ⟨16321351548518627851212805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 87047208258766015206468293 16321351548518627851212805)
              ·
                refine ⟨3060253415347242722102401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16321351548518627851212805 3060253415347242722102401)
                ·
                  refine ⟨2295190061510432041576801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3060253415347242722102401 2295190061510432041576801)
                  ·
                    refine ⟨1721392546132824031182601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2295190061510432041576801 1721392546132824031182601)
                    ·
                      refine ⟨1291044409599618023386951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1721392546132824031182601 1291044409599618023386951)
                      ·
                        rfl

theorem cell23_2514300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 4, 2, 2, 2].length) (baseStart_2514300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2514300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2514300 prefixEnd_2514300 := by exact prefixLift 2514300
  have htrace : WordTrace (prefixWord ++ tailWord_2514300) baseStart_2514300 baseEnd_2514300 := by
    simpa [prefixWord, tailWord_2514300, baseEnd_2514300] using wordTrace_append hprefix tailTrace_2514300
  have hstable : (prefixWord ++ tailWord_2514300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2514300).length < 2 ^ (prefixWord ++ tailWord_2514300).sum := by decide
  have hdescent : baseEnd_2514300 < baseStart_2514300 := by decide
  rcases family_descends (prefixWord ++ tailWord_2514300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2514316 : List Nat := [2, 2, 1, 2, 1, 3, 2, 1, 1, 5, 3]
def baseStart_2514316 : Nat := 118140960795 + 2514316 * 2 ^ 59
def prefixEnd_2514316 : Nat := 4983230072969 + 3 ^ 40 * 2514316 * 2
def baseEnd_2514316 : Nat := 1291052625290089960786877

theorem tailTrace_2514316 : CollatzResearch.WordTrace tailWord_2514316 prefixEnd_2514316 1291052625290089960786877 := by
  unfold tailWord_2514316
  simp only [CollatzResearch.WordTrace]
  refine ⟨45852319179535008915377401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61136425572713345220503201 45852319179535008915377401)
  ·
    refine ⟨34389239384651256686533051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45852319179535008915377401 34389239384651256686533051)
    ·
      refine ⟨51583859076976885029799577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34389239384651256686533051 51583859076976885029799577)
      ·
        refine ⟨38687894307732663772349683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51583859076976885029799577 38687894307732663772349683)
        ·
          refine ⟨58031841461598995658524525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38687894307732663772349683 58031841461598995658524525)
          ·
            refine ⟨21761940548099623371946697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58031841461598995658524525 21761940548099623371946697)
            ·
              refine ⟨16321455411074717528960023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21761940548099623371946697 16321455411074717528960023)
              ·
                refine ⟨24482183116612076293440035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16321455411074717528960023 24482183116612076293440035)
                ·
                  refine ⟨36723274674918114440160053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24482183116612076293440035 36723274674918114440160053)
                  ·
                    refine ⟨3442807000773573228765005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36723274674918114440160053 3442807000773573228765005)
                    ·
                      refine ⟨1291052625290089960786877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3442807000773573228765005 1291052625290089960786877)
                      ·
                        rfl

theorem cell23_2514316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 1, 1, 5, 3].length) (baseStart_2514316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2514316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2514316 prefixEnd_2514316 := by exact prefixLift 2514316
  have htrace : WordTrace (prefixWord ++ tailWord_2514316) baseStart_2514316 baseEnd_2514316 := by
    simpa [prefixWord, tailWord_2514316, baseEnd_2514316] using wordTrace_append hprefix tailTrace_2514316
  have hstable : (prefixWord ++ tailWord_2514316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2514316).length < 2 ^ (prefixWord ++ tailWord_2514316).sum := by decide
  have hdescent : baseEnd_2514316 < baseStart_2514316 := by decide
  rcases family_descends (prefixWord ++ tailWord_2514316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2514357 : List Nat := [1, 3, 3, 2, 2, 3, 2, 2, 5]
def baseStart_2514357 : Nat := 118140960795 + 2514357 * 2 ^ 59
def prefixEnd_2514357 : Nat := 4983230072969 + 3 ^ 40 * 2514357 * 2
def baseEnd_2514357 : Nat := 143452630888547144486021

theorem tailTrace_2514357 : CollatzResearch.WordTrace tailWord_2514357 prefixEnd_2514357 143452630888547144486021 := by
  unfold tailWord_2514357
  simp only [CollatzResearch.WordTrace]
  refine ⟨91706133751921481832997325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61137422501280987888664883 91706133751921481832997325)
  ·
    refine ⟨34389800156970555687373997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91706133751921481832997325 34389800156970555687373997)
    ·
      refine ⟨12896175058863958382765249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34389800156970555687373997 12896175058863958382765249)
      ·
        refine ⟨9672131294147968787073937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12896175058863958382765249 9672131294147968787073937)
        ·
          refine ⟨7254098470610976590305453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9672131294147968787073937 7254098470610976590305453)
          ·
            refine ⟨2720286926479116221364545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7254098470610976590305453 2720286926479116221364545)
            ·
              refine ⟨2040215194859337166023409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2720286926479116221364545 2040215194859337166023409)
              ·
                refine ⟨1530161396144502874517557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2040215194859337166023409 1530161396144502874517557)
                ·
                  refine ⟨143452630888547144486021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1530161396144502874517557 143452630888547144486021)
                  ·
                    rfl

theorem cell23_2514357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 2, 2, 5].length) (baseStart_2514357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2514357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2514357 prefixEnd_2514357 := by exact prefixLift 2514357
  have htrace : WordTrace (prefixWord ++ tailWord_2514357) baseStart_2514357 baseEnd_2514357 := by
    simpa [prefixWord, tailWord_2514357, baseEnd_2514357] using wordTrace_append hprefix tailTrace_2514357
  have hstable : (prefixWord ++ tailWord_2514357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2514357).length < 2 ^ (prefixWord ++ tailWord_2514357).sum := by decide
  have hdescent : baseEnd_2514357 < baseStart_2514357 := by decide
  rcases family_descends (prefixWord ++ tailWord_2514357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2514366 : List Nat := [4, 2, 1, 1, 1, 1, 1, 2, 2, 8]
def baseStart_2514366 : Nat := 118140960795 + 2514366 * 2 ^ 59
def prefixEnd_2514366 : Nat := 4983230072969 + 3 ^ 40 * 2514366 * 2
def baseEnd_2514366 : Nat := 430359433107604921720549

theorem tailTrace_2514366 : CollatzResearch.WordTrace tailWord_2514366 prefixEnd_2514366 430359433107604921720549 := by
  unfold tailWord_2514366
  simp only [CollatzResearch.WordTrace]
  refine ⟨11463307751111109546259369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61137641339259250913383301 11463307751111109546259369)
  ·
    refine ⟨8597480813333332159694527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11463307751111109546259369 8597480813333332159694527)
    ·
      refine ⟨12896221219999998239541791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8597480813333332159694527 12896221219999998239541791)
      ·
        refine ⟨19344331829999997359312687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12896221219999998239541791 19344331829999997359312687)
        ·
          refine ⟨29016497744999996038969031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19344331829999997359312687 29016497744999996038969031)
          ·
            refine ⟨43524746617499994058453547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29016497744999996038969031 43524746617499994058453547)
            ·
              refine ⟨65287119926249991087680321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43524746617499994058453547 65287119926249991087680321)
              ·
                refine ⟨48965339944687493315760241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65287119926249991087680321 48965339944687493315760241)
                ·
                  refine ⟨36724004958515619986820181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48965339944687493315760241 36724004958515619986820181)
                  ·
                    refine ⟨430359433107604921720549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 36724004958515619986820181 430359433107604921720549)
                    ·
                      rfl

theorem cell23_2514366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 2, 2, 8].length) (baseStart_2514366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2514366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2514366 prefixEnd_2514366 := by exact prefixLift 2514366
  have htrace : WordTrace (prefixWord ++ tailWord_2514366) baseStart_2514366 baseEnd_2514366 := by
    simpa [prefixWord, tailWord_2514366, baseEnd_2514366] using wordTrace_append hprefix tailTrace_2514366
  have hstable : (prefixWord ++ tailWord_2514366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2514366).length < 2 ^ (prefixWord ++ tailWord_2514366).sum := by decide
  have hdescent : baseEnd_2514366 < baseStart_2514366 := by decide
  rcases family_descends (prefixWord ++ tailWord_2514366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2514390 : List Nat := [5, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4]
def baseStart_2514390 : Nat := 118140960795 + 2514390 * 2 ^ 59
def prefixEnd_2514390 : Nat := 4983230072969 + 3 ^ 40 * 2514390 * 2
def baseEnd_2514390 : Nat := 1291090622858522671261537

theorem tailTrace_2514390 : CollatzResearch.WordTrace tailWord_2514390 prefixEnd_2514390 1291090622858522671261537 := by
  unfold tailWord_2514390
  simp only [CollatzResearch.WordTrace]
  refine ⟨5731708585050120529309289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 61138224907201285645965749 5731708585050120529309289)
  ·
    refine ⟨4298781438787590396981967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5731708585050120529309289 4298781438787590396981967)
    ·
      refine ⟨6448172158181385595472951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4298781438787590396981967 6448172158181385595472951)
      ·
        refine ⟨9672258237272078393209427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6448172158181385595472951 9672258237272078393209427)
        ·
          refine ⟨14508387355908117589814141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9672258237272078393209427 14508387355908117589814141)
          ·
            refine ⟨5440645258465544096180303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14508387355908117589814141 5440645258465544096180303)
            ·
              refine ⟨8160967887698316144270455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5440645258465544096180303 8160967887698316144270455)
              ·
                refine ⟨12241451831547474216405683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8160967887698316144270455 12241451831547474216405683)
                ·
                  refine ⟨18362177747321211324608525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12241451831547474216405683 18362177747321211324608525)
                  ·
                    refine ⟨6885816655245454246728197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18362177747321211324608525 6885816655245454246728197)
                    ·
                      refine ⟨1291090622858522671261537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6885816655245454246728197 1291090622858522671261537)
                      ·
                        rfl

theorem cell23_2514390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_2514390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2514390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2514390 prefixEnd_2514390 := by exact prefixLift 2514390
  have htrace : WordTrace (prefixWord ++ tailWord_2514390) baseStart_2514390 baseEnd_2514390 := by
    simpa [prefixWord, tailWord_2514390, baseEnd_2514390] using wordTrace_append hprefix tailTrace_2514390
  have hstable : (prefixWord ++ tailWord_2514390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2514390).length < 2 ^ (prefixWord ++ tailWord_2514390).sum := by decide
  have hdescent : baseEnd_2514390 < baseStart_2514390 := by decide
  rcases family_descends (prefixWord ++ tailWord_2514390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2514393 : List Nat := [1, 2, 1, 2, 4, 3, 1, 1, 1, 4, 3]
def baseStart_2514393 : Nat := 118140960795 + 2514393 * 2 ^ 59
def prefixEnd_2514393 : Nat := 4983230072969 + 3 ^ 40 * 2514393 * 2
def baseEnd_2514393 : Nat := 1291092163300486159524023

theorem tailTrace_2514393 : CollatzResearch.WordTrace tailWord_2514393 prefixEnd_2514393 1291092163300486159524023 := by
  unfold tailWord_2514393
  simp only [CollatzResearch.WordTrace]
  refine ⟨91707446779791059981307833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61138297853194039987538555 91707446779791059981307833)
  ·
    refine ⟨68780585084843294985980875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91707446779791059981307833 68780585084843294985980875)
    ·
      refine ⟨103170877627264942478971313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68780585084843294985980875 103170877627264942478971313)
      ·
        refine ⟨77378158220448706859228485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103170877627264942478971313 77378158220448706859228485)
        ·
          refine ⟨14508404666334132536105341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 77378158220448706859228485 14508404666334132536105341)
          ·
            refine ⟨5440651749875299701039503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14508404666334132536105341 5440651749875299701039503)
            ·
              refine ⟨8160977624812949551559255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5440651749875299701039503 8160977624812949551559255)
              ·
                refine ⟨12241466437219424327338883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8160977624812949551559255 12241466437219424327338883)
                ·
                  refine ⟨18362199655829136491008325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12241466437219424327338883 18362199655829136491008325)
                  ·
                    refine ⟨3442912435467963092064061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18362199655829136491008325 3442912435467963092064061)
                    ·
                      refine ⟨1291092163300486159524023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3442912435467963092064061 1291092163300486159524023)
                      ·
                        rfl

theorem cell23_2514393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 1, 1, 4, 3].length) (baseStart_2514393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2514393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2514393 prefixEnd_2514393 := by exact prefixLift 2514393
  have htrace : WordTrace (prefixWord ++ tailWord_2514393) baseStart_2514393 baseEnd_2514393 := by
    simpa [prefixWord, tailWord_2514393, baseEnd_2514393] using wordTrace_append hprefix tailTrace_2514393
  have hstable : (prefixWord ++ tailWord_2514393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2514393).length < 2 ^ (prefixWord ++ tailWord_2514393).sum := by decide
  have hdescent : baseEnd_2514393 < baseStart_2514393 := by decide
  rcases family_descends (prefixWord ++ tailWord_2514393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2514416 : List Nat := [2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 6]
def baseStart_2514416 : Nat := 118140960795 + 2514416 * 2 ^ 59
def prefixEnd_2514416 : Nat := 4983230072969 + 3 ^ 40 * 2514416 * 2
def baseEnd_2514416 : Nat := 1291103973355539569536417

theorem tailTrace_2514416 : CollatzResearch.WordTrace tailWord_2514416 prefixEnd_2514416 1291103973355539569536417 := by
  unfold tailWord_2514416
  simp only [CollatzResearch.WordTrace]
  refine ⟨45854142829353867454697551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61138857105805156606263401 45854142829353867454697551)
  ·
    refine ⟨68781214244030801182046327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45854142829353867454697551 68781214244030801182046327)
    ·
      refine ⟨103171821366046201773069491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68781214244030801182046327 103171821366046201773069491)
      ·
        refine ⟨154757732049069302659604237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103171821366046201773069491 154757732049069302659604237)
        ·
          refine ⟨58034149518400988497351589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 154757732049069302659604237 58034149518400988497351589)
          ·
            refine ⟨10881403034700185343253423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58034149518400988497351589 10881403034700185343253423)
            ·
              refine ⟨16322104552050278014880135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10881403034700185343253423 16322104552050278014880135)
              ·
                refine ⟨24483156828075417022320203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16322104552050278014880135 24483156828075417022320203)
                ·
                  refine ⟨36724735242113125533480305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24483156828075417022320203 36724735242113125533480305)
                  ·
                    refine ⟨27543551431584844150110229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36724735242113125533480305 27543551431584844150110229)
                    ·
                      refine ⟨1291103973355539569536417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27543551431584844150110229 1291103973355539569536417)
                      ·
                        rfl

theorem cell23_2514416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 6].length) (baseStart_2514416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2514416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2514416 prefixEnd_2514416 := by exact prefixLift 2514416
  have htrace : WordTrace (prefixWord ++ tailWord_2514416) baseStart_2514416 baseEnd_2514416 := by
    simpa [prefixWord, tailWord_2514416, baseEnd_2514416] using wordTrace_append hprefix tailTrace_2514416
  have hstable : (prefixWord ++ tailWord_2514416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2514416).length < 2 ^ (prefixWord ++ tailWord_2514416).sum := by decide
  have hdescent : baseEnd_2514416 < baseStart_2514416 := by decide
  rcases family_descends (prefixWord ++ tailWord_2514416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2514440 : List Nat := [2, 1, 3, 2, 1, 1, 4, 2, 3, 1, 3]
def baseStart_2514440 : Nat := 118140960795 + 2514440 * 2 ^ 59
def prefixEnd_2514440 : Nat := 4983230072969 + 3 ^ 40 * 2514440 * 2
def baseEnd_2514440 : Nat := 1291116296891247475636307

theorem tailTrace_2514440 : CollatzResearch.WordTrace tailWord_2514440 prefixEnd_2514440 1291116296891247475636307 := by
  unfold tailWord_2514440
  simp only [CollatzResearch.WordTrace]
  refine ⟨45854580505310393504134387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61139440673747191338845849 45854580505310393504134387)
  ·
    refine ⟨68781870757965590256201581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45854580505310393504134387 68781870757965590256201581)
    ·
      refine ⟨25793201534237096346075593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68781870757965590256201581 25793201534237096346075593)
      ·
        refine ⟨19344901150677822259556695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25793201534237096346075593 19344901150677822259556695)
        ·
          refine ⟨29017351726016733389335043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19344901150677822259556695 29017351726016733389335043)
          ·
            refine ⟨43526027589025100084002565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29017351726016733389335043 43526027589025100084002565)
            ·
              refine ⟨8161130172942206265750481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43526027589025100084002565 8161130172942206265750481)
              ·
                refine ⟨6120847629706654699312861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8161130172942206265750481 6120847629706654699312861)
                ·
                  refine ⟨2295317861139995512242323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6120847629706654699312861 2295317861139995512242323)
                  ·
                    refine ⟨3442976791709993268363485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2295317861139995512242323 3442976791709993268363485)
                    ·
                      refine ⟨1291116296891247475636307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3442976791709993268363485 1291116296891247475636307)
                      ·
                        rfl

theorem cell23_2514440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 2, 3, 1, 3].length) (baseStart_2514440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2514440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2514440 prefixEnd_2514440 := by exact prefixLift 2514440
  have htrace : WordTrace (prefixWord ++ tailWord_2514440) baseStart_2514440 baseEnd_2514440 := by
    simpa [prefixWord, tailWord_2514440, baseEnd_2514440] using wordTrace_append hprefix tailTrace_2514440
  have hstable : (prefixWord ++ tailWord_2514440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2514440).length < 2 ^ (prefixWord ++ tailWord_2514440).sum := by decide
  have hdescent : baseEnd_2514440 < baseStart_2514440 := by decide
  rcases family_descends (prefixWord ++ tailWord_2514440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2514467 : List Nat := [1, 1, 1, 4, 5, 1, 1, 2, 2, 3, 2]
def baseStart_2514467 : Nat := 118140960795 + 2514467 * 2 ^ 59
def prefixEnd_2514467 : Nat := 4983230072969 + 3 ^ 40 * 2514467 * 2
def baseEnd_2514467 : Nat := 1291130160868918869998683

theorem tailTrace_2514467 : CollatzResearch.WordTrace tailWord_2514467 prefixEnd_2514467 1291130160868918869998683 := by
  unfold tailWord_2514467
  simp only [CollatzResearch.WordTrace]
  refine ⟨91710145781522970619501655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61140097187681980413001103 91710145781522970619501655)
  ·
    refine ⟨137565218672284455929252483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91710145781522970619501655 137565218672284455929252483)
    ·
      refine ⟨206347828008426683893878725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137565218672284455929252483 206347828008426683893878725)
      ·
        refine ⟨38690217751580003230102261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 206347828008426683893878725 38690217751580003230102261)
        ·
          refine ⟨3627207914210625302822087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38690217751580003230102261 3627207914210625302822087)
          ·
            refine ⟨5440811871315937954233131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3627207914210625302822087 5440811871315937954233131)
            ·
              refine ⟨8161217806973906931349697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5440811871315937954233131 8161217806973906931349697)
              ·
                refine ⟨6120913355230430198512273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8161217806973906931349697 6120913355230430198512273)
                ·
                  refine ⟨4590685016422822648884205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6120913355230430198512273 4590685016422822648884205)
                  ·
                    refine ⟨1721506881158558493331577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4590685016422822648884205 1721506881158558493331577)
                    ·
                      refine ⟨1291130160868918869998683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1721506881158558493331577 1291130160868918869998683)
                      ·
                        rfl

theorem cell23_2514467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 2, 2, 3, 2].length) (baseStart_2514467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2514467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2514467 prefixEnd_2514467 := by exact prefixLift 2514467
  have htrace : WordTrace (prefixWord ++ tailWord_2514467) baseStart_2514467 baseEnd_2514467 := by
    simpa [prefixWord, tailWord_2514467, baseEnd_2514467] using wordTrace_append hprefix tailTrace_2514467
  have hstable : (prefixWord ++ tailWord_2514467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2514467).length < 2 ^ (prefixWord ++ tailWord_2514467).sum := by decide
  have hdescent : baseEnd_2514467 < baseStart_2514467 := by decide
  rcases family_descends (prefixWord ++ tailWord_2514467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2514483 : List Nat := [1, 1, 1, 2, 4, 3, 2, 2, 1, 1, 5]
def baseStart_2514483 : Nat := 118140960795 + 2514483 * 2 ^ 59
def prefixEnd_2514483 : Nat := 4983230072969 + 3 ^ 40 * 2514483 * 2
def baseEnd_2514483 : Nat := 1291138376559390807398609

theorem tailTrace_2514483 : CollatzResearch.WordTrace tailWord_2514483 prefixEnd_2514483 1291138376559390807398609 := by
  unfold tailWord_2514483
  simp only [CollatzResearch.WordTrace]
  refine ⟨91710729349465005352084103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61140486232976670234722735 91710729349465005352084103)
  ·
    refine ⟨137566094024197508028126155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91710729349465005352084103 137566094024197508028126155)
    ·
      refine ⟨206349141036296262042189233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137566094024197508028126155 206349141036296262042189233)
      ·
        refine ⟨154761855777222196531641925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 206349141036296262042189233 154761855777222196531641925)
        ·
          refine ⟨29017847958229161849682861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 154761855777222196531641925 29017847958229161849682861)
          ·
            refine ⟨10881692984335935693631073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29017847958229161849682861 10881692984335935693631073)
            ·
              refine ⟨8161269738251951770223305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10881692984335935693631073 8161269738251951770223305)
              ·
                refine ⟨6120952303688963827667479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8161269738251951770223305 6120952303688963827667479)
                ·
                  refine ⟨9181428455533445741501219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6120952303688963827667479 9181428455533445741501219)
                  ·
                    refine ⟨13772142683300168612251829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9181428455533445741501219 13772142683300168612251829)
                    ·
                      refine ⟨1291138376559390807398609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13772142683300168612251829 1291138376559390807398609)
                      ·
                        rfl

theorem cell23_2514483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 2, 1, 1, 5].length) (baseStart_2514483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2514483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2514483 prefixEnd_2514483 := by exact prefixLift 2514483
  have htrace : WordTrace (prefixWord ++ tailWord_2514483) baseStart_2514483 baseEnd_2514483 := by
    simpa [prefixWord, tailWord_2514483, baseEnd_2514483] using wordTrace_append hprefix tailTrace_2514483
  have hstable : (prefixWord ++ tailWord_2514483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2514483).length < 2 ^ (prefixWord ++ tailWord_2514483).sum := by decide
  have hdescent : baseEnd_2514483 < baseStart_2514483 := by decide
  rcases family_descends (prefixWord ++ tailWord_2514483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2514490 : List Nat := [3, 1, 1, 1, 3, 2, 3, 3, 2, 4]
def baseStart_2514490 : Nat := 118140960795 + 2514490 * 2 ^ 59
def prefixEnd_2514490 : Nat := 4983230072969 + 3 ^ 40 * 2514490 * 2
def baseEnd_2514490 : Nat := 430380656974657426670359

theorem tailTrace_2514490 : CollatzResearch.WordTrace tailWord_2514490 prefixEnd_2514490 430380656974657426670359 := by
  unfold tailWord_2514490
  simp only [CollatzResearch.WordTrace]
  refine ⟨22927746165109911386897231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61140656440293097031725949 22927746165109911386897231)
  ·
    refine ⟨34391619247664867080345847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22927746165109911386897231 34391619247664867080345847)
    ·
      refine ⟨51587428871497300620518771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34391619247664867080345847 51587428871497300620518771)
      ·
        refine ⟨77381143307245950930778157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51587428871497300620518771 77381143307245950930778157)
        ·
          refine ⟨29017928740217231599041809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77381143307245950930778157 29017928740217231599041809)
          ·
            refine ⟨21763446555162923699281357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29017928740217231599041809 21763446555162923699281357)
            ·
              refine ⟨8161292458186096387230509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21763446555162923699281357 8161292458186096387230509)
              ·
                refine ⟨3060484671819786145211441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8161292458186096387230509 3060484671819786145211441)
                ·
                  refine ⟨2295363503864839608908581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3060484671819786145211441 2295363503864839608908581)
                  ·
                    refine ⟨430380656974657426670359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2295363503864839608908581 430380656974657426670359)
                    ·
                      rfl

theorem cell23_2514490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 3, 2, 4].length) (baseStart_2514490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2514490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2514490 prefixEnd_2514490 := by exact prefixLift 2514490
  have htrace : WordTrace (prefixWord ++ tailWord_2514490) baseStart_2514490 baseEnd_2514490 := by
    simpa [prefixWord, tailWord_2514490, baseEnd_2514490] using wordTrace_append hprefix tailTrace_2514490
  have hstable : (prefixWord ++ tailWord_2514490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2514490).length < 2 ^ (prefixWord ++ tailWord_2514490).sum := by decide
  have hdescent : baseEnd_2514490 < baseStart_2514490 := by decide
  rcases family_descends (prefixWord ++ tailWord_2514490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2514497 : List Nat := [1, 2, 5, 1, 1, 1, 2, 1, 5, 2, 2]
def baseStart_2514497 : Nat := 118140960795 + 2514497 * 2 ^ 59
def prefixEnd_2514497 : Nat := 4983230072969 + 3 ^ 40 * 2514497 * 2
def baseEnd_2514497 : Nat := 1291145565288553752623545

theorem tailTrace_2514497 : CollatzResearch.WordTrace tailWord_2514497 prefixEnd_2514497 1291145565288553752623545 := by
  unfold tailWord_2514497
  simp only [CollatzResearch.WordTrace]
  refine ⟨91711239971414285743093745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61140826647609523828729163 91711239971414285743093745)
  ·
    refine ⟨68783429978560714307320309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91711239971414285743093745 68783429978560714307320309)
    ·
      refine ⟨6448446560490066966311279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 68783429978560714307320309 6448446560490066966311279)
      ·
        refine ⟨9672669840735100449466919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6448446560490066966311279 9672669840735100449466919)
        ·
          refine ⟨14509004761102650674200379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9672669840735100449466919 14509004761102650674200379)
          ·
            refine ⟨21763507141653976011300569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14509004761102650674200379 21763507141653976011300569)
            ·
              refine ⟨16322630356240482008475427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21763507141653976011300569 16322630356240482008475427)
              ·
                refine ⟨24483945534360723012713141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16322630356240482008475427 24483945534360723012713141)
                ·
                  refine ⟨2295369893846317782441857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24483945534360723012713141 2295369893846317782441857)
                  ·
                    refine ⟨1721527420384738336831393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2295369893846317782441857 1721527420384738336831393)
                    ·
                      refine ⟨1291145565288553752623545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1721527420384738336831393 1291145565288553752623545)
                      ·
                        rfl

theorem cell23_2514497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 1, 5, 2, 2].length) (baseStart_2514497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2514497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2514497 prefixEnd_2514497 := by exact prefixLift 2514497
  have htrace : WordTrace (prefixWord ++ tailWord_2514497) baseStart_2514497 baseEnd_2514497 := by
    simpa [prefixWord, tailWord_2514497, baseEnd_2514497] using wordTrace_append hprefix tailTrace_2514497
  have hstable : (prefixWord ++ tailWord_2514497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2514497).length < 2 ^ (prefixWord ++ tailWord_2514497).sum := by decide
  have hdescent : baseEnd_2514497 < baseStart_2514497 := by decide
  rcases family_descends (prefixWord ++ tailWord_2514497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2514525 : List Nat := [1, 4, 4, 2, 1, 2, 2, 2, 1, 1, 3]
def baseStart_2514525 : Nat := 118140960795 + 2514525 * 2 ^ 59
def prefixEnd_2514525 : Nat := 4983230072969 + 3 ^ 40 * 2514525 * 2
def baseEnd_2514525 : Nat := 1291159942746879643073417

theorem tailTrace_2514525 : CollatzResearch.WordTrace tailWord_2514525 prefixEnd_2514525 1291159942746879643073417 := by
  unfold tailWord_2514525
  simp only [CollatzResearch.WordTrace]
  refine ⟨91712261215312846525113029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61141507476875231016742019 91712261215312846525113029)
  ·
    refine ⟨17196048977871158723458693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 91712261215312846525113029 17196048977871158723458693)
    ·
      refine ⟨3224259183350842260648505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17196048977871158723458693 3224259183350842260648505)
      ·
        refine ⟨2418194387513131695486379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3224259183350842260648505 2418194387513131695486379)
        ·
          refine ⟨3627291581269697543229569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2418194387513131695486379 3627291581269697543229569)
          ·
            refine ⟨2720468685952273157422177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3627291581269697543229569 2720468685952273157422177)
            ·
              refine ⟨2040351514464204868066633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2720468685952273157422177 2040351514464204868066633)
              ·
                refine ⟨1530263635848153651049975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2040351514464204868066633 1530263635848153651049975)
                ·
                  refine ⟨2295395453772230476574963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1530263635848153651049975 2295395453772230476574963)
                  ·
                    refine ⟨3443093180658345714862445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2295395453772230476574963 3443093180658345714862445)
                    ·
                      refine ⟨1291159942746879643073417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3443093180658345714862445 1291159942746879643073417)
                      ·
                        rfl

theorem cell23_2514525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 2, 2, 1, 1, 3].length) (baseStart_2514525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2514525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2514525 prefixEnd_2514525 := by exact prefixLift 2514525
  have htrace : WordTrace (prefixWord ++ tailWord_2514525) baseStart_2514525 baseEnd_2514525 := by
    simpa [prefixWord, tailWord_2514525, baseEnd_2514525] using wordTrace_append hprefix tailTrace_2514525
  have hstable : (prefixWord ++ tailWord_2514525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2514525).length < 2 ^ (prefixWord ++ tailWord_2514525).sum := by decide
  have hdescent : baseEnd_2514525 < baseStart_2514525 := by decide
  rcases family_descends (prefixWord ++ tailWord_2514525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2514531 : List Nat := [1, 1, 1, 5, 1, 3, 4, 2, 1, 2, 2]
def baseStart_2514531 : Nat := 118140960795 + 2514531 * 2 ^ 59
def prefixEnd_2514531 : Nat := 4983230072969 + 3 ^ 40 * 2514531 * 2
def baseEnd_2514531 : Nat := 1291163023630806619598389

theorem tailTrace_2514531 : CollatzResearch.WordTrace tailWord_2514531 prefixEnd_2514531 1291163023630806619598389 := by
  unfold tailWord_2514531
  simp only [CollatzResearch.WordTrace]
  refine ⟨91712480053291109549831447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61141653368860739699887631 91712480053291109549831447)
  ·
    refine ⟨137568720079936664324747171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91712480053291109549831447 137568720079936664324747171)
    ·
      refine ⟨206353080119904996487120757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137568720079936664324747171 206353080119904996487120757)
      ·
        refine ⟨19345601261241093420667571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 206353080119904996487120757 19345601261241093420667571)
        ·
          refine ⟨29018401891861640131001357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19345601261241093420667571 29018401891861640131001357)
          ·
            refine ⟨10881900709448115049125509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29018401891861640131001357 10881900709448115049125509)
            ·
              refine ⟨2040356383021521571711033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10881900709448115049125509 2040356383021521571711033)
              ·
                refine ⟨1530267287266141178783275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2040356383021521571711033 1530267287266141178783275)
                ·
                  refine ⟨2295400930899211768174913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1530267287266141178783275 2295400930899211768174913)
                  ·
                    refine ⟨1721550698174408826131185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2295400930899211768174913 1721550698174408826131185)
                    ·
                      refine ⟨1291163023630806619598389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1721550698174408826131185 1291163023630806619598389)
                      ·
                        rfl

theorem cell23_2514531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 4, 2, 1, 2, 2].length) (baseStart_2514531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2514531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2514531 prefixEnd_2514531 := by exact prefixLift 2514531
  have htrace : WordTrace (prefixWord ++ tailWord_2514531) baseStart_2514531 baseEnd_2514531 := by
    simpa [prefixWord, tailWord_2514531, baseEnd_2514531] using wordTrace_append hprefix tailTrace_2514531
  have hstable : (prefixWord ++ tailWord_2514531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2514531).length < 2 ^ (prefixWord ++ tailWord_2514531).sum := by decide
  have hdescent : baseEnd_2514531 < baseStart_2514531 := by decide
  rcases family_descends (prefixWord ++ tailWord_2514531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2514533 : List Nat := [1, 3, 1, 3, 3, 1, 1, 1, 2, 7]
def baseStart_2514533 : Nat := 118140960795 + 2514533 * 2 ^ 59
def prefixEnd_2514533 : Nat := 4983230072969 + 3 ^ 40 * 2514533 * 2
def baseEnd_2514533 : Nat := 430388016864038537257793

theorem tailTrace_2514533 : CollatzResearch.WordTrace tailWord_2514533 prefixEnd_2514533 430388016864038537257793 := by
  unfold tailWord_2514533
  simp only [CollatzResearch.WordTrace]
  refine ⟨91712552999283863891404253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61141701999522575927602835 91712552999283863891404253)
  ·
    refine ⟨34392207374731448959276595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91712552999283863891404253 34392207374731448959276595)
    ·
      refine ⟨51588311062097173438914893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34392207374731448959276595 51588311062097173438914893)
      ·
        refine ⟨19345616648286440039593085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51588311062097173438914893 19345616648286440039593085)
        ·
          refine ⟨7254606243107415014847407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19345616648286440039593085 7254606243107415014847407)
          ·
            refine ⟨10881909364661122522271111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7254606243107415014847407 10881909364661122522271111)
            ·
              refine ⟨16322864046991683783406667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10881909364661122522271111 16322864046991683783406667)
              ·
                refine ⟨24484296070487525675110001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16322864046991683783406667 24484296070487525675110001)
                ·
                  refine ⟨18363222052865644256332501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24484296070487525675110001 18363222052865644256332501)
                  ·
                    refine ⟨430388016864038537257793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18363222052865644256332501 430388016864038537257793)
                    ·
                      rfl

theorem cell23_2514533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 1, 2, 7].length) (baseStart_2514533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2514533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2514533 prefixEnd_2514533 := by exact prefixLift 2514533
  have htrace : WordTrace (prefixWord ++ tailWord_2514533) baseStart_2514533 baseEnd_2514533 := by
    simpa [prefixWord, tailWord_2514533, baseEnd_2514533] using wordTrace_append hprefix tailTrace_2514533
  have hstable : (prefixWord ++ tailWord_2514533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2514533).length < 2 ^ (prefixWord ++ tailWord_2514533).sum := by decide
  have hdescent : baseEnd_2514533 < baseStart_2514533 := by decide
  rcases family_descends (prefixWord ++ tailWord_2514533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2514553 : List Nat := [1, 2, 1, 3, 3, 1, 1, 2, 2, 3, 4]
def baseStart_2514553 : Nat := 118140960795 + 2514553 * 2 ^ 59
def prefixEnd_2514553 : Nat := 4983230072969 + 3 ^ 40 * 2514553 * 2
def baseEnd_2514553 : Nat := 1291174320205205533523287

theorem tailTrace_2514553 : CollatzResearch.WordTrace tailWord_2514553 prefixEnd_2514553 1291174320205205533523287 := by
  unfold tailWord_2514553
  simp only [CollatzResearch.WordTrace]
  refine ⟨91713282459211407307132313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61142188306140938204754875 91713282459211407307132313)
  ·
    refine ⟨68784961844408555480349235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91713282459211407307132313 68784961844408555480349235)
    ·
      refine ⟨103177442766612833220523853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68784961844408555480349235 103177442766612833220523853)
      ·
        refine ⟨38691541037479812457696445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103177442766612833220523853 38691541037479812457696445)
        ·
          refine ⟨14509327889054929671636167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38691541037479812457696445 14509327889054929671636167)
          ·
            refine ⟨21763991833582394507454251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14509327889054929671636167 21763991833582394507454251)
            ·
              refine ⟨32645987750373591761181377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21763991833582394507454251 32645987750373591761181377)
              ·
                refine ⟨24484490812780193820886033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32645987750373591761181377 24484490812780193820886033)
                ·
                  refine ⟨18363368109585145365664525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24484490812780193820886033 18363368109585145365664525)
                  ·
                    refine ⟨6886263041094429512124197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18363368109585145365664525 6886263041094429512124197)
                    ·
                      refine ⟨1291174320205205533523287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6886263041094429512124197 1291174320205205533523287)
                      ·
                        rfl

theorem cell23_2514553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 2, 2, 3, 4].length) (baseStart_2514553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2514553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2514553 prefixEnd_2514553 := by exact prefixLift 2514553
  have htrace : WordTrace (prefixWord ++ tailWord_2514553) baseStart_2514553 baseEnd_2514553 := by
    simpa [prefixWord, tailWord_2514553, baseEnd_2514553] using wordTrace_append hprefix tailTrace_2514553
  have hstable : (prefixWord ++ tailWord_2514553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2514553).length < 2 ^ (prefixWord ++ tailWord_2514553).sum := by decide
  have hdescent : baseEnd_2514553 < baseStart_2514553 := by decide
  rcases family_descends (prefixWord ++ tailWord_2514553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2514557 : List Nat := [1, 4, 1, 1, 4, 1, 2, 1, 3, 3, 2]
def baseStart_2514557 : Nat := 118140960795 + 2514557 * 2 ^ 59
def prefixEnd_2514557 : Nat := 4983230072969 + 3 ^ 40 * 2514557 * 2
def baseEnd_2514557 : Nat := 1291176374127823517873269

theorem tailTrace_2514557 : CollatzResearch.WordTrace tailWord_2514557 prefixEnd_2514557 1291176374127823517873269 := by
  unfold tailWord_2514557
  simp only [CollatzResearch.WordTrace]
  refine ⟨91713428351196915990277925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61142285567464610660185283 91713428351196915990277925)
  ·
    refine ⟨17196267815849421748177111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 91713428351196915990277925 17196267815849421748177111)
    ·
      refine ⟨25794401723774132622265667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17196267815849421748177111 25794401723774132622265667)
      ·
        refine ⟨38691602585661198933398501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25794401723774132622265667 38691602585661198933398501)
        ·
          refine ⟨7254675484811474800012219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38691602585661198933398501 7254675484811474800012219)
          ·
            refine ⟨10882013227217212200018329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7254675484811474800012219 10882013227217212200018329)
            ·
              refine ⟨8161509920412909150013747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10882013227217212200018329 8161509920412909150013747)
              ·
                refine ⟨12242264880619363725020621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8161509920412909150013747 12242264880619363725020621)
                ·
                  refine ⟨4590849330232261396882733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12242264880619363725020621 4590849330232261396882733)
                  ·
                    refine ⟨1721568498837098023831025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4590849330232261396882733 1721568498837098023831025)
                    ·
                      refine ⟨1291176374127823517873269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1721568498837098023831025 1291176374127823517873269)
                      ·
                        rfl

theorem cell23_2514557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 1, 3, 3, 2].length) (baseStart_2514557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2514557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2514557 prefixEnd_2514557 := by exact prefixLift 2514557
  have htrace : WordTrace (prefixWord ++ tailWord_2514557) baseStart_2514557 baseEnd_2514557 := by
    simpa [prefixWord, tailWord_2514557, baseEnd_2514557] using wordTrace_append hprefix tailTrace_2514557
  have hstable : (prefixWord ++ tailWord_2514557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2514557).length < 2 ^ (prefixWord ++ tailWord_2514557).sum := by decide
  have hdescent : baseEnd_2514557 < baseStart_2514557 := by decide
  rcases family_descends (prefixWord ++ tailWord_2514557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2514568 : List Nat := [2, 1, 3, 5, 2, 1, 2, 1, 1, 2, 3]
def baseStart_2514568 : Nat := 118140960795 + 2514568 * 2 ^ 59
def prefixEnd_2514568 : Nat := 4983230072969 + 3 ^ 40 * 2514568 * 2
def baseEnd_2514568 : Nat := 1291182022415022974835719

theorem tailTrace_2514568 : CollatzResearch.WordTrace tailWord_2514568 prefixEnd_2514568 1291182022415022974835719 := by
  unfold tailWord_2514568
  simp only [CollatzResearch.WordTrace]
  refine ⟨45856914777078532434464179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61142553036104709912618905 45856914777078532434464179)
  ·
    refine ⟨68785372165617798651696269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45856914777078532434464179 68785372165617798651696269)
    ·
      refine ⟨25794514562106674494386101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68785372165617798651696269 25794514562106674494386101)
      ·
        refine ⟨2418235740197500733848697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25794514562106674494386101 2418235740197500733848697)
        ·
          refine ⟨1813676805148125550386523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2418235740197500733848697 1813676805148125550386523)
          ·
            refine ⟨2720515207722188325579785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1813676805148125550386523 2720515207722188325579785)
            ·
              refine ⟨2040386405791641244184839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2720515207722188325579785 2040386405791641244184839)
              ·
                refine ⟨3060579608687461866277259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2040386405791641244184839 3060579608687461866277259)
                ·
                  refine ⟨4590869413031192799415889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3060579608687461866277259 4590869413031192799415889)
                  ·
                    refine ⟨3443152059773394599561917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4590869413031192799415889 3443152059773394599561917)
                    ·
                      refine ⟨1291182022415022974835719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3443152059773394599561917 1291182022415022974835719)
                      ·
                        rfl

theorem cell23_2514568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_2514568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2514568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2514568 prefixEnd_2514568 := by exact prefixLift 2514568
  have htrace : WordTrace (prefixWord ++ tailWord_2514568) baseStart_2514568 baseEnd_2514568 := by
    simpa [prefixWord, tailWord_2514568, baseEnd_2514568] using wordTrace_append hprefix tailTrace_2514568
  have hstable : (prefixWord ++ tailWord_2514568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2514568).length < 2 ^ (prefixWord ++ tailWord_2514568).sum := by decide
  have hdescent : baseEnd_2514568 < baseStart_2514568 := by decide
  rcases family_descends (prefixWord ++ tailWord_2514568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2514574 : List Nat := [4, 1, 1, 3, 1, 3, 1, 3, 1, 3, 2]
def baseStart_2514574 : Nat := 118140960795 + 2514574 * 2 ^ 59
def prefixEnd_2514574 : Nat := 4983230072969 + 3 ^ 40 * 2514574 * 2
def baseEnd_2514574 : Nat := 1291185103298949951360691

theorem tailTrace_2514574 : CollatzResearch.WordTrace tailWord_2514574 prefixEnd_2514574 1291185103298949951360691 := by
  unfold tailWord_2514574
  simp only [CollatzResearch.WordTrace]
  refine ⟨11464256049016915986705847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61142698928090218595764517 11464256049016915986705847)
  ·
    refine ⟨17196384073525373980058771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11464256049016915986705847 17196384073525373980058771)
    ·
      refine ⟨25794576110288060970088157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17196384073525373980058771 25794576110288060970088157)
      ·
        refine ⟨9672966041358022863783059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25794576110288060970088157 9672966041358022863783059)
        ·
          refine ⟨14509449062037034295674589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9672966041358022863783059 14509449062037034295674589)
          ·
            refine ⟨5441043398263887860877971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14509449062037034295674589 5441043398263887860877971)
            ·
              refine ⟨8161565097395831791316957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5441043398263887860877971 8161565097395831791316957)
              ·
                refine ⟨3060586911523436921743859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8161565097395831791316957 3060586911523436921743859)
                ·
                  refine ⟨4590880367285155382615789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3060586911523436921743859 4590880367285155382615789)
                  ·
                    refine ⟨1721580137731933268480921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4590880367285155382615789 1721580137731933268480921)
                    ·
                      refine ⟨1291185103298949951360691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1721580137731933268480921 1291185103298949951360691)
                      ·
                        rfl

theorem cell23_2514574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 3, 1, 3, 2].length) (baseStart_2514574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2514574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2514574 prefixEnd_2514574 := by exact prefixLift 2514574
  have htrace : WordTrace (prefixWord ++ tailWord_2514574) baseStart_2514574 baseEnd_2514574 := by
    simpa [prefixWord, tailWord_2514574, baseEnd_2514574] using wordTrace_append hprefix tailTrace_2514574
  have hstable : (prefixWord ++ tailWord_2514574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2514574).length < 2 ^ (prefixWord ++ tailWord_2514574).sum := by decide
  have hdescent : baseEnd_2514574 < baseStart_2514574 := by decide
  rcases family_descends (prefixWord ++ tailWord_2514574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2514623 : List Nat := [1, 1, 2, 2, 2, 3, 1, 3, 1, 7]
def baseStart_2514623 : Nat := 118140960795 + 2514623 * 2 ^ 59
def prefixEnd_2514623 : Nat := 4983230072969 + 3 ^ 40 * 2514623 * 2
def baseEnd_2514623 : Nat := 430403421283673419882655

theorem tailTrace_2514623 : CollatzResearch.WordTrace tailWord_2514623 prefixEnd_2514623 430403421283673419882655 := by
  unfold tailWord_2514623
  simp only [CollatzResearch.WordTrace]
  refine ⟨91715835568957809262180523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61143890379305206174787015 91715835568957809262180523)
  ·
    refine ⟨137573753353436713893270785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91715835568957809262180523 137573753353436713893270785)
    ·
      refine ⟨103180315015077535419953089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137573753353436713893270785 103180315015077535419953089)
      ·
        refine ⟨77385236261308151564964817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103180315015077535419953089 77385236261308151564964817)
        ·
          refine ⟨58038927195981113673723613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77385236261308151564964817 58038927195981113673723613)
          ·
            refine ⟨21764597698492917627646355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58038927195981113673723613 21764597698492917627646355)
            ·
              refine ⟨32646896547739376441469533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21764597698492917627646355 32646896547739376441469533)
              ·
                refine ⟨12242586205402266165551075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32646896547739376441469533 12242586205402266165551075)
                ·
                  refine ⟨18363879308103399248326613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12242586205402266165551075 18363879308103399248326613)
                  ·
                    refine ⟨430403421283673419882655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18363879308103399248326613 430403421283673419882655)
                    ·
                      rfl

theorem cell23_2514623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 3, 1, 7].length) (baseStart_2514623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2514623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2514623 prefixEnd_2514623 := by exact prefixLift 2514623
  have htrace : WordTrace (prefixWord ++ tailWord_2514623) baseStart_2514623 baseEnd_2514623 := by
    simpa [prefixWord, tailWord_2514623, baseEnd_2514623] using wordTrace_append hprefix tailTrace_2514623
  have hstable : (prefixWord ++ tailWord_2514623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2514623).length < 2 ^ (prefixWord ++ tailWord_2514623).sum := by decide
  have hdescent : baseEnd_2514623 < baseStart_2514623 := by decide
  rcases family_descends (prefixWord ++ tailWord_2514623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2514650 : List Nat := [3, 1, 1, 2, 2, 4, 1, 1, 1, 2, 5]
def baseStart_2514650 : Nat := 118140960795 + 2514650 * 2 ^ 59
def prefixEnd_2514650 : Nat := 4983230072969 + 3 ^ 40 * 2514650 * 2
def baseEnd_2514650 : Nat := 1291224127828691654010341

theorem tailTrace_2514650 : CollatzResearch.WordTrace tailWord_2514650 prefixEnd_2514650 1291224127828691654010341 := by
  unfold tailWord_2514650
  simp only [CollatzResearch.WordTrace]
  refine ⟨22929205084964998218353351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61144546893239995248942269 22929205084964998218353351)
  ·
    refine ⟨34393807627447497327530027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22929205084964998218353351 34393807627447497327530027)
    ·
      refine ⟨51590711441171245991295041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34393807627447497327530027 51590711441171245991295041)
      ·
        refine ⟨38693033580878434493471281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51590711441171245991295041 38693033580878434493471281)
        ·
          refine ⟨29019775185658825870103461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38693033580878434493471281 29019775185658825870103461)
          ·
            refine ⟨5441207847311029850644399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29019775185658825870103461 5441207847311029850644399)
            ·
              refine ⟨8161811770966544775966599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5441207847311029850644399 8161811770966544775966599)
              ·
                refine ⟨12242717656449817163949899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8161811770966544775966599 12242717656449817163949899)
                ·
                  refine ⟨18364076484674725745924849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12242717656449817163949899 18364076484674725745924849)
                  ·
                    refine ⟨13773057363506044309443637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18364076484674725745924849 13773057363506044309443637)
                    ·
                      refine ⟨1291224127828691654010341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13773057363506044309443637 1291224127828691654010341)
                      ·
                        rfl

theorem cell23_2514650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 1, 1, 2, 5].length) (baseStart_2514650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2514650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2514650 prefixEnd_2514650 := by exact prefixLift 2514650
  have htrace : WordTrace (prefixWord ++ tailWord_2514650) baseStart_2514650 baseEnd_2514650 := by
    simpa [prefixWord, tailWord_2514650, baseEnd_2514650] using wordTrace_append hprefix tailTrace_2514650
  have hstable : (prefixWord ++ tailWord_2514650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2514650).length < 2 ^ (prefixWord ++ tailWord_2514650).sum := by decide
  have hdescent : baseEnd_2514650 < baseStart_2514650 := by decide
  rcases family_descends (prefixWord ++ tailWord_2514650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2514660 : List Nat := [2, 3, 1, 1, 1, 3, 1, 2, 4, 1, 4]
def baseStart_2514660 : Nat := 118140960795 + 2514660 * 2 ^ 59
def prefixEnd_2514660 : Nat := 4983230072969 + 3 ^ 40 * 2514660 * 2
def baseEnd_2514660 : Nat := 1291229262635236614885295

theorem tailTrace_2514660 : CollatzResearch.WordTrace tailWord_2514660 prefixEnd_2514660 1291229262635236614885295 := by
  unfold tailWord_2514660
  simp only [CollatzResearch.WordTrace]
  refine ⟨45858592534911882290638717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61144790046549176387518289 45858592534911882290638717)
  ·
    refine ⟨17196972200591955858989519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45858592534911882290638717 17196972200591955858989519)
    ·
      refine ⟨25795458300887933788484279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17196972200591955858989519 25795458300887933788484279)
      ·
        refine ⟨38693187451331900682726419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25795458300887933788484279 38693187451331900682726419)
        ·
          refine ⟨58039781176997851024089629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38693187451331900682726419 58039781176997851024089629)
          ·
            refine ⟨21764917941374194134033611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58039781176997851024089629 21764917941374194134033611)
            ·
              refine ⟨32647376912061291201050417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21764917941374194134033611 32647376912061291201050417)
              ·
                refine ⟨24485532684045968400787813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32647376912061291201050417 24485532684045968400787813)
                ·
                  refine ⟨4591037378258619075147715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24485532684045968400787813 4591037378258619075147715)
                  ·
                    refine ⟨6886556067387928612721573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4591037378258619075147715 6886556067387928612721573)
                    ·
                      refine ⟨1291229262635236614885295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6886556067387928612721573 1291229262635236614885295)
                      ·
                        rfl

theorem cell23_2514660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 2, 4, 1, 4].length) (baseStart_2514660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2514660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2514660 prefixEnd_2514660 := by exact prefixLift 2514660
  have htrace : WordTrace (prefixWord ++ tailWord_2514660) baseStart_2514660 baseEnd_2514660 := by
    simpa [prefixWord, tailWord_2514660, baseEnd_2514660] using wordTrace_append hprefix tailTrace_2514660
  have hstable : (prefixWord ++ tailWord_2514660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2514660).length < 2 ^ (prefixWord ++ tailWord_2514660).sum := by decide
  have hdescent : baseEnd_2514660 < baseStart_2514660 := by decide
  rcases family_descends (prefixWord ++ tailWord_2514660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2514683 : List Nat := [1, 1, 1, 1, 1, 3, 1, 6, 8]
def baseStart_2514683 : Nat := 118140960795 + 2514683 * 2 ^ 59
def prefixEnd_2514683 : Nat := 4983230072969 + 3 ^ 40 * 2514683 * 2
def baseEnd_2514683 : Nat := 143471230298921113877521

theorem tailTrace_2514683 : CollatzResearch.WordTrace tailWord_2514683 prefixEnd_2514683 143471230298921113877521 := by
  unfold tailWord_2514683
  simp only [CollatzResearch.WordTrace]
  refine ⟨91718023948740439509364703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61145349299160293006243135 91718023948740439509364703)
  ·
    refine ⟨137577035923110659264047055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91718023948740439509364703 137577035923110659264047055)
    ·
      refine ⟨206365553884665988896070583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137577035923110659264047055 206365553884665988896070583)
      ·
        refine ⟨309548330826998983344105875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206365553884665988896070583 309548330826998983344105875)
        ·
          refine ⟨464322496240498475016158813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 309548330826998983344105875 464322496240498475016158813)
          ·
            refine ⟨174120936090186928131059555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 464322496240498475016158813 174120936090186928131059555)
            ·
              refine ⟨261181404135280392196589333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 174120936090186928131059555 261181404135280392196589333)
              ·
                refine ⟨12242878318841268384215125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 261181404135280392196589333 12242878318841268384215125)
                ·
                  refine ⟨143471230298921113877521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12242878318841268384215125 143471230298921113877521)
                  ·
                    rfl

theorem cell23_2514683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 6, 8].length) (baseStart_2514683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2514683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2514683 prefixEnd_2514683 := by exact prefixLift 2514683
  have htrace : WordTrace (prefixWord ++ tailWord_2514683) baseStart_2514683 baseEnd_2514683 := by
    simpa [prefixWord, tailWord_2514683, baseEnd_2514683] using wordTrace_append hprefix tailTrace_2514683
  have hstable : (prefixWord ++ tailWord_2514683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2514683).length < 2 ^ (prefixWord ++ tailWord_2514683).sum := by decide
  have hdescent : baseEnd_2514683 < baseStart_2514683 := by decide
  rcases family_descends (prefixWord ++ tailWord_2514683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2514700 : List Nat := [2, 2, 1, 2, 2, 1, 3, 4, 6]
def baseStart_2514700 : Nat := 118140960795 + 2514700 * 2 ^ 59
def prefixEnd_2514700 : Nat := 4983230072969 + 3 ^ 40 * 2514700 * 2
def baseEnd_2514700 : Nat := 143472200206824050931679

theorem tailTrace_2514700 : CollatzResearch.WordTrace tailWord_2514700 prefixEnd_2514700 143472200206824050931679 := by
  unfold tailWord_2514700
  simp only [CollatzResearch.WordTrace]
  refine ⟨45859321994839425706366777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61145762659785900941822369 45859321994839425706366777)
  ·
    refine ⟨34394491496129569279775083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45859321994839425706366777 34394491496129569279775083)
    ·
      refine ⟨51591737244194353919662625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34394491496129569279775083 51591737244194353919662625)
      ·
        refine ⟨38693802933145765439746969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51591737244194353919662625 38693802933145765439746969)
        ·
          refine ⟨29020352199859324079810227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38693802933145765439746969 29020352199859324079810227)
          ·
            refine ⟨43530528299788986119715341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29020352199859324079810227 43530528299788986119715341)
            ·
              refine ⟨16323948112420869794893253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43530528299788986119715341 16323948112420869794893253)
              ·
                refine ⟨3060740271078913086542485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16323948112420869794893253 3060740271078913086542485)
                ·
                  refine ⟨143472200206824050931679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3060740271078913086542485 143472200206824050931679)
                  ·
                    rfl

theorem cell23_2514700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 4, 6].length) (baseStart_2514700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2514700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2514700 prefixEnd_2514700 := by exact prefixLift 2514700
  have htrace : WordTrace (prefixWord ++ tailWord_2514700) baseStart_2514700 baseEnd_2514700 := by
    simpa [prefixWord, tailWord_2514700, baseEnd_2514700] using wordTrace_append hprefix tailTrace_2514700
  have hstable : (prefixWord ++ tailWord_2514700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2514700).length < 2 ^ (prefixWord ++ tailWord_2514700).sum := by decide
  have hdescent : baseEnd_2514700 < baseStart_2514700 := by decide
  rcases family_descends (prefixWord ++ tailWord_2514700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2514784 : List Nat := [2, 1, 1, 3, 3, 3, 2, 2, 1, 1, 4]
def baseStart_2514784 : Nat := 118140960795 + 2514784 * 2 ^ 59
def prefixEnd_2514784 : Nat := 4983230072969 + 3 ^ 40 * 2514784 * 2
def baseEnd_2514784 : Nat := 1291292934236394129734725

theorem tailTrace_2514784 : CollatzResearch.WordTrace tailWord_2514784 prefixEnd_2514784 1291292934236394129734725 := by
  unfold tailWord_2514784
  simp only [CollatzResearch.WordTrace]
  refine ⟨45860853860687266879395703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61147805147583022505860937 45860853860687266879395703)
  ·
    refine ⟨68791280791030900319093555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45860853860687266879395703 68791280791030900319093555)
    ·
      refine ⟨103186921186546350478640333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68791280791030900319093555 103186921186546350478640333)
      ·
        refine ⟨38695095444954881429490125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103186921186546350478640333 38695095444954881429490125)
        ·
          refine ⟨14510660791858080536058797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38695095444954881429490125 14510660791858080536058797)
          ·
            refine ⟨5441497796946780201022049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14510660791858080536058797 5441497796946780201022049)
            ·
              refine ⟨4081123347710085150766537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5441497796946780201022049 4081123347710085150766537)
              ·
                refine ⟨3060842510782563863074903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4081123347710085150766537 3060842510782563863074903)
                ·
                  refine ⟨4591263766173845794612355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3060842510782563863074903 4591263766173845794612355)
                  ·
                    refine ⟨6886895649260768691918533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4591263766173845794612355 6886895649260768691918533)
                    ·
                      refine ⟨1291292934236394129734725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6886895649260768691918533 1291292934236394129734725)
                      ·
                        rfl

theorem cell23_2514784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 2, 2, 1, 1, 4].length) (baseStart_2514784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2514784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2514784 prefixEnd_2514784 := by exact prefixLift 2514784
  have htrace : WordTrace (prefixWord ++ tailWord_2514784) baseStart_2514784 baseEnd_2514784 := by
    simpa [prefixWord, tailWord_2514784, baseEnd_2514784] using wordTrace_append hprefix tailTrace_2514784
  have hstable : (prefixWord ++ tailWord_2514784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2514784).length < 2 ^ (prefixWord ++ tailWord_2514784).sum := by decide
  have hdescent : baseEnd_2514784 < baseStart_2514784 := by decide
  rcases family_descends (prefixWord ++ tailWord_2514784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2514797 : List Nat := [1, 5, 1, 1, 1, 1, 2, 4, 1, 2, 4]
def baseStart_2514797 : Nat := 118140960795 + 2514797 * 2 ^ 59
def prefixEnd_2514797 : Nat := 4983230072969 + 3 ^ 40 * 2514797 * 2
def baseEnd_2514797 : Nat := 1291299609484902578872165

theorem tailTrace_2514797 : CollatzResearch.WordTrace tailWord_2514797 prefixEnd_2514797 1291299609484902578872165 := by
  unfold tailWord_2514797
  simp only [CollatzResearch.WordTrace]
  refine ⟨91722181870327436979014645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61148121246884957986009763 91722181870327436979014645)
  ·
    refine ⟨8598954550343197216782623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 91722181870327436979014645 8598954550343197216782623)
    ·
      refine ⟨12898431825514795825173935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8598954550343197216782623 12898431825514795825173935)
      ·
        refine ⟨19347647738272193737760903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12898431825514795825173935 19347647738272193737760903)
        ·
          refine ⟨29021471607408290606641355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19347647738272193737760903 29021471607408290606641355)
          ·
            refine ⟨43532207411112435909962033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29021471607408290606641355 43532207411112435909962033)
            ·
              refine ⟨32649155558334326932471525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43532207411112435909962033 32649155558334326932471525)
              ·
                refine ⟨6121716667187686299838411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32649155558334326932471525 6121716667187686299838411)
                ·
                  refine ⟨9182575000781529449757617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6121716667187686299838411 9182575000781529449757617)
                  ·
                    refine ⟨6886931250586147087318213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9182575000781529449757617 6886931250586147087318213)
                    ·
                      refine ⟨1291299609484902578872165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6886931250586147087318213 1291299609484902578872165)
                      ·
                        rfl

theorem cell23_2514797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 4, 1, 2, 4].length) (baseStart_2514797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2514797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2514797 prefixEnd_2514797 := by exact prefixLift 2514797
  have htrace : WordTrace (prefixWord ++ tailWord_2514797) baseStart_2514797 baseEnd_2514797 := by
    simpa [prefixWord, tailWord_2514797, baseEnd_2514797] using wordTrace_append hprefix tailTrace_2514797
  have hstable : (prefixWord ++ tailWord_2514797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2514797).length < 2 ^ (prefixWord ++ tailWord_2514797).sum := by decide
  have hdescent : baseEnd_2514797 < baseStart_2514797 := by decide
  rcases family_descends (prefixWord ++ tailWord_2514797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2514814 : List Nat := [4, 2, 3, 1, 1, 1, 1, 2, 1, 1, 6]
def baseStart_2514814 : Nat := 118140960795 + 2514814 * 2 ^ 59
def prefixEnd_2514814 : Nat := 4983230072969 + 3 ^ 40 * 2514814 * 2
def baseEnd_2514814 : Nat := 1291308338656029012359587

theorem tailTrace_2514814 : CollatzResearch.WordTrace tailWord_2514814 prefixEnd_2514814 1291308338656029012359587 := by
  unfold tailWord_2514814
  simp only [CollatzResearch.WordTrace]
  refine ⟨11465350238908231110297937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61148534607510565921588997 11465350238908231110297937)
  ·
    refine ⟨8599012679181173332723453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11465350238908231110297937 8599012679181173332723453)
    ·
      refine ⟨3224629754692939999771295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8599012679181173332723453 3224629754692939999771295)
      ·
        refine ⟨4836944632039409999656943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3224629754692939999771295 4836944632039409999656943)
        ·
          refine ⟨7255416948059114999485415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4836944632039409999656943 7255416948059114999485415)
          ·
            refine ⟨10883125422088672499228123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7255416948059114999485415 10883125422088672499228123)
            ·
              refine ⟨16324688133133008748842185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10883125422088672499228123 16324688133133008748842185)
              ·
                refine ⟨12243516099849756561631639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16324688133133008748842185 12243516099849756561631639)
                ·
                  refine ⟨18365274149774634842447459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12243516099849756561631639 18365274149774634842447459)
                  ·
                    refine ⟨27547911224661952263671189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18365274149774634842447459 27547911224661952263671189)
                    ·
                      refine ⟨1291308338656029012359587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27547911224661952263671189 1291308338656029012359587)
                      ·
                        rfl

theorem cell23_2514814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_2514814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2514814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2514814 prefixEnd_2514814 := by exact prefixLift 2514814
  have htrace : WordTrace (prefixWord ++ tailWord_2514814) baseStart_2514814 baseEnd_2514814 := by
    simpa [prefixWord, tailWord_2514814, baseEnd_2514814] using wordTrace_append hprefix tailTrace_2514814
  have hstable : (prefixWord ++ tailWord_2514814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2514814).length < 2 ^ (prefixWord ++ tailWord_2514814).sum := by decide
  have hdescent : baseEnd_2514814 < baseStart_2514814 := by decide
  rcases family_descends (prefixWord ++ tailWord_2514814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2514827 : List Nat := [1, 1, 1, 1, 4, 2, 1, 1, 2, 7, 2]
def baseStart_2514827 : Nat := 118140960795 + 2514827 * 2 ^ 59
def prefixEnd_2514827 : Nat := 4983230072969 + 3 ^ 40 * 2514827 * 2
def baseEnd_2514827 : Nat := 1291315013904537461497027

theorem tailTrace_2514827 : CollatzResearch.WordTrace tailWord_2514827 prefixEnd_2514827 1291315013904537461497027 := by
  unfold tailWord_2514827
  simp only [CollatzResearch.WordTrace]
  refine ⟨91723276060218752102606735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61148850706812501401737823 91723276060218752102606735)
  ·
    refine ⟨137584914090328128153910103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91723276060218752102606735 137584914090328128153910103)
    ·
      refine ⟨206377371135492192230865155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137584914090328128153910103 206377371135492192230865155)
      ·
        refine ⟨309566056703238288346297733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206377371135492192230865155 309566056703238288346297733)
        ·
          refine ⟨58043635631857179064930825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 309566056703238288346297733 58043635631857179064930825)
          ·
            refine ⟨43532726723892884298698119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58043635631857179064930825 43532726723892884298698119)
            ·
              refine ⟨65299090085839326448047179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43532726723892884298698119 65299090085839326448047179)
              ·
                refine ⟨97948635128758989672070769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65299090085839326448047179 97948635128758989672070769)
                ·
                  refine ⟨73461476346569242254053077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 97948635128758989672070769 73461476346569242254053077)
                  ·
                    refine ⟨1721753351872716615329369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 73461476346569242254053077 1721753351872716615329369)
                    ·
                      refine ⟨1291315013904537461497027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1721753351872716615329369 1291315013904537461497027)
                      ·
                        rfl

theorem cell23_2514827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 2, 7, 2].length) (baseStart_2514827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2514827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2514827 prefixEnd_2514827 := by exact prefixLift 2514827
  have htrace : WordTrace (prefixWord ++ tailWord_2514827) baseStart_2514827 baseEnd_2514827 := by
    simpa [prefixWord, tailWord_2514827, baseEnd_2514827] using wordTrace_append hprefix tailTrace_2514827
  have hstable : (prefixWord ++ tailWord_2514827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2514827).length < 2 ^ (prefixWord ++ tailWord_2514827).sum := by decide
  have hdescent : baseEnd_2514827 < baseStart_2514827 := by decide
  rcases family_descends (prefixWord ++ tailWord_2514827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2514891 : List Nat := [1, 1, 1, 1, 3, 4, 1, 5, 2, 2, 2]
def baseStart_2514891 : Nat := 118140960795 + 2514891 * 2 ^ 59
def prefixEnd_2514891 : Nat := 4983230072969 + 3 ^ 40 * 2514891 * 2
def baseEnd_2514891 : Nat := 1291347876666425211096733

theorem tailTrace_2514891 : CollatzResearch.WordTrace tailWord_2514891 prefixEnd_2514891 1291347876666425211096733 := by
  unfold tailWord_2514891
  simp only [CollatzResearch.WordTrace]
  refine ⟨91725610331986891032936527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61150406887991260688624351 91725610331986891032936527)
  ·
    refine ⟨137588415497980336549404791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91725610331986891032936527 137588415497980336549404791)
    ·
      refine ⟨206382623246970504824107187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137588415497980336549404791 206382623246970504824107187)
      ·
        refine ⟨309573934870455757236160781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206382623246970504824107187 309573934870455757236160781)
        ·
          refine ⟨116090225576420908963560293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 309573934870455757236160781 116090225576420908963560293)
          ·
            refine ⟨21766917295578920430667555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 116090225576420908963560293 21766917295578920430667555)
            ·
              refine ⟨32650375943368380646001333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21766917295578920430667555 32650375943368380646001333)
              ·
                refine ⟨3060972744690785685562625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32650375943368380646001333 3060972744690785685562625)
                ·
                  refine ⟨2295729558518089264171969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3060972744690785685562625 2295729558518089264171969)
                  ·
                    refine ⟨1721797168888566948128977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2295729558518089264171969 1721797168888566948128977)
                    ·
                      refine ⟨1291347876666425211096733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1721797168888566948128977 1291347876666425211096733)
                      ·
                        rfl

theorem cell23_2514891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 5, 2, 2, 2].length) (baseStart_2514891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2514891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2514891 prefixEnd_2514891 := by exact prefixLift 2514891
  have htrace : WordTrace (prefixWord ++ tailWord_2514891) baseStart_2514891 baseEnd_2514891 := by
    simpa [prefixWord, tailWord_2514891, baseEnd_2514891] using wordTrace_append hprefix tailTrace_2514891
  have hstable : (prefixWord ++ tailWord_2514891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2514891).length < 2 ^ (prefixWord ++ tailWord_2514891).sum := by decide
  have hdescent : baseEnd_2514891 < baseStart_2514891 := by decide
  rcases family_descends (prefixWord ++ tailWord_2514891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2514925 : List Nat := [1, 5, 1, 4, 1, 1, 1, 1, 4, 2, 2]
def baseStart_2514925 : Nat := 118140960795 + 2514925 * 2 ^ 59
def prefixEnd_2514925 : Nat := 4983230072969 + 3 ^ 40 * 2514925 * 2
def baseEnd_2514925 : Nat := 1291365335008678078071577

theorem tailTrace_2514925 : CollatzResearch.WordTrace tailWord_2514925 prefixEnd_2514925 1291365335008678078071577 := by
  unfold tailWord_2514925
  simp only [CollatzResearch.WordTrace]
  refine ⟨91726850413863714839674229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61151233609242476559782819 91726850413863714839674229)
  ·
    refine ⟨8599392226299723266219459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 91726850413863714839674229 8599392226299723266219459)
    ·
      refine ⟨12899088339449584899329189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8599392226299723266219459 12899088339449584899329189)
      ·
        refine ⟨2418579063646797168624223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12899088339449584899329189 2418579063646797168624223)
        ·
          refine ⟨3627868595470195752936335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2418579063646797168624223 3627868595470195752936335)
          ·
            refine ⟨5441802893205293629404503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3627868595470195752936335 5441802893205293629404503)
            ·
              refine ⟨8162704339807940444106755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5441802893205293629404503 8162704339807940444106755)
              ·
                refine ⟨12244056509711910666160133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8162704339807940444106755 12244056509711910666160133)
                ·
                  refine ⟨2295760595570983249905025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12244056509711910666160133 2295760595570983249905025)
                  ·
                    refine ⟨1721820446678237437428769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2295760595570983249905025 1721820446678237437428769)
                    ·
                      refine ⟨1291365335008678078071577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1721820446678237437428769 1291365335008678078071577)
                      ·
                        rfl

theorem cell23_2514925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_2514925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2514925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2514925 prefixEnd_2514925 := by exact prefixLift 2514925
  have htrace : WordTrace (prefixWord ++ tailWord_2514925) baseStart_2514925 baseEnd_2514925 := by
    simpa [prefixWord, tailWord_2514925, baseEnd_2514925] using wordTrace_append hprefix tailTrace_2514925
  have hstable : (prefixWord ++ tailWord_2514925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2514925).length < 2 ^ (prefixWord ++ tailWord_2514925).sum := by decide
  have hdescent : baseEnd_2514925 < baseStart_2514925 := by decide
  rcases family_descends (prefixWord ++ tailWord_2514925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2514927 : List Nat := [1, 1, 2, 1, 4, 2, 2, 1, 4, 5]
def baseStart_2514927 : Nat := 118140960795 + 2514927 * 2 ^ 59
def prefixEnd_2514927 : Nat := 4983230072969 + 3 ^ 40 * 2514927 * 2
def baseEnd_2514927 : Nat := 430455453989995690082189

theorem tailTrace_2514927 : CollatzResearch.WordTrace tailWord_2514927 prefixEnd_2514927 430455453989995690082189 := by
  unfold tailWord_2514927
  simp only [CollatzResearch.WordTrace]
  refine ⟨91726923359856469181247035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61151282239904312787498023 91726923359856469181247035)
  ·
    refine ⟨137590385039784703771870553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91726923359856469181247035 137590385039784703771870553)
    ·
      refine ⟨103192788779838527828902915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137590385039784703771870553 103192788779838527828902915)
      ·
        refine ⟨154789183169757791743354373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103192788779838527828902915 154789183169757791743354373)
        ·
          refine ⟨29022971844329585951878945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 154789183169757791743354373 29022971844329585951878945)
          ·
            refine ⟨21767228883247189463909209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29022971844329585951878945 21767228883247189463909209)
            ·
              refine ⟨16325421662435392097931907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21767228883247189463909209 16325421662435392097931907)
              ·
                refine ⟨24488132493653088146897861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16325421662435392097931907 24488132493653088146897861)
                ·
                  refine ⟨4591524842559954027543349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24488132493653088146897861 4591524842559954027543349)
                  ·
                    refine ⟨430455453989995690082189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4591524842559954027543349 430455453989995690082189)
                    ·
                      rfl

theorem cell23_2514927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 1, 4, 5].length) (baseStart_2514927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2514927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2514927 prefixEnd_2514927 := by exact prefixLift 2514927
  have htrace : WordTrace (prefixWord ++ tailWord_2514927) baseStart_2514927 baseEnd_2514927 := by
    simpa [prefixWord, tailWord_2514927, baseEnd_2514927] using wordTrace_append hprefix tailTrace_2514927
  have hstable : (prefixWord ++ tailWord_2514927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2514927).length < 2 ^ (prefixWord ++ tailWord_2514927).sum := by decide
  have hdescent : baseEnd_2514927 < baseStart_2514927 := by decide
  rcases family_descends (prefixWord ++ tailWord_2514927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2514942 : List Nat := [4, 2, 2, 2, 1, 2, 3, 1, 2, 2, 2]
def baseStart_2514942 : Nat := 118140960795 + 2514942 * 2 ^ 59
def prefixEnd_2514942 : Nat := 4983230072969 + 3 ^ 40 * 2514942 * 2
def baseEnd_2514942 : Nat := 1291374064179804511558999

theorem tailTrace_2514942 : CollatzResearch.WordTrace tailWord_2514942 prefixEnd_2514942 1291374064179804511558999 := by
  unfold tailWord_2514942
  simp only [CollatzResearch.WordTrace]
  refine ⟨11465933806850265842880385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61151646969868084495362053 11465933806850265842880385)
  ·
    refine ⟨8599450355137699382160289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11465933806850265842880385 8599450355137699382160289)
    ·
      refine ⟨6449587766353274536620217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8599450355137699382160289 6449587766353274536620217)
      ·
        refine ⟨4837190824764955902465163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6449587766353274536620217 4837190824764955902465163)
        ·
          refine ⟨7255786237147433853697745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4837190824764955902465163 7255786237147433853697745)
          ·
            refine ⟨5441839677860575390273309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7255786237147433853697745 5441839677860575390273309)
            ·
              refine ⟨2040689879197715771352491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5441839677860575390273309 2040689879197715771352491)
              ·
                refine ⟨3061034818796573657028737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2040689879197715771352491 3061034818796573657028737)
                ·
                  refine ⟨2295776114097430242771553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3061034818796573657028737 2295776114097430242771553)
                  ·
                    refine ⟨1721832085573072682078665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2295776114097430242771553 1721832085573072682078665)
                    ·
                      refine ⟨1291374064179804511558999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1721832085573072682078665 1291374064179804511558999)
                      ·
                        rfl

theorem cell23_2514942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 3, 1, 2, 2, 2].length) (baseStart_2514942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2514942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2514942 prefixEnd_2514942 := by exact prefixLift 2514942
  have htrace : WordTrace (prefixWord ++ tailWord_2514942) baseStart_2514942 baseEnd_2514942 := by
    simpa [prefixWord, tailWord_2514942, baseEnd_2514942] using wordTrace_append hprefix tailTrace_2514942
  have hstable : (prefixWord ++ tailWord_2514942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2514942).length < 2 ^ (prefixWord ++ tailWord_2514942).sum := by decide
  have hdescent : baseEnd_2514942 < baseStart_2514942 := by decide
  rcases family_descends (prefixWord ++ tailWord_2514942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2515004 : List Nat := [2, 2, 2, 2, 2, 1, 3, 3, 6]
def baseStart_2515004 : Nat := 118140960795 + 2515004 * 2 ^ 59
def prefixEnd_2515004 : Nat := 4983230072969 + 3 ^ 40 * 2515004 * 2
def baseEnd_2515004 : Nat := 143489544442264807664857

theorem tailTrace_2515004 : CollatzResearch.WordTrace tailWord_2515004 prefixEnd_2515004 143489544442264807664857 := by
  unfold tailWord_2515004
  simp only [CollatzResearch.WordTrace]
  refine ⟨45864865890288755665900033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61153154520385007554533377 45864865890288755665900033)
  ·
    refine ⟨34398649417716566749425025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45864865890288755665900033 34398649417716566749425025)
    ·
      refine ⟨25798987063287425062068769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34398649417716566749425025 25798987063287425062068769)
      ·
        refine ⟨19349240297465568796551577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25798987063287425062068769 19349240297465568796551577)
        ·
          refine ⟨14511930223099176597413683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19349240297465568796551577 14511930223099176597413683)
          ·
            refine ⟨21767895334648764896120525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14511930223099176597413683 21767895334648764896120525)
            ·
              refine ⟨8162960750493286836045197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21767895334648764896120525 8162960750493286836045197)
              ·
                refine ⟨3061110281434982563516949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8162960750493286836045197 3061110281434982563516949)
                ·
                  refine ⟨143489544442264807664857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3061110281434982563516949 143489544442264807664857)
                  ·
                    rfl

theorem cell23_2515004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 3, 6].length) (baseStart_2515004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2515004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2515004 prefixEnd_2515004 := by exact prefixLift 2515004
  have htrace : WordTrace (prefixWord ++ tailWord_2515004) baseStart_2515004 baseEnd_2515004 := by
    simpa [prefixWord, tailWord_2515004, baseEnd_2515004] using wordTrace_append hprefix tailTrace_2515004
  have hstable : (prefixWord ++ tailWord_2515004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2515004).length < 2 ^ (prefixWord ++ tailWord_2515004).sum := by decide
  have hdescent : baseEnd_2515004 < baseStart_2515004 := by decide
  rcases family_descends (prefixWord ++ tailWord_2515004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2515007 : List Nat := [1, 1, 2, 2, 3, 1, 2, 2, 1, 2, 6]
def baseStart_2515007 : Nat := 118140960795 + 2515007 * 2 ^ 59
def prefixEnd_2515007 : Nat := 4983230072969 + 3 ^ 40 * 2515007 * 2
def baseEnd_2515007 : Nat := 1291407440422346757246199

theorem tailTrace_2515007 : CollatzResearch.WordTrace tailWord_2515007 prefixEnd_2515007 1291407440422346757246199 := by
  unfold tailWord_2515007
  simp only [CollatzResearch.WordTrace]
  refine ⟨91729841199566642844159275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61153227466377761896106183 91729841199566642844159275)
  ·
    refine ⟨137594761799349964266238913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91729841199566642844159275 137594761799349964266238913)
    ·
      refine ⟨103196071349512473199679185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137594761799349964266238913 103196071349512473199679185)
      ·
        refine ⟨77397053512134354899759389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103196071349512473199679185 77397053512134354899759389)
        ·
          refine ⟨29023895067050383087409771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77397053512134354899759389 29023895067050383087409771)
          ·
            refine ⟨43535842600575574631114657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29023895067050383087409771 43535842600575574631114657)
            ·
              refine ⟨32651881950431680973335993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43535842600575574631114657 32651881950431680973335993)
              ·
                refine ⟨24488911462823760730001995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32651881950431680973335993 24488911462823760730001995)
                ·
                  refine ⟨36733367194235641095002993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24488911462823760730001995 36733367194235641095002993)
                  ·
                    refine ⟨27550025395676730821252245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36733367194235641095002993 27550025395676730821252245)
                    ·
                      refine ⟨1291407440422346757246199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27550025395676730821252245 1291407440422346757246199)
                      ·
                        rfl

theorem cell23_2515007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 2, 1, 2, 6].length) (baseStart_2515007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2515007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2515007 prefixEnd_2515007 := by exact prefixLift 2515007
  have htrace : WordTrace (prefixWord ++ tailWord_2515007) baseStart_2515007 baseEnd_2515007 := by
    simpa [prefixWord, tailWord_2515007, baseEnd_2515007] using wordTrace_append hprefix tailTrace_2515007
  have hstable : (prefixWord ++ tailWord_2515007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2515007).length < 2 ^ (prefixWord ++ tailWord_2515007).sum := by decide
  have hdescent : baseEnd_2515007 < baseStart_2515007 := by decide
  rcases family_descends (prefixWord ++ tailWord_2515007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2515064 : List Nat := [2, 1, 2, 1, 1, 1, 3, 2, 6, 4]
def baseStart_2515064 : Nat := 118140960795 + 2515064 * 2 ^ 59
def prefixEnd_2515064 : Nat := 4983230072969 + 3 ^ 40 * 2515064 * 2
def baseEnd_2515064 : Nat := 430478902939884344744479

theorem tailTrace_2515064 : CollatzResearch.WordTrace tailWord_2515064 prefixEnd_2515064 430478902939884344744479 := by
  unfold tailWord_2515064
  simp only [CollatzResearch.WordTrace]
  refine ⟨45865960080180070789492123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61154613440240094385989497 45865960080180070789492123)
  ·
    refine ⟨68798940120270106184238185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45865960080180070789492123 68798940120270106184238185)
    ·
      refine ⟨51599205090202579638178639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68798940120270106184238185 51599205090202579638178639)
      ·
        refine ⟨77398807635303869457267959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51599205090202579638178639 77398807635303869457267959)
        ·
          refine ⟨116098211452955804185901939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77398807635303869457267959 116098211452955804185901939)
          ·
            refine ⟨174147317179433706278852909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116098211452955804185901939 174147317179433706278852909)
            ·
              refine ⟨65305243942287639854569841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 174147317179433706278852909 65305243942287639854569841)
              ·
                refine ⟨48978932956715729890927381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65305243942287639854569841 48978932956715729890927381)
                ·
                  refine ⟨2295887482346049838637221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 48978932956715729890927381 2295887482346049838637221)
                  ·
                    refine ⟨430478902939884344744479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2295887482346049838637221 430478902939884344744479)
                    ·
                      rfl

theorem cell23_2515064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 6, 4].length) (baseStart_2515064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2515064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2515064 prefixEnd_2515064 := by exact prefixLift 2515064
  have htrace : WordTrace (prefixWord ++ tailWord_2515064) baseStart_2515064 baseEnd_2515064 := by
    simpa [prefixWord, tailWord_2515064, baseEnd_2515064] using wordTrace_append hprefix tailTrace_2515064
  have hstable : (prefixWord ++ tailWord_2515064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2515064).length < 2 ^ (prefixWord ++ tailWord_2515064).sum := by decide
  have hdescent : baseEnd_2515064 < baseStart_2515064 := by decide
  rcases family_descends (prefixWord ++ tailWord_2515064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2515098 : List Nat := [3, 1, 1, 5, 2, 1, 1, 1, 4, 4]
def baseStart_2515098 : Nat := 118140960795 + 2515098 * 2 ^ 59
def prefixEnd_2515098 : Nat := 4983230072969 + 3 ^ 40 * 2515098 * 2
def baseEnd_2515098 : Nat := 430484722387301967069427

theorem tailTrace_2515098 : CollatzResearch.WordTrace tailWord_2515098 prefixEnd_2515098 430484722387301967069427 := by
  unfold tailWord_2515098
  simp only [CollatzResearch.WordTrace]
  refine ⟨22933290060559241346430487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61155440161491310257147965 22933290060559241346430487)
  ·
    refine ⟨34399935090838862019645731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22933290060559241346430487 34399935090838862019645731)
    ·
      refine ⟨51599902636258293029468597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34399935090838862019645731 51599902636258293029468597)
      ·
        refine ⟨4837490872149214971512681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 51599902636258293029468597 4837490872149214971512681)
        ·
          refine ⟨3628118154111911228634511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4837490872149214971512681 3628118154111911228634511)
          ·
            refine ⟨5442177231167866842951767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3628118154111911228634511 5442177231167866842951767)
            ·
              refine ⟨8163265846751800264427651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5442177231167866842951767 8163265846751800264427651)
              ·
                refine ⟨12244898770127700396641477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8163265846751800264427651 12244898770127700396641477)
                ·
                  refine ⟨2295918519398943824370277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12244898770127700396641477 2295918519398943824370277)
                  ·
                    refine ⟨430484722387301967069427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2295918519398943824370277 430484722387301967069427)
                    ·
                      rfl

theorem cell23_2515098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 1, 4, 4].length) (baseStart_2515098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2515098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2515098 prefixEnd_2515098 := by exact prefixLift 2515098
  have htrace : WordTrace (prefixWord ++ tailWord_2515098) baseStart_2515098 baseEnd_2515098 := by
    simpa [prefixWord, tailWord_2515098, baseEnd_2515098] using wordTrace_append hprefix tailTrace_2515098
  have hstable : (prefixWord ++ tailWord_2515098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2515098).length < 2 ^ (prefixWord ++ tailWord_2515098).sum := by decide
  have hdescent : baseEnd_2515098 < baseStart_2515098 := by decide
  rcases family_descends (prefixWord ++ tailWord_2515098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2515105 : List Nat := [1, 2, 3, 3, 1, 3, 2, 1, 3, 2, 2]
def baseStart_2515105 : Nat := 118140960795 + 2515105 * 2 ^ 59
def prefixEnd_2515105 : Nat := 4983230072969 + 3 ^ 40 * 2515105 * 2
def baseEnd_2515105 : Nat := 1291457761526487373820749

theorem tailTrace_2515105 : CollatzResearch.WordTrace tailWord_2515105 prefixEnd_2515105 1291457761526487373820749 := by
  unfold tailWord_2515105
  simp only [CollatzResearch.WordTrace]
  refine ⟨91733415553211605581226769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61155610368807737054151179 91733415553211605581226769)
  ·
    refine ⟨68800061664908704185920077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91733415553211605581226769 68800061664908704185920077)
    ·
      refine ⟨25800023124340764069720029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68800061664908704185920077 25800023124340764069720029)
      ·
        refine ⟨9675008671627786526145011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25800023124340764069720029 9675008671627786526145011)
        ·
          refine ⟨14512513007441679789217517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9675008671627786526145011 14512513007441679789217517)
          ·
            refine ⟨5442192377790629920956569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14512513007441679789217517 5442192377790629920956569)
            ·
              refine ⟨4081644283342972440717427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5442192377790629920956569 4081644283342972440717427)
              ·
                refine ⟨6122466425014458661076141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4081644283342972440717427 6122466425014458661076141)
                ·
                  refine ⟨2295924909380421997903553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6122466425014458661076141 2295924909380421997903553)
                  ·
                    refine ⟨1721943682035316498427665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2295924909380421997903553 1721943682035316498427665)
                    ·
                      refine ⟨1291457761526487373820749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1721943682035316498427665 1291457761526487373820749)
                      ·
                        rfl

theorem cell23_2515105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 2, 1, 3, 2, 2].length) (baseStart_2515105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2515105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2515105 prefixEnd_2515105 := by exact prefixLift 2515105
  have htrace : WordTrace (prefixWord ++ tailWord_2515105) baseStart_2515105 baseEnd_2515105 := by
    simpa [prefixWord, tailWord_2515105, baseEnd_2515105] using wordTrace_append hprefix tailTrace_2515105
  have hstable : (prefixWord ++ tailWord_2515105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2515105).length < 2 ^ (prefixWord ++ tailWord_2515105).sum := by decide
  have hdescent : baseEnd_2515105 < baseStart_2515105 := by decide
  rcases family_descends (prefixWord ++ tailWord_2515105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2515144 : List Nat := [2, 1, 3, 1, 2, 1, 1, 2, 1, 5, 4]
def baseStart_2515144 : Nat := 118140960795 + 2515144 * 2 ^ 59
def prefixEnd_2515144 : Nat := 4983230072969 + 3 ^ 40 * 2515144 * 2
def baseEnd_2515144 : Nat := 1291477787272012721233069

theorem tailTrace_2515144 : CollatzResearch.WordTrace tailWord_2515144 prefixEnd_2515144 1291477787272012721233069 := by
  unfold tailWord_2515144
  simp only [CollatzResearch.WordTrace]
  refine ⟨45867419000035157620948243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61156558666713543494597657 45867419000035157620948243)
  ·
    refine ⟨68801128500052736431422365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45867419000035157620948243 68801128500052736431422365)
    ·
      refine ⟨25800423187519776161783387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68801128500052736431422365 25800423187519776161783387)
      ·
        refine ⟨38700634781279664242675081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25800423187519776161783387 38700634781279664242675081)
        ·
          refine ⟨29025476085959748182006311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38700634781279664242675081 29025476085959748182006311)
          ·
            refine ⟨43538214128939622273009467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29025476085959748182006311 43538214128939622273009467)
            ·
              refine ⟨65307321193409433409514201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43538214128939622273009467 65307321193409433409514201)
              ·
                refine ⟨48980490895057075057135651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65307321193409433409514201 48980490895057075057135651)
                ·
                  refine ⟨73470736342585612585703477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48980490895057075057135651 73470736342585612585703477)
                  ·
                    refine ⟨6887881532117401179909701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 73470736342585612585703477 6887881532117401179909701)
                    ·
                      refine ⟨1291477787272012721233069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6887881532117401179909701 1291477787272012721233069)
                      ·
                        rfl

theorem cell23_2515144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 2, 1, 5, 4].length) (baseStart_2515144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2515144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2515144 prefixEnd_2515144 := by exact prefixLift 2515144
  have htrace : WordTrace (prefixWord ++ tailWord_2515144) baseStart_2515144 baseEnd_2515144 := by
    simpa [prefixWord, tailWord_2515144, baseEnd_2515144] using wordTrace_append hprefix tailTrace_2515144
  have hstable : (prefixWord ++ tailWord_2515144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2515144).length < 2 ^ (prefixWord ++ tailWord_2515144).sum := by decide
  have hdescent : baseEnd_2515144 < baseStart_2515144 := by decide
  rcases family_descends (prefixWord ++ tailWord_2515144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2515178 : List Nat := [3, 1, 3, 1, 1, 2, 2, 3, 1, 4, 2]
def baseStart_2515178 : Nat := 118140960795 + 2515178 * 2 ^ 59
def prefixEnd_2515178 : Nat := 4983230072969 + 3 ^ 40 * 2515178 * 2
def baseEnd_2515178 : Nat := 1291495245614265588207913

theorem tailTrace_2515178 : CollatzResearch.WordTrace tailWord_2515178 prefixEnd_2515178 1291495245614265588207913 := by
  unfold tailWord_2515178
  simp only [CollatzResearch.WordTrace]
  refine ⟨22934019520486784762158547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61157385387964759365756125 22934019520486784762158547)
  ·
    refine ⟨34401029280730177143237821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22934019520486784762158547 34401029280730177143237821)
    ·
      refine ⟨12900385980273816428714183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34401029280730177143237821 12900385980273816428714183)
      ·
        refine ⟨19350578970410724643071275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12900385980273816428714183 19350578970410724643071275)
        ·
          refine ⟨29025868455616086964606913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19350578970410724643071275 29025868455616086964606913)
          ·
            refine ⟨21769401341712065223455185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29025868455616086964606913 21769401341712065223455185)
            ·
              refine ⟨16327051006284048917591389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21769401341712065223455185 16327051006284048917591389)
              ·
                refine ⟨6122644127356518344096771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16327051006284048917591389 6122644127356518344096771)
                ·
                  refine ⟨9183966191034777516145157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6122644127356518344096771 9183966191034777516145157)
                  ·
                    refine ⟨1721993660819020784277217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9183966191034777516145157 1721993660819020784277217)
                    ·
                      refine ⟨1291495245614265588207913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1721993660819020784277217 1291495245614265588207913)
                      ·
                        rfl

theorem cell23_2515178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 3, 1, 4, 2].length) (baseStart_2515178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2515178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2515178 prefixEnd_2515178 := by exact prefixLift 2515178
  have htrace : WordTrace (prefixWord ++ tailWord_2515178) baseStart_2515178 baseEnd_2515178 := by
    simpa [prefixWord, tailWord_2515178, baseEnd_2515178] using wordTrace_append hprefix tailTrace_2515178
  have hstable : (prefixWord ++ tailWord_2515178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2515178).length < 2 ^ (prefixWord ++ tailWord_2515178).sum := by decide
  have hdescent : baseEnd_2515178 < baseStart_2515178 := by decide
  rcases family_descends (prefixWord ++ tailWord_2515178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2515184 : List Nat := [2, 1, 1, 1, 3, 1, 1, 6, 7]
def baseStart_2515184 : Nat := 118140960795 + 2515184 * 2 ^ 59
def prefixEnd_2515184 : Nat := 4983230072969 + 3 ^ 40 * 2515184 * 2
def baseEnd_2515184 : Nat := 143499814055354729414765

theorem tailTrace_2515184 : CollatzResearch.WordTrace tailWord_2515184 prefixEnd_2515184 143499814055354729414765 := by
  unfold tailWord_2515184
  simp only [CollatzResearch.WordTrace]
  refine ⟨45868148459962701036676303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61157531279950268048901737 45868148459962701036676303)
  ·
    refine ⟨68802222689944051555014455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45868148459962701036676303 68802222689944051555014455)
    ·
      refine ⟨103203334034916077332521683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68802222689944051555014455 103203334034916077332521683)
      ·
        refine ⟨154805001052374115998782525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103203334034916077332521683 154805001052374115998782525)
        ·
          refine ⟨58051875394640293499543447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 154805001052374115998782525 58051875394640293499543447)
          ·
            refine ⟨87077813091960440249315171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58051875394640293499543447 87077813091960440249315171)
            ·
              refine ⟨130616719637940660373972757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87077813091960440249315171 130616719637940660373972757)
              ·
                refine ⟨6122658733028468455029973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 130616719637940660373972757 6122658733028468455029973)
                ·
                  refine ⟨143499814055354729414765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6122658733028468455029973 143499814055354729414765)
                  ·
                    rfl

theorem cell23_2515184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 6, 7].length) (baseStart_2515184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2515184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2515184 prefixEnd_2515184 := by exact prefixLift 2515184
  have htrace : WordTrace (prefixWord ++ tailWord_2515184) baseStart_2515184 baseEnd_2515184 := by
    simpa [prefixWord, tailWord_2515184, baseEnd_2515184] using wordTrace_append hprefix tailTrace_2515184
  have hstable : (prefixWord ++ tailWord_2515184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2515184).length < 2 ^ (prefixWord ++ tailWord_2515184).sum := by decide
  have hdescent : baseEnd_2515184 < baseStart_2515184 := by decide
  rcases family_descends (prefixWord ++ tailWord_2515184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2515211 : List Nat := [1, 1, 1, 1, 5, 2, 2, 2, 2, 3, 3]
def baseStart_2515211 : Nat := 118140960795 + 2515211 * 2 ^ 59
def prefixEnd_2515211 : Nat := 4983230072969 + 3 ^ 40 * 2515211 * 2
def baseEnd_2515211 : Nat := 1291512190475863959095261

theorem tailTrace_2515211 : CollatzResearch.WordTrace tailWord_2515211 prefixEnd_2515211 1291512190475863959095261 := by
  unfold tailWord_2515211
  simp only [CollatzResearch.WordTrace]
  refine ⟨91737281690827585684585487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61158187793885057123056991 91737281690827585684585487)
  ·
    refine ⟨137605922536241378526878231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91737281690827585684585487 137605922536241378526878231)
    ·
      refine ⟨206408883804362067790317347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137605922536241378526878231 206408883804362067790317347)
      ·
        refine ⟨309613325706543101685476021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206408883804362067790317347 309613325706543101685476021)
        ·
          refine ⟨29026249284988415783013377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 309613325706543101685476021 29026249284988415783013377)
          ·
            refine ⟨21769686963741311837260033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29026249284988415783013377 21769686963741311837260033)
            ·
              refine ⟨16327265222805983877945025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21769686963741311837260033 16327265222805983877945025)
              ·
                refine ⟨12245448917104487908458769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16327265222805983877945025 12245448917104487908458769)
                ·
                  refine ⟨9184086687828365931344077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12245448917104487908458769 9184086687828365931344077)
                  ·
                    refine ⟨3444032507935637224254029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9184086687828365931344077 3444032507935637224254029)
                    ·
                      refine ⟨1291512190475863959095261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3444032507935637224254029 1291512190475863959095261)
                      ·
                        rfl

theorem cell23_2515211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 2, 2, 3, 3].length) (baseStart_2515211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2515211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2515211 prefixEnd_2515211 := by exact prefixLift 2515211
  have htrace : WordTrace (prefixWord ++ tailWord_2515211) baseStart_2515211 baseEnd_2515211 := by
    simpa [prefixWord, tailWord_2515211, baseEnd_2515211] using wordTrace_append hprefix tailTrace_2515211
  have hstable : (prefixWord ++ tailWord_2515211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2515211).length < 2 ^ (prefixWord ++ tailWord_2515211).sum := by decide
  have hdescent : baseEnd_2515211 < baseStart_2515211 := by decide
  rcases family_descends (prefixWord ++ tailWord_2515211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2515251 : List Nat := [1, 1, 1, 2, 5, 1, 3, 1, 1, 3, 4]
def baseStart_2515251 : Nat := 118140960795 + 2515251 * 2 ^ 59
def prefixEnd_2515251 : Nat := 4983230072969 + 3 ^ 40 * 2515251 * 2
def baseEnd_2515251 : Nat := 1291532729702043802595077

theorem tailTrace_2515251 : CollatzResearch.WordTrace tailWord_2515251 prefixEnd_2515251 1291532729702043802595077 := by
  unfold tailWord_2515251
  simp only [CollatzResearch.WordTrace]
  refine ⟨91738740610682672516041607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61159160407121781677361071 91738740610682672516041607)
  ·
    refine ⟨137608110916024008774062411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91738740610682672516041607 137608110916024008774062411)
    ·
      refine ⟨206412166374036013161093617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137608110916024008774062411 206412166374036013161093617)
      ·
        refine ⟨154809124780527009870820213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 206412166374036013161093617 154809124780527009870820213)
        ·
          refine ⟨14513355448174407175389395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 154809124780527009870820213 14513355448174407175389395)
          ·
            refine ⟨21770033172261610763084093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14513355448174407175389395 21770033172261610763084093)
            ·
              refine ⟨8163762439598104036156535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21770033172261610763084093 8163762439598104036156535)
              ·
                refine ⟨12245643659397156054234803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8163762439598104036156535 12245643659397156054234803)
                ·
                  refine ⟨18368465489095734081352205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12245643659397156054234803 18368465489095734081352205)
                  ·
                    refine ⟨6888174558410900280507077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18368465489095734081352205 6888174558410900280507077)
                    ·
                      refine ⟨1291532729702043802595077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6888174558410900280507077 1291532729702043802595077)
                      ·
                        rfl

theorem cell23_2515251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 1, 1, 3, 4].length) (baseStart_2515251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2515251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2515251 prefixEnd_2515251 := by exact prefixLift 2515251
  have htrace : WordTrace (prefixWord ++ tailWord_2515251) baseStart_2515251 baseEnd_2515251 := by
    simpa [prefixWord, tailWord_2515251, baseEnd_2515251] using wordTrace_append hprefix tailTrace_2515251
  have hstable : (prefixWord ++ tailWord_2515251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2515251).length < 2 ^ (prefixWord ++ tailWord_2515251).sum := by decide
  have hdescent : baseEnd_2515251 < baseStart_2515251 := by decide
  rcases family_descends (prefixWord ++ tailWord_2515251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2515312 : List Nat := [2, 1, 1, 1, 4, 5, 1, 3, 1, 4]
def baseStart_2515312 : Nat := 118140960795 + 2515312 * 2 ^ 59
def prefixEnd_2515312 : Nat := 4983230072969 + 3 ^ 40 * 2515312 * 2
def baseEnd_2515312 : Nat := 430521350673989354644099

theorem tailTrace_2515312 : CollatzResearch.WordTrace tailWord_2515312 prefixEnd_2515312 430521350673989354644099 := by
  unfold tailWord_2515312
  simp only [CollatzResearch.WordTrace]
  refine ⟨45870482731730839967006095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61160643642307786622674793 45870482731730839967006095)
  ·
    refine ⟨68805724097596259950509143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45870482731730839967006095 68805724097596259950509143)
    ·
      refine ⟨103208586146394389925763715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68805724097596259950509143 103208586146394389925763715)
      ·
        refine ⟨154812879219591584888645573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103208586146394389925763715 154812879219591584888645573)
        ·
          refine ⟨29027414853673422166621045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 154812879219591584888645573 29027414853673422166621045)
          ·
            refine ⟨2721320142531883328120723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29027414853673422166621045 2721320142531883328120723)
            ·
              refine ⟨4081980213797824992181085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2721320142531883328120723 4081980213797824992181085)
              ·
                refine ⟨1530742580174184372067907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4081980213797824992181085 1530742580174184372067907)
                ·
                  refine ⟨2296113870261276558101861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1530742580174184372067907 2296113870261276558101861)
                  ·
                    refine ⟨430521350673989354644099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2296113870261276558101861 430521350673989354644099)
                    ·
                      rfl

theorem cell23_2515312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 1, 3, 1, 4].length) (baseStart_2515312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2515312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2515312 prefixEnd_2515312 := by exact prefixLift 2515312
  have htrace : WordTrace (prefixWord ++ tailWord_2515312) baseStart_2515312 baseEnd_2515312 := by
    simpa [prefixWord, tailWord_2515312, baseEnd_2515312] using wordTrace_append hprefix tailTrace_2515312
  have hstable : (prefixWord ++ tailWord_2515312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2515312).length < 2 ^ (prefixWord ++ tailWord_2515312).sum := by decide
  have hdescent : baseEnd_2515312 < baseStart_2515312 := by decide
  rcases family_descends (prefixWord ++ tailWord_2515312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2515321 : List Nat := [1, 2, 1, 3, 2, 1, 1, 2, 5, 5]
def baseStart_2515321 : Nat := 118140960795 + 2515321 * 2 ^ 59
def prefixEnd_2515321 : Nat := 4983230072969 + 3 ^ 40 * 2515321 * 2
def baseEnd_2515321 : Nat := 430522891115952842906585

theorem tailTrace_2515321 : CollatzResearch.WordTrace tailWord_2515321 prefixEnd_2515321 430522891115952842906585 := by
  unfold tailWord_2515321
  simp only [CollatzResearch.WordTrace]
  refine ⟨91741293720429074471089817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61160862480286049647393211 91741293720429074471089817)
  ·
    refine ⟨68805970290321805853317363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91741293720429074471089817 68805970290321805853317363)
    ·
      refine ⟨103208955435482708779976045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68805970290321805853317363 103208955435482708779976045)
      ·
        refine ⟨38703358288306015792491017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103208955435482708779976045 38703358288306015792491017)
        ·
          refine ⟨29027518716229511844368263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38703358288306015792491017 29027518716229511844368263)
          ·
            refine ⟨43541278074344267766552395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29027518716229511844368263 43541278074344267766552395)
            ·
              refine ⟨65311917111516401649828593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43541278074344267766552395 65311917111516401649828593)
              ·
                refine ⟨48983937833637301237371445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65311917111516401649828593 48983937833637301237371445)
                ·
                  refine ⟨4592244171903496991003573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 48983937833637301237371445 4592244171903496991003573)
                  ·
                    refine ⟨430522891115952842906585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4592244171903496991003573 430522891115952842906585)
                    ·
                      rfl

theorem cell23_2515321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 2, 5, 5].length) (baseStart_2515321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2515321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2515321 prefixEnd_2515321 := by exact prefixLift 2515321
  have htrace : WordTrace (prefixWord ++ tailWord_2515321) baseStart_2515321 baseEnd_2515321 := by
    simpa [prefixWord, tailWord_2515321, baseEnd_2515321] using wordTrace_append hprefix tailTrace_2515321
  have hstable : (prefixWord ++ tailWord_2515321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2515321).length < 2 ^ (prefixWord ++ tailWord_2515321).sum := by decide
  have hdescent : baseEnd_2515321 < baseStart_2515321 := by decide
  rcases family_descends (prefixWord ++ tailWord_2515321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2515329 : List Nat := [1, 2, 4, 3, 1, 2, 3, 2, 1, 4]
def baseStart_2515329 : Nat := 118140960795 + 2515329 * 2 ^ 59
def prefixEnd_2515329 : Nat := 4983230072969 + 3 ^ 40 * 2515329 * 2
def baseEnd_2515329 : Nat := 430524260397698165806573

theorem tailTrace_2515329 : CollatzResearch.WordTrace tailWord_2515329 prefixEnd_2515329 430524260397698165806573 := by
  unfold tailWord_2515329
  simp only [CollatzResearch.WordTrace]
  refine ⟨91741585504400091837381041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61161057002933394558254027 91741585504400091837381041)
  ·
    refine ⟨68806189128300068878035781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91741585504400091837381041 68806189128300068878035781)
    ·
      refine ⟨12901160461556262914631709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68806189128300068878035781 12901160461556262914631709)
      ·
        refine ⟨4837935173083598592986891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12901160461556262914631709 4837935173083598592986891)
        ·
          refine ⟨7256902759625397889480337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4837935173083598592986891 7256902759625397889480337)
          ·
            refine ⟨5442677069719048417110253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7256902759625397889480337 5442677069719048417110253)
            ·
              refine ⟨2041003901144643156416345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5442677069719048417110253 2041003901144643156416345)
              ·
                refine ⟨1530752925858482367312259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2041003901144643156416345 1530752925858482367312259)
                ·
                  refine ⟨2296129388787723550968389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1530752925858482367312259 2296129388787723550968389)
                  ·
                    refine ⟨430524260397698165806573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2296129388787723550968389 430524260397698165806573)
                    ·
                      rfl

theorem cell23_2515329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 3, 2, 1, 4].length) (baseStart_2515329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2515329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2515329 prefixEnd_2515329 := by exact prefixLift 2515329
  have htrace : WordTrace (prefixWord ++ tailWord_2515329) baseStart_2515329 baseEnd_2515329 := by
    simpa [prefixWord, tailWord_2515329, baseEnd_2515329] using wordTrace_append hprefix tailTrace_2515329
  have hstable : (prefixWord ++ tailWord_2515329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2515329).length < 2 ^ (prefixWord ++ tailWord_2515329).sum := by decide
  have hdescent : baseEnd_2515329 < baseStart_2515329 := by decide
  rcases family_descends (prefixWord ++ tailWord_2515329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2515342 : List Nat := [4, 1, 1, 4, 1, 3, 2, 1, 6]
def baseStart_2515342 : Nat := 118140960795 + 2515342 * 2 ^ 59
def prefixEnd_2515342 : Nat := 4983230072969 + 3 ^ 40 * 2515342 * 2
def baseEnd_2515342 : Nat := 143508828493511438506351

theorem tailTrace_2515342 : CollatzResearch.WordTrace tailWord_2515342 prefixEnd_2515342 143508828493511438506351 := by
  unfold tailWord_2515342
  simp only [CollatzResearch.WordTrace]
  refine ⟨11467757456669124382200535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61161373102235330038402853 11467757456669124382200535)
  ·
    refine ⟨17201636185003686573300803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11467757456669124382200535 17201636185003686573300803)
    ·
      refine ⟨25802454277505529859951205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17201636185003686573300803 25802454277505529859951205)
      ·
        refine ⟨4837960177032286848740851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25802454277505529859951205 4837960177032286848740851)
        ·
          refine ⟨7256940265548430273111277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4837960177032286848740851 7256940265548430273111277)
          ·
            refine ⟨2721352599580661352416729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7256940265548430273111277 2721352599580661352416729)
            ·
              refine ⟨2041014449685496014312547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2721352599580661352416729 2041014449685496014312547)
              ·
                refine ⟨3061521674528244021468821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2041014449685496014312547 3061521674528244021468821)
                ·
                  refine ⟨143508828493511438506351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3061521674528244021468821 143508828493511438506351)
                  ·
                    rfl

theorem cell23_2515342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 2, 1, 6].length) (baseStart_2515342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2515342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2515342 prefixEnd_2515342 := by exact prefixLift 2515342
  have htrace : WordTrace (prefixWord ++ tailWord_2515342) baseStart_2515342 baseEnd_2515342 := by
    simpa [prefixWord, tailWord_2515342, baseEnd_2515342] using wordTrace_append hprefix tailTrace_2515342
  have hstable : (prefixWord ++ tailWord_2515342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2515342).length < 2 ^ (prefixWord ++ tailWord_2515342).sum := by decide
  have hdescent : baseEnd_2515342 < baseStart_2515342 := by decide
  rcases family_descends (prefixWord ++ tailWord_2515342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2515362 : List Nat := [3, 3, 1, 2, 1, 1, 4, 1, 2, 3, 2]
def baseStart_2515362 : Nat := 118140960795 + 2515362 * 2 ^ 59
def prefixEnd_2515362 : Nat := 4983230072969 + 3 ^ 40 * 2515362 * 2
def baseEnd_2515362 : Nat := 1291589726054692868307067

theorem tailTrace_2515362 : CollatzResearch.WordTrace tailWord_2515362 prefixEnd_2515362 1291589726054692868307067 := by
  unfold tailWord_2515362
  simp only [CollatzResearch.WordTrace]
  refine ⟨22935697278320134618333085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61161859408853692315554893 22935697278320134618333085)
  ·
    refine ⟨8600886479370050481874907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22935697278320134618333085 8600886479370050481874907)
    ·
      refine ⟨12901329719055075722812361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8600886479370050481874907 12901329719055075722812361)
      ·
        refine ⟨9675997289291306792109271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12901329719055075722812361 9675997289291306792109271)
        ·
          refine ⟨14513995933936960188163907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9675997289291306792109271 14513995933936960188163907)
          ·
            refine ⟨21770993900905440282245861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14513995933936960188163907 21770993900905440282245861)
            ·
              refine ⟨4082061356419770052921099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21770993900905440282245861 4082061356419770052921099)
              ·
                refine ⟨6123092034629655079381649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4082061356419770052921099 6123092034629655079381649)
                ·
                  refine ⟨4592319025972241309536237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6123092034629655079381649 4592319025972241309536237)
                  ·
                    refine ⟨1722119634739590491076089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4592319025972241309536237 1722119634739590491076089)
                    ·
                      refine ⟨1291589726054692868307067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1722119634739590491076089 1291589726054692868307067)
                      ·
                        rfl

theorem cell23_2515362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 4, 1, 2, 3, 2].length) (baseStart_2515362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2515362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2515362 prefixEnd_2515362 := by exact prefixLift 2515362
  have htrace : WordTrace (prefixWord ++ tailWord_2515362) baseStart_2515362 baseEnd_2515362 := by
    simpa [prefixWord, tailWord_2515362, baseEnd_2515362] using wordTrace_append hprefix tailTrace_2515362
  have hstable : (prefixWord ++ tailWord_2515362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2515362).length < 2 ^ (prefixWord ++ tailWord_2515362).sum := by decide
  have hdescent : baseEnd_2515362 < baseStart_2515362 := by decide
  rcases family_descends (prefixWord ++ tailWord_2515362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2515380 : List Nat := [2, 5, 2, 2, 2, 1, 2, 2, 1, 4]
def baseStart_2515380 : Nat := 118140960795 + 2515380 * 2 ^ 59
def prefixEnd_2515380 : Nat := 4983230072969 + 3 ^ 40 * 2515380 * 2
def baseEnd_2515380 : Nat := 430532989568824599293995

theorem tailTrace_2515380 : CollatzResearch.WordTrace tailWord_2515380 prefixEnd_2515380 430532989568824599293995 := by
  unfold tailWord_2515380
  simp only [CollatzResearch.WordTrace]
  refine ⟨45871722813607663773743797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61162297084810218364991729 45871722813607663773743797)
  ·
    refine ⟨4300474013775718478788481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 45871722813607663773743797 4300474013775718478788481)
    ·
      refine ⟨3225355510331788859091361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4300474013775718478788481 3225355510331788859091361)
      ·
        refine ⟨2419016632748841644318521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3225355510331788859091361 2419016632748841644318521)
        ·
          refine ⟨1814262474561631233238891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2419016632748841644318521 1814262474561631233238891)
          ·
            refine ⟨2721393711842446849858337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1814262474561631233238891 2721393711842446849858337)
            ·
              refine ⟨2041045283881835137393753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2721393711842446849858337 2041045283881835137393753)
              ·
                refine ⟨1530783962911376353045315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2041045283881835137393753 1530783962911376353045315)
                ·
                  refine ⟨2296175944367064529567973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1530783962911376353045315 2296175944367064529567973)
                  ·
                    refine ⟨430532989568824599293995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2296175944367064529567973 430532989568824599293995)
                    ·
                      rfl

theorem cell23_2515380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_2515380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2515380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2515380 prefixEnd_2515380 := by exact prefixLift 2515380
  have htrace : WordTrace (prefixWord ++ tailWord_2515380) baseStart_2515380 baseEnd_2515380 := by
    simpa [prefixWord, tailWord_2515380, baseEnd_2515380] using wordTrace_append hprefix tailTrace_2515380
  have hstable : (prefixWord ++ tailWord_2515380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2515380).length < 2 ^ (prefixWord ++ tailWord_2515380).sum := by decide
  have hdescent : baseEnd_2515380 < baseStart_2515380 := by decide
  rcases family_descends (prefixWord ++ tailWord_2515380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2515381 : List Nat := [1, 3, 3, 2, 14]
def baseStart_2515381 : Nat := 118140960795 + 2515381 * 2 ^ 59
def prefixEnd_2515381 : Nat := 4983230072969 + 3 ^ 40 * 2515381 * 2
def baseEnd_2515381 : Nat := 1771741402177130718751

theorem tailTrace_2515381 : CollatzResearch.WordTrace tailWord_2515381 prefixEnd_2515381 1771741402177130718751 := by
  unfold tailWord_2515381
  simp only [CollatzResearch.WordTrace]
  refine ⟨91743482100211704718273997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61162321400141136478849331 91743482100211704718273997)
  ·
    refine ⟨34403805787579389269352749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91743482100211704718273997 34403805787579389269352749)
    ·
      refine ⟨12901427170342270976007281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34403805787579389269352749 12901427170342270976007281)
      ·
        refine ⟨9676070377756703232005461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12901427170342270976007281 9676070377756703232005461)
        ·
          refine ⟨1771741402177130718751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 9676070377756703232005461 1771741402177130718751)
          ·
            rfl

theorem cell23_2515381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 14].length) (baseStart_2515381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2515381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2515381 prefixEnd_2515381 := by exact prefixLift 2515381
  have htrace : WordTrace (prefixWord ++ tailWord_2515381) baseStart_2515381 baseEnd_2515381 := by
    simpa [prefixWord, tailWord_2515381, baseEnd_2515381] using wordTrace_append hprefix tailTrace_2515381
  have hstable : (prefixWord ++ tailWord_2515381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2515381).length < 2 ^ (prefixWord ++ tailWord_2515381).sum := by decide
  have hdescent : baseEnd_2515381 < baseStart_2515381 := by decide
  rcases family_descends (prefixWord ++ tailWord_2515381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2515385 : List Nat := [1, 2, 1, 4, 3, 1, 1, 4, 2, 4]
def baseStart_2515385 : Nat := 118140960795 + 2515385 * 2 ^ 59
def prefixEnd_2515385 : Nat := 4983230072969 + 3 ^ 40 * 2515385 * 2
def baseEnd_2515385 : Nat := 430533845369915426106487

theorem tailTrace_2515385 : CollatzResearch.WordTrace tailWord_2515385 prefixEnd_2515385 430533845369915426106487 := by
  unfold tailWord_2515385
  simp only [CollatzResearch.WordTrace]
  refine ⟨91743627992197213401419609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61162418661464808934279739 91743627992197213401419609)
  ·
    refine ⟨68807720994147910051064707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91743627992197213401419609 68807720994147910051064707)
    ·
      refine ⟨103211581491221865076597061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68807720994147910051064707 103211581491221865076597061)
      ·
        refine ⟨19352171529604099701861949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 103211581491221865076597061 19352171529604099701861949)
        ·
          refine ⟨7257064323601537388198231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19352171529604099701861949 7257064323601537388198231)
          ·
            refine ⟨10885596485402306082297347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7257064323601537388198231 10885596485402306082297347)
            ·
              refine ⟨16328394728103459123446021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10885596485402306082297347 16328394728103459123446021)
              ·
                refine ⟨3061574011519398585646129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16328394728103459123446021 3061574011519398585646129)
                ·
                  refine ⟨2296180508639548939234597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3061574011519398585646129 2296180508639548939234597)
                  ·
                    refine ⟨430533845369915426106487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2296180508639548939234597 430533845369915426106487)
                    ·
                      rfl

theorem cell23_2515385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 4, 2, 4].length) (baseStart_2515385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2515385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2515385 prefixEnd_2515385 := by exact prefixLift 2515385
  have htrace : WordTrace (prefixWord ++ tailWord_2515385) baseStart_2515385 baseEnd_2515385 := by
    simpa [prefixWord, tailWord_2515385, baseEnd_2515385] using wordTrace_append hprefix tailTrace_2515385
  have hstable : (prefixWord ++ tailWord_2515385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2515385).length < 2 ^ (prefixWord ++ tailWord_2515385).sum := by decide
  have hdescent : baseEnd_2515385 < baseStart_2515385 := by decide
  rcases family_descends (prefixWord ++ tailWord_2515385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2515401 : List Nat := [1, 2, 1, 1, 2, 1, 4, 1, 2, 2, 6]
def baseStart_2515401 : Nat := 118140960795 + 2515401 * 2 ^ 59
def prefixEnd_2515401 : Nat := 4983230072969 + 3 ^ 40 * 2515401 * 2
def baseEnd_2515401 : Nat := 1291609751800218215719387

theorem tailTrace_2515401 : CollatzResearch.WordTrace tailWord_2515401 prefixEnd_2515401 1291609751800218215719387 := by
  unfold tailWord_2515401
  simp only [CollatzResearch.WordTrace]
  refine ⟨91744211560139248134002057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61162807706759498756001371 91744211560139248134002057)
  ·
    refine ⟨68808158670104436100501543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91744211560139248134002057 68808158670104436100501543)
    ·
      refine ⟨103212238005156654150752315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68808158670104436100501543 103212238005156654150752315)
      ·
        refine ⟨154818357007734981226128473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103212238005156654150752315 154818357007734981226128473)
        ·
          refine ⟨116113767755801235919596355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 154818357007734981226128473 116113767755801235919596355)
          ·
            refine ⟨174170651633701853879394533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116113767755801235919596355 174170651633701853879394533)
            ·
              refine ⟨32656997181319097602386475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 174170651633701853879394533 32656997181319097602386475)
              ·
                refine ⟨48985495771978646403579713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32656997181319097602386475 48985495771978646403579713)
                ·
                  refine ⟨36739121828983984802684785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48985495771978646403579713 36739121828983984802684785)
                  ·
                    refine ⟨27554341371737988602013589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36739121828983984802684785 27554341371737988602013589)
                    ·
                      refine ⟨1291609751800218215719387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27554341371737988602013589 1291609751800218215719387)
                      ·
                        rfl

theorem cell23_2515401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 1, 2, 2, 6].length) (baseStart_2515401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2515401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2515401 prefixEnd_2515401 := by exact prefixLift 2515401
  have htrace : WordTrace (prefixWord ++ tailWord_2515401) baseStart_2515401 baseEnd_2515401 := by
    simpa [prefixWord, tailWord_2515401, baseEnd_2515401] using wordTrace_append hprefix tailTrace_2515401
  have hstable : (prefixWord ++ tailWord_2515401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2515401).length < 2 ^ (prefixWord ++ tailWord_2515401).sum := by decide
  have hdescent : baseEnd_2515401 < baseStart_2515401 := by decide
  rcases family_descends (prefixWord ++ tailWord_2515401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2515425 : List Nat := [1, 2, 3, 1, 2, 2, 2, 2, 4, 1, 3]
def baseStart_2515425 : Nat := 118140960795 + 2515425 * 2 ^ 59
def prefixEnd_2515425 : Nat := 4983230072969 + 3 ^ 40 * 2515425 * 2
def baseEnd_2515425 : Nat := 1291622075335926121819277

theorem tailTrace_2515425 : CollatzResearch.WordTrace tailWord_2515425 prefixEnd_2515425 1291622075335926121819277 := by
  unfold tailWord_2515425
  simp only [CollatzResearch.WordTrace]
  refine ⟨91745086912052300232875729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61163391274701533488583819 91745086912052300232875729)
  ·
    refine ⟨68808815184039225174656797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91745086912052300232875729 68808815184039225174656797)
    ·
      refine ⟨25803305694014709440496299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68808815184039225174656797 25803305694014709440496299)
      ·
        refine ⟨38704958541022064160744449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25803305694014709440496299 38704958541022064160744449)
        ·
          refine ⟨29028718905766548120558337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38704958541022064160744449 29028718905766548120558337)
          ·
            refine ⟨21771539179324911090418753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29028718905766548120558337 21771539179324911090418753)
            ·
              refine ⟨16328654384493683317814065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21771539179324911090418753 16328654384493683317814065)
              ·
                refine ⟨12246490788370262488360549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16328654384493683317814065 12246490788370262488360549)
                ·
                  refine ⟨2296217022819424216567603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12246490788370262488360549 2296217022819424216567603)
                  ·
                    refine ⟨3444325534229136324851405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2296217022819424216567603 3444325534229136324851405)
                    ·
                      refine ⟨1291622075335926121819277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3444325534229136324851405 1291622075335926121819277)
                      ·
                        rfl

theorem cell23_2515425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 2, 4, 1, 3].length) (baseStart_2515425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2515425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2515425 prefixEnd_2515425 := by exact prefixLift 2515425
  have htrace : WordTrace (prefixWord ++ tailWord_2515425) baseStart_2515425 baseEnd_2515425 := by
    simpa [prefixWord, tailWord_2515425, baseEnd_2515425] using wordTrace_append hprefix tailTrace_2515425
  have hstable : (prefixWord ++ tailWord_2515425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2515425).length < 2 ^ (prefixWord ++ tailWord_2515425).sum := by decide
  have hdescent : baseEnd_2515425 < baseStart_2515425 := by decide
  rcases family_descends (prefixWord ++ tailWord_2515425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2515465 : List Nat := [1, 2, 1, 1, 3, 1, 2, 5, 1, 4, 2]
def baseStart_2515465 : Nat := 118140960795 + 2515465 * 2 ^ 59
def prefixEnd_2515465 : Nat := 4983230072969 + 3 ^ 40 * 2515465 * 2
def baseEnd_2515465 : Nat := 1291642614562105965319093

theorem tailTrace_2515465 : CollatzResearch.WordTrace tailWord_2515465 prefixEnd_2515465 1291642614562105965319093 := by
  unfold tailWord_2515465
  simp only [CollatzResearch.WordTrace]
  refine ⟨91746545831907387064331849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61164363887938258042887899 91746545831907387064331849)
  ·
    refine ⟨68809909373930540298248887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91746545831907387064331849 68809909373930540298248887)
    ·
      refine ⟨103214864060895810447373331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68809909373930540298248887 103214864060895810447373331)
      ·
        refine ⟨154822296091343715671059997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103214864060895810447373331 154822296091343715671059997)
        ·
          refine ⟨58058361034253893376647499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 154822296091343715671059997 58058361034253893376647499)
          ·
            refine ⟨87087541551380840064971249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58058361034253893376647499 87087541551380840064971249)
            ·
              refine ⟨65315656163535630048728437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87087541551380840064971249 65315656163535630048728437)
              ·
                refine ⟨6123342765331465317068291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 65315656163535630048728437 6123342765331465317068291)
                ·
                  refine ⟨9185014147997197975602437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6123342765331465317068291 9185014147997197975602437)
                  ·
                    refine ⟨1722190152749474620425457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9185014147997197975602437 1722190152749474620425457)
                    ·
                      refine ⟨1291642614562105965319093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1722190152749474620425457 1291642614562105965319093)
                      ·
                        rfl

theorem cell23_2515465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 5, 1, 4, 2].length) (baseStart_2515465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2515465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2515465 prefixEnd_2515465 := by exact prefixLift 2515465
  have htrace : WordTrace (prefixWord ++ tailWord_2515465) baseStart_2515465 baseEnd_2515465 := by
    simpa [prefixWord, tailWord_2515465, baseEnd_2515465] using wordTrace_append hprefix tailTrace_2515465
  have hstable : (prefixWord ++ tailWord_2515465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2515465).length < 2 ^ (prefixWord ++ tailWord_2515465).sum := by decide
  have hdescent : baseEnd_2515465 < baseStart_2515465 := by decide
  rcases family_descends (prefixWord ++ tailWord_2515465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2515482 : List Nat := [3, 1, 1, 3, 1, 1, 3, 2, 4, 2, 2]
def baseStart_2515482 : Nat := 118140960795 + 2515482 * 2 ^ 59
def prefixEnd_2515482 : Nat := 4983230072969 + 3 ^ 40 * 2515482 * 2
def baseEnd_2515482 : Nat := 1291651343733232398806515

theorem tailTrace_2515482 : CollatzResearch.WordTrace tailWord_2515482 prefixEnd_2515482 1291651343733232398806515 := by
  unfold tailWord_2515482
  simp only [CollatzResearch.WordTrace]
  refine ⟨22936791468211449741925175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61164777248563865978467133 22936791468211449741925175)
  ·
    refine ⟨34405187202317174612887763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22936791468211449741925175 34405187202317174612887763)
    ·
      refine ⟨51607780803475761919331645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34405187202317174612887763 51607780803475761919331645)
      ·
        refine ⟨19352917801303410719749367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51607780803475761919331645 19352917801303410719749367)
        ·
          refine ⟨29029376701955116079624051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19352917801303410719749367 29029376701955116079624051)
          ·
            refine ⟨43544065052932674119436077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29029376701955116079624051 43544065052932674119436077)
            ·
              refine ⟨16329024394849752794788529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43544065052932674119436077 16329024394849752794788529)
              ·
                refine ⟨12246768296137314596091397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16329024394849752794788529 12246768296137314596091397)
                ·
                  refine ⟨2296269055525746486767137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12246768296137314596091397 2296269055525746486767137)
                  ·
                    refine ⟨1722201791644309865075353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2296269055525746486767137 1722201791644309865075353)
                    ·
                      refine ⟨1291651343733232398806515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1722201791644309865075353 1291651343733232398806515)
                      ·
                        rfl

theorem cell23_2515482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 2, 4, 2, 2].length) (baseStart_2515482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2515482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2515482 prefixEnd_2515482 := by exact prefixLift 2515482
  have htrace : WordTrace (prefixWord ++ tailWord_2515482) baseStart_2515482 baseEnd_2515482 := by
    simpa [prefixWord, tailWord_2515482, baseEnd_2515482] using wordTrace_append hprefix tailTrace_2515482
  have hstable : (prefixWord ++ tailWord_2515482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2515482).length < 2 ^ (prefixWord ++ tailWord_2515482).sum := by decide
  have hdescent : baseEnd_2515482 < baseStart_2515482 := by decide
  rcases family_descends (prefixWord ++ tailWord_2515482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2515485 : List Nat := [1, 4, 2, 2, 1, 3, 1, 1, 2, 1, 5]
def baseStart_2515485 : Nat := 118140960795 + 2515485 * 2 ^ 59
def prefixEnd_2515485 : Nat := 4983230072969 + 3 ^ 40 * 2515485 * 2
def baseEnd_2515485 : Nat := 1291652884175195887069001

theorem tailTrace_2515485 : CollatzResearch.WordTrace tailWord_2515485 prefixEnd_2515485 1291652884175195887069001 := by
  unfold tailWord_2515485
  simp only [CollatzResearch.WordTrace]
  refine ⟨91747275291834930480059909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61164850194556620320039939 91747275291834930480059909)
  ·
    refine ⟨17202614117219049465011233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 91747275291834930480059909 17202614117219049465011233)
    ·
      refine ⟨12901960587914287098758425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17202614117219049465011233 12901960587914287098758425)
      ·
        refine ⟨9676470440935715324068819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12901960587914287098758425 9676470440935715324068819)
        ·
          refine ⟨14514705661403572986103229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9676470440935715324068819 14514705661403572986103229)
          ·
            refine ⟨5443014623026339869788711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14514705661403572986103229 5443014623026339869788711)
            ·
              refine ⟨8164521934539509804683067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5443014623026339869788711 8164521934539509804683067)
              ·
                refine ⟨12246782901809264707024601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8164521934539509804683067 12246782901809264707024601)
                ·
                  refine ⟨9185087176356948530268451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12246782901809264707024601 9185087176356948530268451)
                  ·
                    refine ⟨13777630764535422795402677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9185087176356948530268451 13777630764535422795402677)
                    ·
                      refine ⟨1291652884175195887069001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13777630764535422795402677 1291652884175195887069001)
                      ·
                        rfl

theorem cell23_2515485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_2515485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2515485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2515485 prefixEnd_2515485 := by exact prefixLift 2515485
  have htrace : WordTrace (prefixWord ++ tailWord_2515485) baseStart_2515485 baseEnd_2515485 := by
    simpa [prefixWord, tailWord_2515485, baseEnd_2515485] using wordTrace_append hprefix tailTrace_2515485
  have hstable : (prefixWord ++ tailWord_2515485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2515485).length < 2 ^ (prefixWord ++ tailWord_2515485).sum := by decide
  have hdescent : baseEnd_2515485 < baseStart_2515485 := by decide
  rcases family_descends (prefixWord ++ tailWord_2515485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2515505 : List Nat := [1, 2, 2, 3, 1, 1, 2, 6, 5]
def baseStart_2515505 : Nat := 118140960795 + 2515505 * 2 ^ 59
def prefixEnd_2515505 : Nat := 4983230072969 + 3 ^ 40 * 2515505 * 2
def baseEnd_2515505 : Nat := 143518128198698423202101

theorem tailTrace_2515505 : CollatzResearch.WordTrace tailWord_2515505 prefixEnd_2515505 143518128198698423202101 := by
  unfold tailWord_2515505
  simp only [CollatzResearch.WordTrace]
  refine ⟨91748004751762473895787969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61165336501174982597191979 91748004751762473895787969)
  ·
    refine ⟨68811003563821855421840977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91748004751762473895787969 68811003563821855421840977)
    ·
      refine ⟨51608252672866391566380733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68811003563821855421840977 51608252672866391566380733)
      ·
        refine ⟨19353094752324896837392775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51608252672866391566380733 19353094752324896837392775)
        ·
          refine ⟨29029642128487345256089163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19353094752324896837392775 29029642128487345256089163)
          ·
            refine ⟨43544463192731017884133745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29029642128487345256089163 43544463192731017884133745)
            ·
              refine ⟨32658347394548263413100309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43544463192731017884133745 32658347394548263413100309)
              ·
                refine ⟨1530860034119449847489077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 32658347394548263413100309 1530860034119449847489077)
                ·
                  refine ⟨143518128198698423202101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1530860034119449847489077 143518128198698423202101)
                  ·
                    rfl

theorem cell23_2515505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 6, 5].length) (baseStart_2515505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2515505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2515505 prefixEnd_2515505 := by exact prefixLift 2515505
  have htrace : WordTrace (prefixWord ++ tailWord_2515505) baseStart_2515505 baseEnd_2515505 := by
    simpa [prefixWord, tailWord_2515505, baseEnd_2515505] using wordTrace_append hprefix tailTrace_2515505
  have hstable : (prefixWord ++ tailWord_2515505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2515505).length < 2 ^ (prefixWord ++ tailWord_2515505).sum := by decide
  have hdescent : baseEnd_2515505 < baseStart_2515505 := by decide
  rcases family_descends (prefixWord ++ tailWord_2515505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2515516 : List Nat := [2, 2, 2, 2, 3, 1, 4, 1, 2, 2, 2]
def baseStart_2515516 : Nat := 118140960795 + 2515516 * 2 ^ 59
def prefixEnd_2515516 : Nat := 4983230072969 + 3 ^ 40 * 2515516 * 2
def baseEnd_2515516 : Nat := 1291668802075485265781359

theorem tailTrace_2515516 : CollatzResearch.WordTrace tailWord_2515516 prefixEnd_2515516 1291668802075485265781359 := by
  unfold tailWord_2515516
  simp only [CollatzResearch.WordTrace]
  refine ⟨45874202977361311387219201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61165603969815081849625601 45874202977361311387219201)
  ·
    refine ⟨34405652233020983540414401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45874202977361311387219201 34405652233020983540414401)
    ·
      refine ⟨25804239174765737655310801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34405652233020983540414401 25804239174765737655310801)
      ·
        refine ⟨19353179381074303241483101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25804239174765737655310801 19353179381074303241483101)
        ·
          refine ⟨7257442267902863715556163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19353179381074303241483101 7257442267902863715556163)
          ·
            refine ⟨10886163401854295573334245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7257442267902863715556163 10886163401854295573334245)
            ·
              refine ⟨2041155637847680420000171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10886163401854295573334245 2041155637847680420000171)
              ·
                refine ⟨3061733456771520630000257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2041155637847680420000171 3061733456771520630000257)
                ·
                  refine ⟨2296300092578640472500193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3061733456771520630000257 2296300092578640472500193)
                  ·
                    refine ⟨1722225069433980354375145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2296300092578640472500193 1722225069433980354375145)
                    ·
                      refine ⟨1291668802075485265781359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1722225069433980354375145 1291668802075485265781359)
                      ·
                        rfl

theorem cell23_2515516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 4, 1, 2, 2, 2].length) (baseStart_2515516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2515516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2515516 prefixEnd_2515516 := by exact prefixLift 2515516
  have htrace : WordTrace (prefixWord ++ tailWord_2515516) baseStart_2515516 baseEnd_2515516 := by
    simpa [prefixWord, tailWord_2515516, baseEnd_2515516] using wordTrace_append hprefix tailTrace_2515516
  have hstable : (prefixWord ++ tailWord_2515516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2515516).length < 2 ^ (prefixWord ++ tailWord_2515516).sum := by decide
  have hdescent : baseEnd_2515516 < baseStart_2515516 := by decide
  rcases family_descends (prefixWord ++ tailWord_2515516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2515555 : List Nat := [1, 1, 1, 5, 1, 2, 1, 4, 2, 1, 4]
def baseStart_2515555 : Nat := 118140960795 + 2515555 * 2 ^ 59
def prefixEnd_2515555 : Nat := 4983230072969 + 3 ^ 40 * 2515555 * 2
def baseEnd_2515555 : Nat := 1291688827821010613193679

theorem tailTrace_2515555 : CollatzResearch.WordTrace tailWord_2515555 prefixEnd_2515555 1291688827821010613193679 := by
  unfold tailWord_2515555
  simp only [CollatzResearch.WordTrace]
  refine ⟨91749828401581332435108119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61166552267720888290072079 91749828401581332435108119)
  ·
    refine ⟨137624742602371998652662179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91749828401581332435108119 137624742602371998652662179)
    ·
      refine ⟨206437113903557997978993269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137624742602371998652662179 206437113903557997978993269)
      ·
        refine ⟨19353479428458562310530619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 206437113903557997978993269 19353479428458562310530619)
        ·
          refine ⟨29030219142687843465795929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19353479428458562310530619 29030219142687843465795929)
          ·
            refine ⟨21772664357015882599346947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29030219142687843465795929 21772664357015882599346947)
            ·
              refine ⟨32658996535523823899020421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21772664357015882599346947 32658996535523823899020421)
              ·
                refine ⟨6123561850410716981066329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32658996535523823899020421 6123561850410716981066329)
                ·
                  refine ⟨4592671387808037735799747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6123561850410716981066329 4592671387808037735799747)
                  ·
                    refine ⟨6889007081712056603699621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4592671387808037735799747 6889007081712056603699621)
                    ·
                      refine ⟨1291688827821010613193679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6889007081712056603699621 1291688827821010613193679)
                      ·
                        rfl

theorem cell23_2515555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 4, 2, 1, 4].length) (baseStart_2515555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2515555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2515555 prefixEnd_2515555 := by exact prefixLift 2515555
  have htrace : WordTrace (prefixWord ++ tailWord_2515555) baseStart_2515555 baseEnd_2515555 := by
    simpa [prefixWord, tailWord_2515555, baseEnd_2515555] using wordTrace_append hprefix tailTrace_2515555
  have hstable : (prefixWord ++ tailWord_2515555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2515555).length < 2 ^ (prefixWord ++ tailWord_2515555).sum := by decide
  have hdescent : baseEnd_2515555 < baseStart_2515555 := by decide
  rcases family_descends (prefixWord ++ tailWord_2515555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2515575 : List Nat := [1, 1, 3, 1, 1, 3, 2, 2, 4, 2, 3]
def baseStart_2515575 : Nat := 118140960795 + 2515575 * 2 ^ 59
def prefixEnd_2515575 : Nat := 4983230072969 + 3 ^ 40 * 2515575 * 2
def baseEnd_2515575 : Nat := 1291699097434100534943587

theorem tailTrace_2515575 : CollatzResearch.WordTrace tailWord_2515575 prefixEnd_2515575 1291699097434100534943587 := by
  unfold tailWord_2515575
  simp only [CollatzResearch.WordTrace]
  refine ⟨91750557861508875850836179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61167038574339250567224119 91750557861508875850836179)
  ·
    refine ⟨137625836792263313776254269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91750557861508875850836179 137625836792263313776254269)
    ·
      refine ⟨51609688797098742666095351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137625836792263313776254269 51609688797098742666095351)
      ·
        refine ⟨77414533195648113999143027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51609688797098742666095351 77414533195648113999143027)
        ·
          refine ⟨116121799793472170998714541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77414533195648113999143027 116121799793472170998714541)
          ·
            refine ⟨43545674922552064124517953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 116121799793472170998714541 43545674922552064124517953)
            ·
              refine ⟨32659256191914048093388465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43545674922552064124517953 32659256191914048093388465)
              ·
                refine ⟨24494442143935536070041349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32659256191914048093388465 24494442143935536070041349)
                ·
                  refine ⟨4592707901987913013132753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24494442143935536070041349 4592707901987913013132753)
                  ·
                    refine ⟨3444530926490934759849565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4592707901987913013132753 3444530926490934759849565)
                    ·
                      refine ⟨1291699097434100534943587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3444530926490934759849565 1291699097434100534943587)
                      ·
                        rfl

theorem cell23_2515575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 2, 4, 2, 3].length) (baseStart_2515575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2515575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2515575 prefixEnd_2515575 := by exact prefixLift 2515575
  have htrace : WordTrace (prefixWord ++ tailWord_2515575) baseStart_2515575 baseEnd_2515575 := by
    simpa [prefixWord, tailWord_2515575, baseEnd_2515575] using wordTrace_append hprefix tailTrace_2515575
  have hstable : (prefixWord ++ tailWord_2515575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2515575).length < 2 ^ (prefixWord ++ tailWord_2515575).sum := by decide
  have hdescent : baseEnd_2515575 < baseStart_2515575 := by decide
  rcases family_descends (prefixWord ++ tailWord_2515575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2515586 : List Nat := [3, 4, 3, 1, 1, 1, 1, 1, 1, 7]
def baseStart_2515586 : Nat := 118140960795 + 2515586 * 2 ^ 59
def prefixEnd_2515586 : Nat := 4983230072969 + 3 ^ 40 * 2515586 * 2
def baseEnd_2515586 : Nat := 430568248573766663968679

theorem tailTrace_2515586 : CollatzResearch.WordTrace tailWord_2515586 prefixEnd_2515586 430568248573766663968679 := by
  unfold tailWord_2515586
  simp only [CollatzResearch.WordTrace]
  refine ⟨22937739766117256182371653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61167306042979349819657741 22937739766117256182371653)
  ·
    refine ⟨4300826206146985534194685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22937739766117256182371653 4300826206146985534194685)
    ·
      refine ⟨1612809827305119575323007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4300826206146985534194685 1612809827305119575323007)
      ·
        refine ⟨2419214740957679362984511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1612809827305119575323007 2419214740957679362984511)
        ·
          refine ⟨3628822111436519044476767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2419214740957679362984511 3628822111436519044476767)
          ·
            refine ⟨5443233167154778566715151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3628822111436519044476767 5443233167154778566715151)
            ·
              refine ⟨8164849750732167850072727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5443233167154778566715151 8164849750732167850072727)
              ·
                refine ⟨12247274626098251775109091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8164849750732167850072727 12247274626098251775109091)
                ·
                  refine ⟨18370911939147377662663637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12247274626098251775109091 18370911939147377662663637)
                  ·
                    refine ⟨430568248573766663968679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18370911939147377662663637 430568248573766663968679)
                    ·
                      rfl

theorem cell23_2515586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_2515586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2515586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2515586 prefixEnd_2515586 := by exact prefixLift 2515586
  have htrace : WordTrace (prefixWord ++ tailWord_2515586) baseStart_2515586 baseEnd_2515586 := by
    simpa [prefixWord, tailWord_2515586, baseEnd_2515586] using wordTrace_append hprefix tailTrace_2515586
  have hstable : (prefixWord ++ tailWord_2515586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2515586).length < 2 ^ (prefixWord ++ tailWord_2515586).sum := by decide
  have hdescent : baseEnd_2515586 < baseStart_2515586 := by decide
  rcases family_descends (prefixWord ++ tailWord_2515586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2515612 : List Nat := [2, 2, 3, 2, 2, 1, 3, 2, 6]
def baseStart_2515612 : Nat := 118140960795 + 2515612 * 2 ^ 59
def prefixEnd_2515612 : Nat := 4983230072969 + 3 ^ 40 * 2515612 * 2
def baseEnd_2515612 : Nat := 143524232913146321131213

theorem tailTrace_2515612 : CollatzResearch.WordTrace tailWord_2515612 prefixEnd_2515612 143524232913146321131213 := by
  unfold tailWord_2515612
  simp only [CollatzResearch.WordTrace]
  refine ⟨45875953681187415584966545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61167938241583220779955393 45875953681187415584966545)
  ·
    refine ⟨34406965260890561688724909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45875953681187415584966545 34406965260890561688724909)
    ·
      refine ⟨12902611972833960633271841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34406965260890561688724909 12902611972833960633271841)
      ·
        refine ⟨9676958979625470474953881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12902611972833960633271841 9676958979625470474953881)
        ·
          refine ⟨7257719234719102856215411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9676958979625470474953881 7257719234719102856215411)
          ·
            refine ⟨10886578852078654284323117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7257719234719102856215411 10886578852078654284323117)
            ·
              refine ⟨4082467069529495356621169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10886578852078654284323117 4082467069529495356621169)
              ·
                refine ⟨3061850302147121517465877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4082467069529495356621169 3061850302147121517465877)
                ·
                  refine ⟨143524232913146321131213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3061850302147121517465877 143524232913146321131213)
                  ·
                    rfl

theorem cell23_2515612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 3, 2, 6].length) (baseStart_2515612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2515612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2515612 prefixEnd_2515612 := by exact prefixLift 2515612
  have htrace : WordTrace (prefixWord ++ tailWord_2515612) baseStart_2515612 baseEnd_2515612 := by
    simpa [prefixWord, tailWord_2515612, baseEnd_2515612] using wordTrace_append hprefix tailTrace_2515612
  have hstable : (prefixWord ++ tailWord_2515612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2515612).length < 2 ^ (prefixWord ++ tailWord_2515612).sum := by decide
  have hdescent : baseEnd_2515612 < baseStart_2515612 := by decide
  rcases family_descends (prefixWord ++ tailWord_2515612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2515629 : List Nat := [1, 5, 2, 1, 1, 3, 3, 1, 6]
def baseStart_2515629 : Nat := 118140960795 + 2515629 * 2 ^ 59
def prefixEnd_2515629 : Nat := 4983230072969 + 3 ^ 40 * 2515629 * 2
def baseEnd_2515629 : Nat := 143525202821049258185371

theorem tailTrace_2515629 : CollatzResearch.WordTrace tailWord_2515629 prefixEnd_2515629 143525202821049258185371 := by
  unfold tailWord_2515629
  simp only [CollatzResearch.WordTrace]
  refine ⟨91752527403313243073301941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61168351602208828715534627 91752527403313243073301941)
  ·
    refine ⟨8601799444060616538122057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 91752527403313243073301941 8601799444060616538122057)
    ·
      refine ⟨6451349583045462403591543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8601799444060616538122057 6451349583045462403591543)
      ·
        refine ⟨9677024374568193605387315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6451349583045462403591543 9677024374568193605387315)
        ·
          refine ⟨14515536561852290408080973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9677024374568193605387315 14515536561852290408080973)
          ·
            refine ⟨5443326210694608903030365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14515536561852290408080973 5443326210694608903030365)
            ·
              refine ⟨2041247329010478338636387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5443326210694608903030365 2041247329010478338636387)
              ·
                refine ⟨3061870993515717507954581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2041247329010478338636387 3061870993515717507954581)
                ·
                  refine ⟨143525202821049258185371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3061870993515717507954581 143525202821049258185371)
                  ·
                    rfl

theorem cell23_2515629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 3, 1, 6].length) (baseStart_2515629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2515629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2515629 prefixEnd_2515629 := by exact prefixLift 2515629
  have htrace : WordTrace (prefixWord ++ tailWord_2515629) baseStart_2515629 baseEnd_2515629 := by
    simpa [prefixWord, tailWord_2515629, baseEnd_2515629] using wordTrace_append hprefix tailTrace_2515629
  have hstable : (prefixWord ++ tailWord_2515629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2515629).length < 2 ^ (prefixWord ++ tailWord_2515629).sum := by decide
  have hdescent : baseEnd_2515629 < baseStart_2515629 := by decide
  rcases family_descends (prefixWord ++ tailWord_2515629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2515642 : List Nat := [3, 1, 1, 1, 2, 3, 4, 2, 1, 5]
def baseStart_2515642 : Nat := 118140960795 + 2515642 * 2 ^ 59
def prefixEnd_2515642 : Nat := 4983230072969 + 3 ^ 40 * 2515642 * 2
def baseEnd_2515642 : Nat := 430577833545983924268593

theorem tailTrace_2515642 : CollatzResearch.WordTrace tailWord_2515642 prefixEnd_2515642 430577833545983924268593 := by
  unfold tailWord_2515642
  simp only [CollatzResearch.WordTrace]
  refine ⟨22938250388066536573381295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61168667701510764195683453 22938250388066536573381295)
  ·
    refine ⟨34407375582099804860071943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22938250388066536573381295 34407375582099804860071943)
    ·
      refine ⟨51611063373149707290107915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34407375582099804860071943 51611063373149707290107915)
      ·
        refine ⟨77416595059724560935161873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51611063373149707290107915 77416595059724560935161873)
        ·
          refine ⟨58062446294793420701371405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77416595059724560935161873 58062446294793420701371405)
          ·
            refine ⟨21773417360547532763014277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58062446294793420701371405 21773417360547532763014277)
            ·
              refine ⟨4082515755102662393065177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21773417360547532763014277 4082515755102662393065177)
              ·
                refine ⟨3061886816326996794798883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4082515755102662393065177 3061886816326996794798883)
                ·
                  refine ⟨4592830224490495192198325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3061886816326996794798883 4592830224490495192198325)
                  ·
                    refine ⟨430577833545983924268593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4592830224490495192198325 430577833545983924268593)
                    ·
                      rfl

theorem cell23_2515642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 4, 2, 1, 5].length) (baseStart_2515642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2515642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2515642 prefixEnd_2515642 := by exact prefixLift 2515642
  have htrace : WordTrace (prefixWord ++ tailWord_2515642) baseStart_2515642 baseEnd_2515642 := by
    simpa [prefixWord, tailWord_2515642, baseEnd_2515642] using wordTrace_append hprefix tailTrace_2515642
  have hstable : (prefixWord ++ tailWord_2515642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2515642).length < 2 ^ (prefixWord ++ tailWord_2515642).sum := by decide
  have hdescent : baseEnd_2515642 < baseStart_2515642 := by decide
  rcases family_descends (prefixWord ++ tailWord_2515642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2515656 : List Nat := [2, 1, 3, 1, 2, 3, 3, 3, 1, 1, 3]
def baseStart_2515656 : Nat := 118140960795 + 2515656 * 2 ^ 59
def prefixEnd_2515656 : Nat := 4983230072969 + 3 ^ 40 * 2515656 * 2
def baseEnd_2515656 : Nat := 1291740689367114718030715

theorem tailTrace_2515656 : CollatzResearch.WordTrace tailWord_2515656 prefixEnd_2515656 1291740689367114718030715 := by
  unfold tailWord_2515656
  simp only [CollatzResearch.WordTrace]
  refine ⟨45876756087107713342267411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61169008116143617789689881 45876756087107713342267411)
  ·
    refine ⟨68815134130661570013401117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45876756087107713342267411 68815134130661570013401117)
    ·
      refine ⟨25805675298998088755025419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68815134130661570013401117 25805675298998088755025419)
      ·
        refine ⟨38708512948497133132538129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25805675298998088755025419 38708512948497133132538129)
        ·
          refine ⟨29031384711372849849403597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38708512948497133132538129 29031384711372849849403597)
          ·
            refine ⟨10886769266764818693526349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29031384711372849849403597 10886769266764818693526349)
            ·
              refine ⟨4082538475036807010072381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10886769266764818693526349 4082538475036807010072381)
              ·
                refine ⟨1530951928138802628777143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4082538475036807010072381 1530951928138802628777143)
                ·
                  refine ⟨2296427892208203943165715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1530951928138802628777143 2296427892208203943165715)
                  ·
                    refine ⟨3444641838312305914748573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2296427892208203943165715 3444641838312305914748573)
                    ·
                      refine ⟨1291740689367114718030715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3444641838312305914748573 1291740689367114718030715)
                      ·
                        rfl

theorem cell23_2515656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 3, 3, 1, 1, 3].length) (baseStart_2515656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2515656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2515656 prefixEnd_2515656 := by exact prefixLift 2515656
  have htrace : WordTrace (prefixWord ++ tailWord_2515656) baseStart_2515656 baseEnd_2515656 := by
    simpa [prefixWord, tailWord_2515656, baseEnd_2515656] using wordTrace_append hprefix tailTrace_2515656
  have hstable : (prefixWord ++ tailWord_2515656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2515656).length < 2 ^ (prefixWord ++ tailWord_2515656).sum := by decide
  have hdescent : baseEnd_2515656 < baseStart_2515656 := by decide
  rcases family_descends (prefixWord ++ tailWord_2515656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2515666 : List Nat := [3, 2, 2, 2, 3, 1, 1, 2, 2, 3, 2]
def baseStart_2515666 : Nat := 118140960795 + 2515666 * 2 ^ 59
def prefixEnd_2515666 : Nat := 4983230072969 + 3 ^ 40 * 2515666 * 2
def baseEnd_2515666 : Nat := 1291745824173659678905669

theorem tailTrace_2515666 : CollatzResearch.WordTrace tailWord_2515666 prefixEnd_2515666 1291745824173659678905669 := by
  unfold tailWord_2515666
  simp only [CollatzResearch.WordTrace]
  refine ⟨22938469226044799598099713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61169251269452798928265901 22938469226044799598099713)
  ·
    refine ⟨17203851919533599698574785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22938469226044799598099713 17203851919533599698574785)
    ·
      refine ⟨12902888939650199773931089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17203851919533599698574785 12902888939650199773931089)
      ·
        refine ⟨9677166704737649830448317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12902888939650199773931089 9677166704737649830448317)
        ·
          refine ⟨3628937514276618686418119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9677166704737649830448317 3628937514276618686418119)
          ·
            refine ⟨5443406271414928029627179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3628937514276618686418119 5443406271414928029627179)
            ·
              refine ⟨8165109407122392044440769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5443406271414928029627179 8165109407122392044440769)
              ·
                refine ⟨6123832055341794033330577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8165109407122392044440769 6123832055341794033330577)
                ·
                  refine ⟨4592874041506345524997933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6123832055341794033330577 4592874041506345524997933)
                  ·
                    refine ⟨1722327765564879571874225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4592874041506345524997933 1722327765564879571874225)
                    ·
                      refine ⟨1291745824173659678905669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1722327765564879571874225 1291745824173659678905669)
                      ·
                        rfl

theorem cell23_2515666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 2, 2, 3, 2].length) (baseStart_2515666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2515666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2515666 prefixEnd_2515666 := by exact prefixLift 2515666
  have htrace : WordTrace (prefixWord ++ tailWord_2515666) baseStart_2515666 baseEnd_2515666 := by
    simpa [prefixWord, tailWord_2515666, baseEnd_2515666] using wordTrace_append hprefix tailTrace_2515666
  have hstable : (prefixWord ++ tailWord_2515666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2515666).length < 2 ^ (prefixWord ++ tailWord_2515666).sum := by decide
  have hdescent : baseEnd_2515666 < baseStart_2515666 := by decide
  rcases family_descends (prefixWord ++ tailWord_2515666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2515672 : List Nat := [2, 1, 2, 2, 3, 2, 2, 1, 4, 4]
def baseStart_2515672 : Nat := 118140960795 + 2515672 * 2 ^ 59
def prefixEnd_2515672 : Nat := 4983230072969 + 3 ^ 40 * 2515672 * 2
def baseEnd_2515672 : Nat := 430582968352528885143547

theorem tailTrace_2515672 : CollatzResearch.WordTrace tailWord_2515672 prefixEnd_2515672 430582968352528885143547 := by
  unfold tailWord_2515672
  simp only [CollatzResearch.WordTrace]
  refine ⟨45877047871078730708558635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61169397161438307611411513 45877047871078730708558635)
  ·
    refine ⟨68815571806618096062837953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45877047871078730708558635 68815571806618096062837953)
    ·
      refine ⟨51611678854963572047128465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68815571806618096062837953 51611678854963572047128465)
      ·
        refine ⟨38708759141222679035346349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51611678854963572047128465 38708759141222679035346349)
        ·
          refine ⟨14515784677958504638254881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38708759141222679035346349 14515784677958504638254881)
          ·
            refine ⟨10886838508468878478691161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14515784677958504638254881 10886838508468878478691161)
            ·
              refine ⟨8165128881351658859018371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10886838508468878478691161 8165128881351658859018371)
              ·
                refine ⟨12247693322027488288527557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8165128881351658859018371 12247693322027488288527557)
                ·
                  refine ⟨2296442497880154054098917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12247693322027488288527557 2296442497880154054098917)
                  ·
                    refine ⟨430582968352528885143547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2296442497880154054098917 430582968352528885143547)
                    ·
                      rfl

theorem cell23_2515672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 1, 4, 4].length) (baseStart_2515672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2515672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2515672 prefixEnd_2515672 := by exact prefixLift 2515672
  have htrace : WordTrace (prefixWord ++ tailWord_2515672) baseStart_2515672 baseEnd_2515672 := by
    simpa [prefixWord, tailWord_2515672, baseEnd_2515672] using wordTrace_append hprefix tailTrace_2515672
  have hstable : (prefixWord ++ tailWord_2515672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2515672).length < 2 ^ (prefixWord ++ tailWord_2515672).sum := by decide
  have hdescent : baseEnd_2515672 < baseStart_2515672 := by decide
  rcases family_descends (prefixWord ++ tailWord_2515672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2515685 : List Nat := [1, 3, 1, 4, 1, 2, 1, 10]
def baseStart_2515685 : Nat := 118140960795 + 2515685 * 2 ^ 59
def prefixEnd_2515685 : Nat := 4983230072969 + 3 ^ 40 * 2515685 * 2
def baseEnd_2515685 : Nat := 47842799270596114984003

theorem tailTrace_2515685 : CollatzResearch.WordTrace tailWord_2515685 prefixEnd_2515685 47842799270596114984003 := by
  unfold tailWord_2515685
  simp only [CollatzResearch.WordTrace]
  refine ⟨91754569891110364637340509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61169713260740243091560339 91754569891110364637340509)
  ·
    refine ⟨34407963709166386739002691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91754569891110364637340509 34407963709166386739002691)
    ·
      refine ⟨51611945563749580108504037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34407963709166386739002691 51611945563749580108504037)
      ·
        refine ⟨9677239793203046270344507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51611945563749580108504037 9677239793203046270344507)
        ·
          refine ⟨14515859689804569405516761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9677239793203046270344507 14515859689804569405516761)
          ·
            refine ⟨10886894767353427054137571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14515859689804569405516761 10886894767353427054137571)
            ·
              refine ⟨16330342151030140581206357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10886894767353427054137571 16330342151030140581206357)
              ·
                refine ⟨47842799270596114984003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 16330342151030140581206357 47842799270596114984003)
                ·
                  rfl

theorem cell23_2515685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 10].length) (baseStart_2515685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2515685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2515685 prefixEnd_2515685 := by exact prefixLift 2515685
  have htrace : WordTrace (prefixWord ++ tailWord_2515685) baseStart_2515685 baseEnd_2515685 := by
    simpa [prefixWord, tailWord_2515685, baseEnd_2515685] using wordTrace_append hprefix tailTrace_2515685
  have hstable : (prefixWord ++ tailWord_2515685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2515685).length < 2 ^ (prefixWord ++ tailWord_2515685).sum := by decide
  have hdescent : baseEnd_2515685 < baseStart_2515685 := by decide
  rcases family_descends (prefixWord ++ tailWord_2515685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2515689 : List Nat := [1, 2, 1, 1, 1, 2, 8, 1, 2, 4]
def baseStart_2515689 : Nat := 118140960795 + 2515689 * 2 ^ 59
def prefixEnd_2515689 : Nat := 4983230072969 + 3 ^ 40 * 2515689 * 2
def baseEnd_2515689 : Nat := 430585878076237696306021

theorem tailTrace_2515689 : CollatzResearch.WordTrace tailWord_2515689 prefixEnd_2515689 430585878076237696306021 := by
  unfold tailWord_2515689
  simp only [CollatzResearch.WordTrace]
  refine ⟨91754715783095873320486121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61169810522063915546990747 91754715783095873320486121)
  ·
    refine ⟨68816036837321904990364591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91754715783095873320486121 68816036837321904990364591)
    ·
      refine ⟨103224055255982857485546887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68816036837321904990364591 103224055255982857485546887)
      ·
        refine ⟨154836082883974286228320331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103224055255982857485546887 154836082883974286228320331)
        ·
          refine ⟨232254124325961429342480497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154836082883974286228320331 232254124325961429342480497)
          ·
            refine ⟨174190593244471072006860373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 232254124325961429342480497 174190593244471072006860373)
            ·
              refine ⟨2041296014583645375080395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 174190593244471072006860373 2041296014583645375080395)
              ·
                refine ⟨3061944021875468062620593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2041296014583645375080395 3061944021875468062620593)
                ·
                  refine ⟨2296458016406601046965445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3061944021875468062620593 2296458016406601046965445)
                  ·
                    refine ⟨430585878076237696306021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2296458016406601046965445 430585878076237696306021)
                    ·
                      rfl

theorem cell23_2515689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 8, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 8, 1, 2, 4].length) (baseStart_2515689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2515689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2515689 prefixEnd_2515689 := by exact prefixLift 2515689
  have htrace : WordTrace (prefixWord ++ tailWord_2515689) baseStart_2515689 baseEnd_2515689 := by
    simpa [prefixWord, tailWord_2515689, baseEnd_2515689] using wordTrace_append hprefix tailTrace_2515689
  have hstable : (prefixWord ++ tailWord_2515689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2515689).length < 2 ^ (prefixWord ++ tailWord_2515689).sum := by decide
  have hdescent : baseEnd_2515689 < baseStart_2515689 := by decide
  rcases family_descends (prefixWord ++ tailWord_2515689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2515700 : List Nat := [2, 6, 1, 1, 2, 1, 2, 1, 2, 3, 2]
def baseStart_2515700 : Nat := 118140960795 + 2515700 * 2 ^ 59
def prefixEnd_2515700 : Nat := 4983230072969 + 3 ^ 40 * 2515700 * 2
def baseEnd_2515700 : Nat := 1291763282515912545880513

theorem tailTrace_2515700 : CollatzResearch.WordTrace tailWord_2515700 prefixEnd_2515700 1291763282515912545880513 := by
  unfold tailWord_2515700
  simp only [CollatzResearch.WordTrace]
  refine ⟨45877558493028011099568277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61170077990704014799424369 45877558493028011099568277)
  ·
    refine ⟨2150510554360688020292263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 45877558493028011099568277 2150510554360688020292263)
    ·
      refine ⟨3225765831541032030438395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2150510554360688020292263 3225765831541032030438395)
      ·
        refine ⟨4838648747311548045657593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3225765831541032030438395 4838648747311548045657593)
        ·
          refine ⟨3628986560483661034243195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4838648747311548045657593 3628986560483661034243195)
          ·
            refine ⟨5443479840725491551364793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3628986560483661034243195 5443479840725491551364793)
            ·
              refine ⟨4082609880544118663523595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5443479840725491551364793 4082609880544118663523595)
              ·
                refine ⟨6123914820816177995285393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4082609880544118663523595 6123914820816177995285393)
                ·
                  refine ⟨4592936115612133496464045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6123914820816177995285393 4592936115612133496464045)
                  ·
                    refine ⟨1722351043354550061174017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4592936115612133496464045 1722351043354550061174017)
                    ·
                      refine ⟨1291763282515912545880513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1722351043354550061174017 1291763282515912545880513)
                      ·
                        rfl

theorem cell23_2515700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 2, 1, 2, 3, 2].length) (baseStart_2515700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2515700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2515700 prefixEnd_2515700 := by exact prefixLift 2515700
  have htrace : WordTrace (prefixWord ++ tailWord_2515700) baseStart_2515700 baseEnd_2515700 := by
    simpa [prefixWord, tailWord_2515700, baseEnd_2515700] using wordTrace_append hprefix tailTrace_2515700
  have hstable : (prefixWord ++ tailWord_2515700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2515700).length < 2 ^ (prefixWord ++ tailWord_2515700).sum := by decide
  have hdescent : baseEnd_2515700 < baseStart_2515700 := by decide
  rcases family_descends (prefixWord ++ tailWord_2515700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2515716 : List Nat := [2, 3, 2, 2, 1, 1, 5, 1, 1, 2, 3]
def baseStart_2515716 : Nat := 118140960795 + 2515716 * 2 ^ 59
def prefixEnd_2515716 : Nat := 4983230072969 + 3 ^ 40 * 2515716 * 2
def baseEnd_2515716 : Nat := 1291771498206384483280439

theorem tailTrace_2515716 : CollatzResearch.WordTrace tailWord_2515716 prefixEnd_2515716 1291771498206384483280439 := by
  unfold tailWord_2515716
  simp only [CollatzResearch.WordTrace]
  refine ⟨45877850276999028465859501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61170467035998704621146001 45877850276999028465859501)
  ·
    refine ⟨17204193853874635674697313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45877850276999028465859501 17204193853874635674697313)
    ·
      refine ⟨12903145390405976756022985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17204193853874635674697313 12903145390405976756022985)
      ·
        refine ⟨9677359042804482567017239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12903145390405976756022985 9677359042804482567017239)
        ·
          refine ⟨14516038564206723850525859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9677359042804482567017239 14516038564206723850525859)
          ·
            refine ⟨21774057846310085775788789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14516038564206723850525859 21774057846310085775788789)
            ·
              refine ⟨2041317923091570541480199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21774057846310085775788789 2041317923091570541480199)
              ·
                refine ⟨3061976884637355812220299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2041317923091570541480199 3061976884637355812220299)
                ·
                  refine ⟨4592965326956033718330449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3061976884637355812220299 4592965326956033718330449)
                  ·
                    refine ⟨3444723995217025288747837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4592965326956033718330449 3444723995217025288747837)
                    ·
                      refine ⟨1291771498206384483280439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3444723995217025288747837 1291771498206384483280439)
                      ·
                        rfl

theorem cell23_2515716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 5, 1, 1, 2, 3].length) (baseStart_2515716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2515716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2515716 prefixEnd_2515716 := by exact prefixLift 2515716
  have htrace : WordTrace (prefixWord ++ tailWord_2515716) baseStart_2515716 baseEnd_2515716 := by
    simpa [prefixWord, tailWord_2515716, baseEnd_2515716] using wordTrace_append hprefix tailTrace_2515716
  have hstable : (prefixWord ++ tailWord_2515716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2515716).length < 2 ^ (prefixWord ++ tailWord_2515716).sum := by decide
  have hdescent : baseEnd_2515716 < baseStart_2515716 := by decide
  rcases family_descends (prefixWord ++ tailWord_2515716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2515729 : List Nat := [1, 2, 2, 1, 1, 3, 3, 4, 2, 1, 3]
def baseStart_2515729 : Nat := 118140960795 + 2515729 * 2 ^ 59
def prefixEnd_2515729 : Nat := 4983230072969 + 3 ^ 40 * 2515729 * 2
def baseEnd_2515729 : Nat := 1291778173454892932417879

theorem tailTrace_2515729 : CollatzResearch.WordTrace tailWord_2515729 prefixEnd_2515729 1291778173454892932417879 := by
  unfold tailWord_2515729
  simp only [CollatzResearch.WordTrace]
  refine ⟨91756174702950960151942241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61170783135300640101294827 91756174702950960151942241)
  ·
    refine ⟨68817131027213220113956681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91756174702950960151942241 68817131027213220113956681)
    ·
      refine ⟨51612848270409915085467511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68817131027213220113956681 51612848270409915085467511)
      ·
        refine ⟨77419272405614872628201267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51612848270409915085467511 77419272405614872628201267)
        ·
          refine ⟨116128908608422308942301901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77419272405614872628201267 116128908608422308942301901)
          ·
            refine ⟨43548340728158365853363213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 116128908608422308942301901 43548340728158365853363213)
            ·
              refine ⟨16330627773059387195011205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43548340728158365853363213 16330627773059387195011205)
              ·
                refine ⟨3061992707448635099064601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16330627773059387195011205 3061992707448635099064601)
                ·
                  refine ⟨2296494530586476324298451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3061992707448635099064601 2296494530586476324298451)
                  ·
                    refine ⟨3444741795879714486447677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2296494530586476324298451 3444741795879714486447677)
                    ·
                      refine ⟨1291778173454892932417879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3444741795879714486447677 1291778173454892932417879)
                      ·
                        rfl

theorem cell23_2515729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 4, 2, 1, 3].length) (baseStart_2515729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2515729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2515729 prefixEnd_2515729 := by exact prefixLift 2515729
  have htrace : WordTrace (prefixWord ++ tailWord_2515729) baseStart_2515729 baseEnd_2515729 := by
    simpa [prefixWord, tailWord_2515729, baseEnd_2515729] using wordTrace_append hprefix tailTrace_2515729
  have hstable : (prefixWord ++ tailWord_2515729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2515729).length < 2 ^ (prefixWord ++ tailWord_2515729).sum := by decide
  have hdescent : baseEnd_2515729 < baseStart_2515729 := by decide
  rcases family_descends (prefixWord ++ tailWord_2515729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2515746 : List Nat := [3, 3, 1, 1, 2, 2, 2, 3, 2, 1, 3]
def baseStart_2515746 : Nat := 118140960795 + 2515746 * 2 ^ 59
def prefixEnd_2515746 : Nat := 4983230072969 + 3 ^ 40 * 2515746 * 2
def baseEnd_2515746 : Nat := 1291786902626019365905301

theorem tailTrace_2515746 : CollatzResearch.WordTrace tailWord_2515746 prefixEnd_2515746 1291786902626019365905301 := by
  unfold tailWord_2515746
  simp only [CollatzResearch.WordTrace]
  refine ⟨22939198685972343013827773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61171196495926248036874061 22939198685972343013827773)
  ·
    refine ⟨8602199507239628630185415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22939198685972343013827773 8602199507239628630185415)
    ·
      refine ⟨12903299260859442945278123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8602199507239628630185415 12903299260859442945278123)
      ·
        refine ⟨19354948891289164417917185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12903299260859442945278123 19354948891289164417917185)
        ·
          refine ⟨14516211668466873313437889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19354948891289164417917185 14516211668466873313437889)
          ·
            refine ⟨10887158751350154985078417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14516211668466873313437889 10887158751350154985078417)
            ·
              refine ⟨8165369063512616238808813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10887158751350154985078417 8165369063512616238808813)
              ·
                refine ⟨3062013398817231089553305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8165369063512616238808813 3062013398817231089553305)
                ·
                  refine ⟨2296510049112923317164979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3062013398817231089553305 2296510049112923317164979)
                  ·
                    refine ⟨3444765073669384975747469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2296510049112923317164979 3444765073669384975747469)
                    ·
                      refine ⟨1291786902626019365905301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3444765073669384975747469 1291786902626019365905301)
                      ·
                        rfl

theorem cell23_2515746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 3, 2, 1, 3].length) (baseStart_2515746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2515746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2515746 prefixEnd_2515746 := by exact prefixLift 2515746
  have htrace : WordTrace (prefixWord ++ tailWord_2515746) baseStart_2515746 baseEnd_2515746 := by
    simpa [prefixWord, tailWord_2515746, baseEnd_2515746] using wordTrace_append hprefix tailTrace_2515746
  have hstable : (prefixWord ++ tailWord_2515746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2515746).length < 2 ^ (prefixWord ++ tailWord_2515746).sum := by decide
  have hdescent : baseEnd_2515746 < baseStart_2515746 := by decide
  rcases family_descends (prefixWord ++ tailWord_2515746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2515752 : List Nat := [2, 1, 5, 1, 1, 1, 1, 2, 2, 3, 4]
def baseStart_2515752 : Nat := 118140960795 + 2515752 * 2 ^ 59
def prefixEnd_2515752 : Nat := 4983230072969 + 3 ^ 40 * 2515752 * 2
def baseEnd_2515752 : Nat := 1291789983509946342430273

theorem tailTrace_2515752 : CollatzResearch.WordTrace tailWord_2515752 prefixEnd_2515752 1291789983509946342430273 := by
  unfold tailWord_2515752
  simp only [CollatzResearch.WordTrace]
  refine ⟨45878506790933817540014755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61171342387911756720019673 45878506790933817540014755)
  ·
    refine ⟨68817760186400726310022133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45878506790933817540014755 68817760186400726310022133)
    ·
      refine ⟨6451665017475068091564575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 68817760186400726310022133 6451665017475068091564575)
      ·
        refine ⟨9677497526212602137346863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6451665017475068091564575 9677497526212602137346863)
        ·
          refine ⟨14516246289318903206020295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9677497526212602137346863 14516246289318903206020295)
          ·
            refine ⟨21774369433978354809030443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14516246289318903206020295 21774369433978354809030443)
            ·
              refine ⟨32661554150967532213545665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21774369433978354809030443 32661554150967532213545665)
              ·
                refine ⟨24496165613225649160159249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32661554150967532213545665 24496165613225649160159249)
                ·
                  refine ⟨18372124209919236870119437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24496165613225649160159249 18372124209919236870119437)
                  ·
                    refine ⟨6889546578719713826294789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18372124209919236870119437 6889546578719713826294789)
                    ·
                      refine ⟨1291789983509946342430273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6889546578719713826294789 1291789983509946342430273)
                      ·
                        rfl

theorem cell23_2515752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_2515752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2515752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2515752 prefixEnd_2515752 := by exact prefixLift 2515752
  have htrace : WordTrace (prefixWord ++ tailWord_2515752) baseStart_2515752 baseEnd_2515752 := by
    simpa [prefixWord, tailWord_2515752, baseEnd_2515752] using wordTrace_append hprefix tailTrace_2515752
  have hstable : (prefixWord ++ tailWord_2515752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2515752).length < 2 ^ (prefixWord ++ tailWord_2515752).sum := by decide
  have hdescent : baseEnd_2515752 < baseStart_2515752 := by decide
  rcases family_descends (prefixWord ++ tailWord_2515752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2515773 : List Nat := [1, 4, 1, 4, 2, 1, 1, 3, 1, 3, 2]
def baseStart_2515773 : Nat := 118140960795 + 2515773 * 2 ^ 59
def prefixEnd_2515773 : Nat := 4983230072969 + 3 ^ 40 * 2515773 * 2
def baseEnd_2515773 : Nat := 1291800766603690760267677

theorem tailTrace_2515773 : CollatzResearch.WordTrace tailWord_2515773 prefixEnd_2515773 1291800766603690760267677 := by
  unfold tailWord_2515773
  simp only [CollatzResearch.WordTrace]
  refine ⟨91757779514791555666543973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61171853009861037111029315 91757779514791555666543973)
  ·
    refine ⟨17204583659023416687476995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 91757779514791555666543973 17204583659023416687476995)
    ·
      refine ⟨25806875488535125031215493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17204583659023416687476995 25806875488535125031215493)
      ·
        refine ⟨4838789154100335943352905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25806875488535125031215493 4838789154100335943352905)
        ·
          refine ⟨3629091865575251957514679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4838789154100335943352905 3629091865575251957514679)
          ·
            refine ⟨5443637798362877936272019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3629091865575251957514679 5443637798362877936272019)
            ·
              refine ⟨8165456697544316904408029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5443637798362877936272019 8165456697544316904408029)
              ·
                refine ⟨3062046261579118839153011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8165456697544316904408029 3062046261579118839153011)
                ·
                  refine ⟨4593069392368678258729517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3062046261579118839153011 4593069392368678258729517)
                  ·
                    refine ⟨1722401022138254347023569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4593069392368678258729517 1722401022138254347023569)
                    ·
                      refine ⟨1291800766603690760267677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1722401022138254347023569 1291800766603690760267677)
                      ·
                        rfl

theorem cell23_2515773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 3, 1, 3, 2].length) (baseStart_2515773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2515773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2515773 prefixEnd_2515773 := by exact prefixLift 2515773
  have htrace : WordTrace (prefixWord ++ tailWord_2515773) baseStart_2515773 baseEnd_2515773 := by
    simpa [prefixWord, tailWord_2515773, baseEnd_2515773] using wordTrace_append hprefix tailTrace_2515773
  have hstable : (prefixWord ++ tailWord_2515773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2515773).length < 2 ^ (prefixWord ++ tailWord_2515773).sum := by decide
  have hdescent : baseEnd_2515773 < baseStart_2515773 := by decide
  rcases family_descends (prefixWord ++ tailWord_2515773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2515786 : List Nat := [3, 1, 2, 1, 1, 1, 2, 6, 2, 2, 2]
def baseStart_2515786 : Nat := 118140960795 + 2515786 * 2 ^ 59
def prefixEnd_2515786 : Nat := 4983230072969 + 3 ^ 40 * 2515786 * 2
def baseEnd_2515786 : Nat := 1291807441852199209405117

theorem tailTrace_2515786 : CollatzResearch.WordTrace tailWord_2515786 prefixEnd_2515786 1291807441852199209405117 := by
  unfold tailWord_2515786
  simp only [CollatzResearch.WordTrace]
  refine ⟨22939563415936114721691803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61172169109162972591178141 22939563415936114721691803)
  ·
    refine ⟨34409345123904172082537705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22939563415936114721691803 34409345123904172082537705)
    ·
      refine ⟨25807008842928129061903279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34409345123904172082537705 25807008842928129061903279)
      ·
        refine ⟨38710513264392193592854919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25807008842928129061903279 38710513264392193592854919)
        ·
          refine ⟨58065769896588290389282379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38710513264392193592854919 58065769896588290389282379)
          ·
            refine ⟨87098654844882435583923569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58065769896588290389282379 87098654844882435583923569)
            ·
              refine ⟨65323991133661826687942677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87098654844882435583923569 65323991133661826687942677)
              ·
                refine ⟨3062062084390398125997313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 65323991133661826687942677 3062062084390398125997313)
                ·
                  refine ⟨2296546563292798594497985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3062062084390398125997313 2296546563292798594497985)
                  ·
                    refine ⟨1722409922469598945873489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2296546563292798594497985 1722409922469598945873489)
                    ·
                      refine ⟨1291807441852199209405117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1722409922469598945873489 1291807441852199209405117)
                      ·
                        rfl

theorem cell23_2515786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 6, 2, 2, 2].length) (baseStart_2515786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2515786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2515786 prefixEnd_2515786 := by exact prefixLift 2515786
  have htrace : WordTrace (prefixWord ++ tailWord_2515786) baseStart_2515786 baseEnd_2515786 := by
    simpa [prefixWord, tailWord_2515786, baseEnd_2515786] using wordTrace_append hprefix tailTrace_2515786
  have hstable : (prefixWord ++ tailWord_2515786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2515786).length < 2 ^ (prefixWord ++ tailWord_2515786).sum := by decide
  have hdescent : baseEnd_2515786 < baseStart_2515786 := by decide
  rcases family_descends (prefixWord ++ tailWord_2515786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2515869 : List Nat := [1, 4, 2, 1, 2, 1, 2, 1, 5, 4]
def baseStart_2515869 : Nat := 118140960795 + 2515869 * 2 ^ 59
def prefixEnd_2515869 : Nat := 4983230072969 + 3 ^ 40 * 2515869 * 2
def baseEnd_2515869 : Nat := 430616686915507461555745

theorem tailTrace_2515869 : CollatzResearch.WordTrace tailWord_2515869 prefixEnd_2515869 430616686915507461555745 := by
  unfold tailWord_2515869
  simp only [CollatzResearch.WordTrace]
  refine ⟨91761280922443764062038661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61174187281629176041359107 91761280922443764062038661)
  ·
    refine ⟨17205240172958205761632249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 91761280922443764062038661 17205240172958205761632249)
    ·
      refine ⟨12903930129718654321224187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17205240172958205761632249 12903930129718654321224187)
      ·
        refine ⟨19355895194577981481836281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12903930129718654321224187 19355895194577981481836281)
        ·
          refine ⟨14516921395933486111377211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19355895194577981481836281 14516921395933486111377211)
          ·
            refine ⟨21775382093900229167065817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14516921395933486111377211 21775382093900229167065817)
            ·
              refine ⟨16331536570425171875299363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21775382093900229167065817 16331536570425171875299363)
              ·
                refine ⟨24497304855637757812949045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16331536570425171875299363 24497304855637757812949045)
                ·
                  refine ⟨2296622330216039794963973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24497304855637757812949045 2296622330216039794963973)
                  ·
                    refine ⟨430616686915507461555745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2296622330216039794963973 430616686915507461555745)
                    ·
                      rfl

theorem cell23_2515869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 1, 5, 4].length) (baseStart_2515869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2515869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2515869 prefixEnd_2515869 := by exact prefixLift 2515869
  have htrace : WordTrace (prefixWord ++ tailWord_2515869) baseStart_2515869 baseEnd_2515869 := by
    simpa [prefixWord, tailWord_2515869, baseEnd_2515869] using wordTrace_append hprefix tailTrace_2515869
  have hstable : (prefixWord ++ tailWord_2515869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2515869).length < 2 ^ (prefixWord ++ tailWord_2515869).sum := by decide
  have hdescent : baseEnd_2515869 < baseStart_2515869 := by decide
  rcases family_descends (prefixWord ++ tailWord_2515869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2515872 : List Nat := [2, 1, 1, 4, 1, 1, 2, 1, 2, 4, 4]
def baseStart_2515872 : Nat := 118140960795 + 2515872 * 2 ^ 59
def prefixEnd_2515872 : Nat := 4983230072969 + 3 ^ 40 * 2515872 * 2
def baseEnd_2515872 : Nat := 1291851601188485872929721

theorem tailTrace_2515872 : CollatzResearch.WordTrace tailWord_2515872 prefixEnd_2515872 1291851601188485872929721 := by
  unfold tailWord_2515872
  simp only [CollatzResearch.WordTrace]
  refine ⟨45880695170716447787198935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61174260227621930382931913 45880695170716447787198935)
  ·
    refine ⟨68821042756074671680798403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45880695170716447787198935 68821042756074671680798403)
    ·
      refine ⟨103231564134112007521197605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68821042756074671680798403 103231564134112007521197605)
      ·
        refine ⟨19355918275146001410224551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 103231564134112007521197605 19355918275146001410224551)
        ·
          refine ⟨29033877412719002115336827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19355918275146001410224551 29033877412719002115336827)
          ·
            refine ⟨43550816119078503173005241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29033877412719002115336827 43550816119078503173005241)
            ·
              refine ⟨32663112089308877379753931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43550816119078503173005241 32663112089308877379753931)
              ·
                refine ⟨48994668133963316069630897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32663112089308877379753931 48994668133963316069630897)
                ·
                  refine ⟨36746001100472487052223173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48994668133963316069630897 36746001100472487052223173)
                  ·
                    refine ⟨6889875206338591322291845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36746001100472487052223173 6889875206338591322291845)
                    ·
                      refine ⟨1291851601188485872929721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6889875206338591322291845 1291851601188485872929721)
                      ·
                        rfl

theorem cell23_2515872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 1, 2, 4, 4].length) (baseStart_2515872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2515872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2515872 prefixEnd_2515872 := by exact prefixLift 2515872
  have htrace : WordTrace (prefixWord ++ tailWord_2515872) baseStart_2515872 baseEnd_2515872 := by
    simpa [prefixWord, tailWord_2515872, baseEnd_2515872] using wordTrace_append hprefix tailTrace_2515872
  have hstable : (prefixWord ++ tailWord_2515872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2515872).length < 2 ^ (prefixWord ++ tailWord_2515872).sum := by decide
  have hdescent : baseEnd_2515872 < baseStart_2515872 := by decide
  rcases family_descends (prefixWord ++ tailWord_2515872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2515894 : List Nat := [5, 1, 4, 1, 1, 2, 2, 2, 5]
def baseStart_2515894 : Nat := 118140960795 + 2515894 * 2 ^ 59
def prefixEnd_2515894 : Nat := 4983230072969 + 3 ^ 40 * 2515894 * 2
def baseEnd_2515894 : Nat := 143540321973653865206069

theorem tailTrace_2515894 : CollatzResearch.WordTrace tailWord_2515894 prefixEnd_2515894 143540321973653865206069 := by
  unfold tailWord_2515894
  simp only [CollatzResearch.WordTrace]
  refine ⟨5735137046709574583231171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 61174795164902128887799157 5735137046709574583231171)
  ·
    refine ⟨8602705570064361874846757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5735137046709574583231171 8602705570064361874846757)
    ·
      refine ⟨1613007294387067851533767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8602705570064361874846757 1613007294387067851533767)
      ·
        refine ⟨2419510941580601777300651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1613007294387067851533767 2419510941580601777300651)
        ·
          refine ⟨3629266412370902665950977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2419510941580601777300651 3629266412370902665950977)
          ·
            refine ⟨2721949809278176999463233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3629266412370902665950977 2721949809278176999463233)
            ·
              refine ⟨2041462356958632749597425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2721949809278176999463233 2041462356958632749597425)
              ·
                refine ⟨1531096767718974562198069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2041462356958632749597425 1531096767718974562198069)
                ·
                  refine ⟨143540321973653865206069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1531096767718974562198069 143540321973653865206069)
                  ·
                    rfl

theorem cell23_2515894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 2, 2, 5].length) (baseStart_2515894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2515894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2515894 prefixEnd_2515894 := by exact prefixLift 2515894
  have htrace : WordTrace (prefixWord ++ tailWord_2515894) baseStart_2515894 baseEnd_2515894 := by
    simpa [prefixWord, tailWord_2515894, baseEnd_2515894] using wordTrace_append hprefix tailTrace_2515894
  have hstable : (prefixWord ++ tailWord_2515894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2515894).length < 2 ^ (prefixWord ++ tailWord_2515894).sum := by decide
  have hdescent : baseEnd_2515894 < baseStart_2515894 := by decide
  rcases family_descends (prefixWord ++ tailWord_2515894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2515929 : List Nat := [1, 2, 1, 2, 5, 1, 2, 1, 3, 5]
def baseStart_2515929 : Nat := 118140960795 + 2515929 * 2 ^ 59
def prefixEnd_2515929 : Nat := 4983230072969 + 3 ^ 40 * 2515929 * 2
def baseEnd_2515929 : Nat := 430626956528597383305653

theorem tailTrace_2515929 : CollatzResearch.WordTrace tailWord_2515929 prefixEnd_2515929 430626956528597383305653 := by
  unfold tailWord_2515929
  simp only [CollatzResearch.WordTrace]
  refine ⟨91763469302226394309222841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61175646201484262872815227 91763469302226394309222841)
  ·
    refine ⟨68822601976669795731917131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91763469302226394309222841 68822601976669795731917131)
    ·
      refine ⟨103233902965004693597875697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68822601976669795731917131 103233902965004693597875697)
      ·
        refine ⟨77425427223753520198406773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103233902965004693597875697 77425427223753520198406773)
        ·
          refine ⟨7258633802226892518600635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 77425427223753520198406773 7258633802226892518600635)
          ·
            refine ⟨10887950703340338777900953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7258633802226892518600635 10887950703340338777900953)
            ·
              refine ⟨8165963027505254083425715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10887950703340338777900953 8165963027505254083425715)
              ·
                refine ⟨12248944541257881125138573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8165963027505254083425715 12248944541257881125138573)
                ·
                  refine ⟨4593354202971705421926965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12248944541257881125138573 4593354202971705421926965)
                  ·
                    refine ⟨430626956528597383305653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4593354202971705421926965 430626956528597383305653)
                    ·
                      rfl

theorem cell23_2515929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 1, 3, 5].length) (baseStart_2515929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2515929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2515929 prefixEnd_2515929 := by exact prefixLift 2515929
  have htrace : WordTrace (prefixWord ++ tailWord_2515929) baseStart_2515929 baseEnd_2515929 := by
    simpa [prefixWord, tailWord_2515929, baseEnd_2515929] using wordTrace_append hprefix tailTrace_2515929
  have hstable : (prefixWord ++ tailWord_2515929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2515929).length < 2 ^ (prefixWord ++ tailWord_2515929).sum := by decide
  have hdescent : baseEnd_2515929 < baseStart_2515929 := by decide
  rcases family_descends (prefixWord ++ tailWord_2515929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2515946 : List Nat := [3, 1, 3, 1, 2, 3, 1, 3, 1, 5]
def baseStart_2515946 : Nat := 118140960795 + 2515946 * 2 ^ 59
def prefixEnd_2515946 : Nat := 4983230072969 + 3 ^ 40 * 2515946 * 2
def baseEnd_2515946 : Nat := 430629866252306194468127

theorem tailTrace_2515946 : CollatzResearch.WordTrace tailWord_2515946 prefixEnd_2515946 430629866252306194468127 := by
  unfold tailWord_2515946
  simp only [CollatzResearch.WordTrace]
  refine ⟨22941022335791201553147923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61176059562109870808394461 22941022335791201553147923)
  ·
    refine ⟨34411533503686802329721885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22941022335791201553147923 34411533503686802329721885)
    ·
      refine ⟨12904325063882550873645707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34411533503686802329721885 12904325063882550873645707)
      ·
        refine ⟨19356487595823826310468561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12904325063882550873645707 19356487595823826310468561)
        ·
          refine ⟨14517365696867869732851421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19356487595823826310468561 14517365696867869732851421)
          ·
            refine ⟨5444012136325451149819283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14517365696867869732851421 5444012136325451149819283)
            ·
              refine ⟨8166018204488176724728925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5444012136325451149819283 8166018204488176724728925)
              ·
                refine ⟨3062256826683066271773347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8166018204488176724728925 3062256826683066271773347)
                ·
                  refine ⟨4593385240024599407660021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3062256826683066271773347 4593385240024599407660021)
                  ·
                    refine ⟨430629866252306194468127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4593385240024599407660021 430629866252306194468127)
                    ·
                      rfl

theorem cell23_2515946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 3, 1, 5].length) (baseStart_2515946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2515946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2515946 prefixEnd_2515946 := by exact prefixLift 2515946
  have htrace : WordTrace (prefixWord ++ tailWord_2515946) baseStart_2515946 baseEnd_2515946 := by
    simpa [prefixWord, tailWord_2515946, baseEnd_2515946] using wordTrace_append hprefix tailTrace_2515946
  have hstable : (prefixWord ++ tailWord_2515946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2515946).length < 2 ^ (prefixWord ++ tailWord_2515946).sum := by decide
  have hdescent : baseEnd_2515946 < baseStart_2515946 := by decide
  rcases family_descends (prefixWord ++ tailWord_2515946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2515969 : List Nat := [1, 2, 4, 1, 2, 2, 1, 1, 3, 1, 5]
def baseStart_2515969 : Nat := 118140960795 + 2515969 * 2 ^ 59
def prefixEnd_2515969 : Nat := 4983230072969 + 3 ^ 40 * 2515969 * 2
def baseEnd_2515969 : Nat := 1291901408811971993416775

theorem tailTrace_2515969 : CollatzResearch.WordTrace tailWord_2515969 prefixEnd_2515969 1291901408811971993416775 := by
  unfold tailWord_2515969
  simp only [CollatzResearch.WordTrace]
  refine ⟨91764928222081481140678961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61176618814720987427119307 91764928222081481140678961)
  ·
    refine ⟨68823696166561110855509221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91764928222081481140678961 68823696166561110855509221)
    ·
      refine ⟨12904443031230208285407979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68823696166561110855509221 12904443031230208285407979)
      ·
        refine ⟨19356664546845312428111969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12904443031230208285407979 19356664546845312428111969)
        ·
          refine ⟨14517498410133984321083977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19356664546845312428111969 14517498410133984321083977)
          ·
            refine ⟨10888123807600488240812983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14517498410133984321083977 10888123807600488240812983)
            ·
              refine ⟨16332185711400732361219475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10888123807600488240812983 16332185711400732361219475)
              ·
                refine ⟨24498278567101098541829213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16332185711400732361219475 24498278567101098541829213)
                ·
                  refine ⟨9186854462662911953185955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24498278567101098541829213 9186854462662911953185955)
                  ·
                    refine ⟨13780281693994367929778933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9186854462662911953185955 13780281693994367929778933)
                    ·
                      refine ⟨1291901408811971993416775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13780281693994367929778933 1291901408811971993416775)
                      ·
                        rfl

theorem cell23_2515969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 1, 3, 1, 5].length) (baseStart_2515969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2515969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2515969 prefixEnd_2515969 := by exact prefixLift 2515969
  have htrace : WordTrace (prefixWord ++ tailWord_2515969) baseStart_2515969 baseEnd_2515969 := by
    simpa [prefixWord, tailWord_2515969, baseEnd_2515969] using wordTrace_append hprefix tailTrace_2515969
  have hstable : (prefixWord ++ tailWord_2515969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2515969).length < 2 ^ (prefixWord ++ tailWord_2515969).sum := by decide
  have hdescent : baseEnd_2515969 < baseStart_2515969 := by decide
  rcases family_descends (prefixWord ++ tailWord_2515969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2515976 : List Nat := [2, 1, 3, 2, 1, 5, 1, 1, 1, 6]
def baseStart_2515976 : Nat := 118140960795 + 2515976 * 2 ^ 59
def prefixEnd_2515976 : Nat := 4983230072969 + 3 ^ 40 * 2515976 * 2
def baseEnd_2515976 : Nat := 430635001058851155343081

theorem tailTrace_2515976 : CollatzResearch.WordTrace tailWord_2515976 prefixEnd_2515976 430635001058851155343081 := by
  unfold tailWord_2515976
  simp only [CollatzResearch.WordTrace]
  refine ⟨45882591766528060668091891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61176789022037414224122521 45882591766528060668091891)
  ·
    refine ⟨68823887649792091002137837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45882591766528060668091891 68823887649792091002137837)
    ·
      refine ⟨25808957868672034125801689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68823887649792091002137837 25808957868672034125801689)
      ·
        refine ⟨19356718401504025594351267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25808957868672034125801689 19356718401504025594351267)
        ·
          refine ⟨29035077602256038391526901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19356718401504025594351267 29035077602256038391526901)
          ·
            refine ⟨2722038525211503599205647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29035077602256038391526901 2722038525211503599205647)
            ·
              refine ⟨4083057787817255398808471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2722038525211503599205647 4083057787817255398808471)
              ·
                refine ⟨6124586681725883098212707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4083057787817255398808471 6124586681725883098212707)
                ·
                  refine ⟨9186880022588824647319061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6124586681725883098212707 9186880022588824647319061)
                  ·
                    refine ⟨430635001058851155343081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9186880022588824647319061 430635001058851155343081)
                    ·
                      rfl

theorem cell23_2515976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 1, 1, 1, 6].length) (baseStart_2515976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2515976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2515976 prefixEnd_2515976 := by exact prefixLift 2515976
  have htrace : WordTrace (prefixWord ++ tailWord_2515976) baseStart_2515976 baseEnd_2515976 := by
    simpa [prefixWord, tailWord_2515976, baseEnd_2515976] using wordTrace_append hprefix tailTrace_2515976
  have hstable : (prefixWord ++ tailWord_2515976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2515976).length < 2 ^ (prefixWord ++ tailWord_2515976).sum := by decide
  have hdescent : baseEnd_2515976 < baseStart_2515976 := by decide
  rcases family_descends (prefixWord ++ tailWord_2515976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2515979 : List Nat := [1, 1, 1, 1, 6, 3, 1, 1, 1, 1, 6]
def baseStart_2515979 : Nat := 118140960795 + 2515979 * 2 ^ 59
def prefixEnd_2515979 : Nat := 4983230072969 + 3 ^ 40 * 2515979 * 2
def baseEnd_2515979 : Nat := 1291906543618516954291729

theorem tailTrace_2515979 : CollatzResearch.WordTrace tailWord_2515979 prefixEnd_2515979 1291906543618516954291729 := by
  unfold tailWord_2515979
  simp only [CollatzResearch.WordTrace]
  refine ⟨91765292952045252848542991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61176861968030168565695327 91765292952045252848542991)
  ·
    refine ⟨137647939428067879272814487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91765292952045252848542991 137647939428067879272814487)
    ·
      refine ⟨206471909142101818909221731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137647939428067879272814487 206471909142101818909221731)
      ·
        refine ⟨309707863713152728363832597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206471909142101818909221731 309707863713152728363832597)
        ·
          refine ⟨14517556111554034142054653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 309707863713152728363832597 14517556111554034142054653)
          ·
            refine ⟨5444083541832762803270495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14517556111554034142054653 5444083541832762803270495)
            ·
              refine ⟨8166125312749144204905743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5444083541832762803270495 8166125312749144204905743)
              ·
                refine ⟨12249187969123716307358615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8166125312749144204905743 12249187969123716307358615)
                ·
                  refine ⟨18373781953685574461037923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12249187969123716307358615 18373781953685574461037923)
                  ·
                    refine ⟨27560672930528361691556885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18373781953685574461037923 27560672930528361691556885)
                    ·
                      refine ⟨1291906543618516954291729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27560672930528361691556885 1291906543618516954291729)
                      ·
                        rfl

theorem cell23_2515979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 1, 1, 1, 6].length) (baseStart_2515979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2515979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2515979 prefixEnd_2515979 := by exact prefixLift 2515979
  have htrace : WordTrace (prefixWord ++ tailWord_2515979) baseStart_2515979 baseEnd_2515979 := by
    simpa [prefixWord, tailWord_2515979, baseEnd_2515979] using wordTrace_append hprefix tailTrace_2515979
  have hstable : (prefixWord ++ tailWord_2515979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2515979).length < 2 ^ (prefixWord ++ tailWord_2515979).sum := by decide
  have hdescent : baseEnd_2515979 < baseStart_2515979 := by decide
  rcases family_descends (prefixWord ++ tailWord_2515979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2515989 : List Nat := [1, 3, 2, 1, 4, 2, 1, 9]
def baseStart_2515989 : Nat := 118140960795 + 2515989 * 2 ^ 59
def prefixEnd_2515989 : Nat := 4983230072969 + 3 ^ 40 * 2515989 * 2
def baseEnd_2515989 : Nat := 47848580682409700561729

theorem tailTrace_2515989 : CollatzResearch.WordTrace tailWord_2515989 prefixEnd_2515989 47848580682409700561729 := by
  unfold tailWord_2515989
  simp only [CollatzResearch.WordTrace]
  refine ⟨91765657682009024556407021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61177105121339349704271347 91765657682009024556407021)
  ·
    refine ⟨34412121630753384208652633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91765657682009024556407021 34412121630753384208652633)
    ·
      refine ⟨25809091223065038156489475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34412121630753384208652633 25809091223065038156489475)
      ·
        refine ⟨38713636834597557234734213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25809091223065038156489475 38713636834597557234734213)
        ·
          refine ⟨7258806906487041981512665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38713636834597557234734213 7258806906487041981512665)
          ·
            refine ⟨5444105179865281486134499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7258806906487041981512665 5444105179865281486134499)
            ·
              refine ⟨8166157769797922229201749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5444105179865281486134499 8166157769797922229201749)
              ·
                refine ⟨47848580682409700561729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8166157769797922229201749 47848580682409700561729)
                ·
                  rfl

theorem cell23_2515989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 9].length) (baseStart_2515989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2515989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2515989 prefixEnd_2515989 := by exact prefixLift 2515989
  have htrace : WordTrace (prefixWord ++ tailWord_2515989) baseStart_2515989 baseEnd_2515989 := by
    simpa [prefixWord, tailWord_2515989, baseEnd_2515989] using wordTrace_append hprefix tailTrace_2515989
  have hstable : (prefixWord ++ tailWord_2515989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2515989).length < 2 ^ (prefixWord ++ tailWord_2515989).sum := by decide
  have hdescent : baseEnd_2515989 < baseStart_2515989 := by decide
  rcases family_descends (prefixWord ++ tailWord_2515989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2516016 : List Nat := [2, 1, 1, 1, 2, 4, 1, 3, 4, 1, 3]
def baseStart_2516016 : Nat := 118140960795 + 2516016 * 2 ^ 59
def prefixEnd_2516016 : Nat := 4983230072969 + 3 ^ 40 * 2516016 * 2
def baseEnd_2516016 : Nat := 1291925542402733309529059

theorem tailTrace_2516016 : CollatzResearch.WordTrace tailWord_2516016 prefixEnd_2516016 1291925542402733309529059 := by
  unfold tailWord_2516016
  simp only [CollatzResearch.WordTrace]
  refine ⟨45883321226455604083819951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61177761635274138778426601 45883321226455604083819951)
  ·
    refine ⟨68824981839683406125729927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45883321226455604083819951 68824981839683406125729927)
    ·
      refine ⟨103237472759525109188594891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68824981839683406125729927 103237472759525109188594891)
      ·
        refine ⟨154856209139287663782892337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103237472759525109188594891 154856209139287663782892337)
        ·
          refine ⟨116142156854465747837169253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 154856209139287663782892337 116142156854465747837169253)
          ·
            refine ⟨21776654410212327719469235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 116142156854465747837169253 21776654410212327719469235)
            ·
              refine ⟨32664981615318491579203853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21776654410212327719469235 32664981615318491579203853)
              ·
                refine ⟨12249368105744434342201445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32664981615318491579203853 12249368105744434342201445)
                ·
                  refine ⟨2296756519827081439162771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12249368105744434342201445 2296756519827081439162771)
                  ·
                    refine ⟨3445134779740622158744157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2296756519827081439162771 3445134779740622158744157)
                    ·
                      refine ⟨1291925542402733309529059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3445134779740622158744157 1291925542402733309529059)
                      ·
                        rfl

theorem cell23_2516016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 3, 4, 1, 3].length) (baseStart_2516016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2516016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2516016 prefixEnd_2516016 := by exact prefixLift 2516016
  have htrace : WordTrace (prefixWord ++ tailWord_2516016) baseStart_2516016 baseEnd_2516016 := by
    simpa [prefixWord, tailWord_2516016, baseEnd_2516016] using wordTrace_append hprefix tailTrace_2516016
  have hstable : (prefixWord ++ tailWord_2516016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2516016).length < 2 ^ (prefixWord ++ tailWord_2516016).sum := by decide
  have hdescent : baseEnd_2516016 < baseStart_2516016 := by decide
  rcases family_descends (prefixWord ++ tailWord_2516016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2516017 : List Nat := [1, 2, 2, 3, 1, 2, 5, 2, 1, 2, 2]
def baseStart_2516017 : Nat := 118140960795 + 2516017 * 2 ^ 59
def prefixEnd_2516017 : Nat := 4983230072969 + 3 ^ 40 * 2516017 * 2
def baseEnd_2516017 : Nat := 1291926055883387805616555

theorem tailTrace_2516017 : CollatzResearch.WordTrace tailWord_2516017 prefixEnd_2516017 1291926055883387805616555 := by
  unfold tailWord_2516017
  simp only [CollatzResearch.WordTrace]
  refine ⟨91766678925907585338426305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61177785950605056892284203 91766678925907585338426305)
  ·
    refine ⟨68825009194430689003819729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91766678925907585338426305 68825009194430689003819729)
    ·
      refine ⟨51618756895823016752864797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68825009194430689003819729 51618756895823016752864797)
      ·
        refine ⟨19357033835933631282324299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51618756895823016752864797 19357033835933631282324299)
        ·
          refine ⟨29035550753900446923486449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19357033835933631282324299 29035550753900446923486449)
          ·
            refine ⟨21776663065425335192614837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29035550753900446923486449 21776663065425335192614837)
            ·
              refine ⟨2041562162383625174307641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21776663065425335192614837 2041562162383625174307641)
              ·
                refine ⟨1531171621787718880730731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2041562162383625174307641 1531171621787718880730731)
                ·
                  refine ⟨2296757432681578321096097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1531171621787718880730731 2296757432681578321096097)
                  ·
                    refine ⟨1722568074511183740822073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2296757432681578321096097 1722568074511183740822073)
                    ·
                      refine ⟨1291926055883387805616555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1722568074511183740822073 1291926055883387805616555)
                      ·
                        rfl

theorem cell23_2516017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 5, 2, 1, 2, 2].length) (baseStart_2516017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2516017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2516017 prefixEnd_2516017 := by exact prefixLift 2516017
  have htrace : WordTrace (prefixWord ++ tailWord_2516017) baseStart_2516017 baseEnd_2516017 := by
    simpa [prefixWord, tailWord_2516017, baseEnd_2516017] using wordTrace_append hprefix tailTrace_2516017
  have hstable : (prefixWord ++ tailWord_2516017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2516017).length < 2 ^ (prefixWord ++ tailWord_2516017).sum := by decide
  have hdescent : baseEnd_2516017 < baseStart_2516017 := by decide
  rcases family_descends (prefixWord ++ tailWord_2516017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2516054 : List Nat := [5, 2, 2, 1, 2, 1, 3, 1, 1, 2, 3]
def baseStart_2516054 : Nat := 118140960795 + 2516054 * 2 ^ 59
def prefixEnd_2516054 : Nat := 4983230072969 + 3 ^ 40 * 2516054 * 2
def baseEnd_2516054 : Nat := 1291945054667604160853885

theorem tailTrace_2516054 : CollatzResearch.WordTrace tailWord_2516054 prefixEnd_2516054 1291945054667604160853885 := by
  unfold tailWord_2516054
  simp only [CollatzResearch.WordTrace]
  refine ⟨5735501776673346291095201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 61178685617849027105015477 5735501776673346291095201)
  ·
    refine ⟨4301626332505009718321401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5735501776673346291095201 4301626332505009718321401)
    ·
      refine ⟨3226219749378757288741051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4301626332505009718321401 3226219749378757288741051)
      ·
        refine ⟨4839329624068135933111577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3226219749378757288741051 4839329624068135933111577)
        ·
          refine ⟨3629497218051101949833683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4839329624068135933111577 3629497218051101949833683)
          ·
            refine ⟨5444245827076652924750525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3629497218051101949833683 5444245827076652924750525)
            ·
              refine ⟨2041592185153744846781447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5444245827076652924750525 2041592185153744846781447)
              ·
                refine ⟨3062388277730617270172171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2041592185153744846781447 3062388277730617270172171)
                ·
                  refine ⟨4593582416595925905258257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3062388277730617270172171 4593582416595925905258257)
                  ·
                    refine ⟨3445186812446944428943693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4593582416595925905258257 3445186812446944428943693)
                    ·
                      refine ⟨1291945054667604160853885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3445186812446944428943693 1291945054667604160853885)
                      ·
                        rfl

theorem cell23_2516054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 3, 1, 1, 2, 3].length) (baseStart_2516054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2516054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2516054 prefixEnd_2516054 := by exact prefixLift 2516054
  have htrace : WordTrace (prefixWord ++ tailWord_2516054) baseStart_2516054 baseEnd_2516054 := by
    simpa [prefixWord, tailWord_2516054, baseEnd_2516054] using wordTrace_append hprefix tailTrace_2516054
  have hstable : (prefixWord ++ tailWord_2516054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2516054).length < 2 ^ (prefixWord ++ tailWord_2516054).sum := by decide
  have hdescent : baseEnd_2516054 < baseStart_2516054 := by decide
  rcases family_descends (prefixWord ++ tailWord_2516054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2516079 : List Nat := [1, 1, 2, 1, 3, 3, 2, 3, 7]
def baseStart_2516079 : Nat := 118140960795 + 2516079 * 2 ^ 59
def prefixEnd_2516079 : Nat := 4983230072969 + 3 ^ 40 * 2516079 * 2
def baseEnd_2516079 : Nat := 143550876853774062560141

theorem tailTrace_2516079 : CollatzResearch.WordTrace tailWord_2516079 prefixEnd_2516079 143550876853774062560141 := by
  unfold tailWord_2516079
  simp only [CollatzResearch.WordTrace]
  refine ⟨91768940251682969927183291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61179293501121979951455527 91768940251682969927183291)
  ·
    refine ⟨137653410377524454890774937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91768940251682969927183291 137653410377524454890774937)
    ·
      refine ⟨103240057783143341168081203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137653410377524454890774937 103240057783143341168081203)
      ·
        refine ⟨154860086674715011752121805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103240057783143341168081203 154860086674715011752121805)
        ·
          refine ⟨58072532503018129407045677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 154860086674715011752121805 58072532503018129407045677)
          ·
            refine ⟨21777199688631798527642129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58072532503018129407045677 21777199688631798527642129)
            ·
              refine ⟨16332899766473848895731597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21777199688631798527642129 16332899766473848895731597)
              ·
                refine ⟨6124837412427693335899349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16332899766473848895731597 6124837412427693335899349)
                ·
                  refine ⟨143550876853774062560141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6124837412427693335899349 143550876853774062560141)
                  ·
                    rfl

theorem cell23_2516079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 3, 7].length) (baseStart_2516079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2516079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2516079 prefixEnd_2516079 := by exact prefixLift 2516079
  have htrace : WordTrace (prefixWord ++ tailWord_2516079) baseStart_2516079 baseEnd_2516079 := by
    simpa [prefixWord, tailWord_2516079, baseEnd_2516079] using wordTrace_append hprefix tailTrace_2516079
  have hstable : (prefixWord ++ tailWord_2516079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2516079).length < 2 ^ (prefixWord ++ tailWord_2516079).sum := by decide
  have hdescent : baseEnd_2516079 < baseStart_2516079 := by decide
  rcases family_descends (prefixWord ++ tailWord_2516079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2516106 : List Nat := [3, 1, 2, 3, 1, 1, 1, 2, 1, 5, 3]
def baseStart_2516106 : Nat := 118140960795 + 2516106 * 2 ^ 59
def prefixEnd_2516106 : Nat := 4983230072969 + 3 ^ 40 * 2516106 * 2
def baseEnd_2516106 : Nat := 1291971755661637957403645

theorem tailTrace_2516106 : CollatzResearch.WordTrace tailWord_2516106 prefixEnd_2516106 1291971755661637957403645 := by
  unfold tailWord_2516106
  simp only [CollatzResearch.WordTrace]
  refine ⟨22942481255646288384604043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61179950015056769025610781 22942481255646288384604043)
  ·
    refine ⟨34413721883469432576906065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22942481255646288384604043 34413721883469432576906065)
    ·
      refine ⟨25810291412602074432679549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34413721883469432576906065 25810291412602074432679549)
      ·
        refine ⟨9678859279725777912254831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25810291412602074432679549 9678859279725777912254831)
        ·
          refine ⟨14518288919588666868382247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9678859279725777912254831 14518288919588666868382247)
          ·
            refine ⟨21777433379383000302573371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14518288919588666868382247 21777433379383000302573371)
            ·
              refine ⟨32666150069074500453860057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21777433379383000302573371 32666150069074500453860057)
              ·
                refine ⟨24499612551805875340395043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32666150069074500453860057 24499612551805875340395043)
                ·
                  refine ⟨36749418827708813010592565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24499612551805875340395043 36749418827708813010592565)
                  ·
                    refine ⟨3445258015097701219743053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36749418827708813010592565 3445258015097701219743053)
                    ·
                      refine ⟨1291971755661637957403645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3445258015097701219743053 1291971755661637957403645)
                      ·
                        rfl

theorem cell23_2516106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 2, 1, 5, 3].length) (baseStart_2516106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2516106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2516106 prefixEnd_2516106 := by exact prefixLift 2516106
  have htrace : WordTrace (prefixWord ++ tailWord_2516106) baseStart_2516106 baseEnd_2516106 := by
    simpa [prefixWord, tailWord_2516106, baseEnd_2516106] using wordTrace_append hprefix tailTrace_2516106
  have hstable : (prefixWord ++ tailWord_2516106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2516106).length < 2 ^ (prefixWord ++ tailWord_2516106).sum := by decide
  have hdescent : baseEnd_2516106 < baseStart_2516106 := by decide
  rcases family_descends (prefixWord ++ tailWord_2516106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2516146 : List Nat := [3, 2, 1, 1, 1, 4, 1, 2, 1, 3, 4]
def baseStart_2516146 : Nat := 118140960795 + 2516146 * 2 ^ 59
def prefixEnd_2516146 : Nat := 4983230072969 + 3 ^ 40 * 2516146 * 2
def baseEnd_2516146 : Nat := 1291992294887817800903461

theorem tailTrace_2516146 : CollatzResearch.WordTrace tailWord_2516146 prefixEnd_2516146 1291992294887817800903461 := by
  unfold tailWord_2516146
  simp only [CollatzResearch.WordTrace]
  refine ⟨22942845985610060092468073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61180922628293493579914861 22942845985610060092468073)
  ·
    refine ⟨17207134489207545069351055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22942845985610060092468073 17207134489207545069351055)
    ·
      refine ⟨25810701733811317604026583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17207134489207545069351055 25810701733811317604026583)
      ·
        refine ⟨38716052600716976406039875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25810701733811317604026583 38716052600716976406039875)
        ·
          refine ⟨58074078901075464609059813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38716052600716976406039875 58074078901075464609059813)
          ·
            refine ⟨10888889793951649614198715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58074078901075464609059813 10888889793951649614198715)
            ·
              refine ⟨16333334690927474421298073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10888889793951649614198715 16333334690927474421298073)
              ·
                refine ⟨12250001018195605815973555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16333334690927474421298073 12250001018195605815973555)
                ·
                  refine ⟨18375001527293408723960333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12250001018195605815973555 18375001527293408723960333)
                  ·
                    refine ⟨6890625572735028271485125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18375001527293408723960333 6890625572735028271485125)
                    ·
                      refine ⟨1291992294887817800903461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6890625572735028271485125 1291992294887817800903461)
                      ·
                        rfl

theorem cell23_2516146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 2, 1, 3, 4].length) (baseStart_2516146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2516146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2516146 prefixEnd_2516146 := by exact prefixLift 2516146
  have htrace : WordTrace (prefixWord ++ tailWord_2516146) baseStart_2516146 baseEnd_2516146 := by
    simpa [prefixWord, tailWord_2516146, baseEnd_2516146] using wordTrace_append hprefix tailTrace_2516146
  have hstable : (prefixWord ++ tailWord_2516146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2516146).length < 2 ^ (prefixWord ++ tailWord_2516146).sum := by decide
  have hdescent : baseEnd_2516146 < baseStart_2516146 := by decide
  rcases family_descends (prefixWord ++ tailWord_2516146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2516186 : List Nat := [3, 1, 1, 2, 2, 1, 1, 6, 6]
def baseStart_2516186 : Nat := 118140960795 + 2516186 * 2 ^ 59
def prefixEnd_2516186 : Nat := 4983230072969 + 3 ^ 40 * 2516186 * 2
def baseEnd_2516186 : Nat := 143556981568221960489253

theorem tailTrace_2516186 : CollatzResearch.WordTrace tailWord_2516186 prefixEnd_2516186 143556981568221960489253 := by
  unfold tailWord_2516186
  simp only [CollatzResearch.WordTrace]
  refine ⟨22943210715573831800332103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61181895241530218134218941 22943210715573831800332103)
  ·
    refine ⟨34414816073360747700498155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22943210715573831800332103 34414816073360747700498155)
    ·
      refine ⟨51622224110041121550747233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34414816073360747700498155 51622224110041121550747233)
      ·
        refine ⟨38716668082530841163060425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51622224110041121550747233 38716668082530841163060425)
        ·
          refine ⟨29037501061898130872295319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38716668082530841163060425 29037501061898130872295319)
          ·
            refine ⟨43556251592847196308442979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29037501061898130872295319 43556251592847196308442979)
            ·
              refine ⟨65334377389270794462664469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43556251592847196308442979 65334377389270794462664469)
              ·
                refine ⟨3062548940122068490437397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 65334377389270794462664469 3062548940122068490437397)
                ·
                  refine ⟨143556981568221960489253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3062548940122068490437397 143556981568221960489253)
                  ·
                    rfl

theorem cell23_2516186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 6, 6].length) (baseStart_2516186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2516186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2516186 prefixEnd_2516186 := by exact prefixLift 2516186
  have htrace : WordTrace (prefixWord ++ tailWord_2516186) baseStart_2516186 baseEnd_2516186 := by
    simpa [prefixWord, tailWord_2516186, baseEnd_2516186] using wordTrace_append hprefix tailTrace_2516186
  have hstable : (prefixWord ++ tailWord_2516186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2516186).length < 2 ^ (prefixWord ++ tailWord_2516186).sum := by decide
  have hdescent : baseEnd_2516186 < baseStart_2516186 := by decide
  rcases family_descends (prefixWord ++ tailWord_2516186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2516203 : List Nat := [1, 1, 1, 1, 2, 6, 4, 1, 6]
def baseStart_2516203 : Nat := 118140960795 + 2516203 * 2 ^ 59
def prefixEnd_2516203 : Nat := 4983230072969 + 3 ^ 40 * 2516203 * 2
def baseEnd_2516203 : Nat := 143557951476124897543411

theorem tailTrace_2516203 : CollatzResearch.WordTrace tailWord_2516203 prefixEnd_2516203 143557951476124897543411 := by
  unfold tailWord_2516203
  simp only [CollatzResearch.WordTrace]
  refine ⟨91773462903233739104697263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61182308602155826069798175 91773462903233739104697263)
  ·
    refine ⟨137660194354850608657045895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91773462903233739104697263 137660194354850608657045895)
    ·
      refine ⟨206490291532275912985568843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137660194354850608657045895 206490291532275912985568843)
      ·
        refine ⟨309735437298413869478353265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206490291532275912985568843 309735437298413869478353265)
        ·
          refine ⟨232301577973810402108764949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 309735437298413869478353265 232301577973810402108764949)
          ·
            refine ⟨10889136467522362598848357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 232301577973810402108764949 10889136467522362598848357)
            ·
              refine ⟨2041713087660442987284067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10889136467522362598848357 2041713087660442987284067)
              ·
                refine ⟨3062569631490664480926101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2041713087660442987284067 3062569631490664480926101)
                ·
                  refine ⟨143557951476124897543411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3062569631490664480926101 143557951476124897543411)
                  ·
                    rfl

theorem cell23_2516203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 4, 1, 6].length) (baseStart_2516203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2516203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2516203 prefixEnd_2516203 := by exact prefixLift 2516203
  have htrace : WordTrace (prefixWord ++ tailWord_2516203) baseStart_2516203 baseEnd_2516203 := by
    simpa [prefixWord, tailWord_2516203, baseEnd_2516203] using wordTrace_append hprefix tailTrace_2516203
  have hstable : (prefixWord ++ tailWord_2516203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2516203).length < 2 ^ (prefixWord ++ tailWord_2516203).sum := by decide
  have hdescent : baseEnd_2516203 < baseStart_2516203 := by decide
  rcases family_descends (prefixWord ++ tailWord_2516203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2516206 : List Nat := [4, 1, 2, 1, 1, 1, 2, 2, 1, 2, 6]
def baseStart_2516206 : Nat := 118140960795 + 2516206 * 2 ^ 59
def prefixEnd_2516206 : Nat := 4983230072969 + 3 ^ 40 * 2516206 * 2
def baseEnd_2516206 : Nat := 1292023103727087566153185

theorem tailTrace_2516206 : CollatzResearch.WordTrace tailWord_2516206 prefixEnd_2516206 1292023103727087566153185 := by
  unfold tailWord_2516206
  simp only [CollatzResearch.WordTrace]
  refine ⟨11471696540277858827132059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61182381548148580411370981 11471696540277858827132059)
  ·
    refine ⟨17207544810416788240698089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11471696540277858827132059 17207544810416788240698089)
    ·
      refine ⟨12905658607812591180523567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17207544810416788240698089 12905658607812591180523567)
      ·
        refine ⟨19358487911718886770785351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12905658607812591180523567 19358487911718886770785351)
        ·
          refine ⟨29037731867578330156178027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19358487911718886770785351 29037731867578330156178027)
          ·
            refine ⟨43556597801367495234267041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29037731867578330156178027 43556597801367495234267041)
            ·
              refine ⟨32667448351025621425700281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43556597801367495234267041 32667448351025621425700281)
              ·
                refine ⟨24500586263269216069275211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32667448351025621425700281 24500586263269216069275211)
                ·
                  refine ⟨36750879394903824103912817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24500586263269216069275211 36750879394903824103912817)
                  ·
                    refine ⟨27563159546177868077934613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36750879394903824103912817 27563159546177868077934613)
                    ·
                      refine ⟨1292023103727087566153185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27563159546177868077934613 1292023103727087566153185)
                      ·
                        rfl

theorem cell23_2516206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 2, 1, 2, 6].length) (baseStart_2516206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2516206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2516206 prefixEnd_2516206 := by exact prefixLift 2516206
  have htrace : WordTrace (prefixWord ++ tailWord_2516206) baseStart_2516206 baseEnd_2516206 := by
    simpa [prefixWord, tailWord_2516206, baseEnd_2516206] using wordTrace_append hprefix tailTrace_2516206
  have hstable : (prefixWord ++ tailWord_2516206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2516206).length < 2 ^ (prefixWord ++ tailWord_2516206).sum := by decide
  have hdescent : baseEnd_2516206 < baseStart_2516206 := by decide
  rcases family_descends (prefixWord ++ tailWord_2516206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2516247 : List Nat := [1, 1, 3, 4, 1, 1, 3, 4, 1, 1, 3]
def baseStart_2516247 : Nat := 118140960795 + 2516247 * 2 ^ 59
def prefixEnd_2516247 : Nat := 4983230072969 + 3 ^ 40 * 2516247 * 2
def baseEnd_2516247 : Nat := 1292044156433921905740497

theorem tailTrace_2516247 : CollatzResearch.WordTrace tailWord_2516247 prefixEnd_2516247 1292044156433921905740497 := by
  unfold tailWord_2516247
  simp only [CollatzResearch.WordTrace]
  refine ⟨91775067715074334619298995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61183378476716223079532663 91775067715074334619298995)
  ·
    refine ⟨137662601572611501928948493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91775067715074334619298995 137662601572611501928948493)
    ·
      refine ⟨51623475589729313223355685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137662601572611501928948493 51623475589729313223355685)
      ·
        refine ⟨9679401673074246229379191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51623475589729313223355685 9679401673074246229379191)
        ·
          refine ⟨14519102509611369344068787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9679401673074246229379191 14519102509611369344068787)
          ·
            refine ⟨21778653764417054016103181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14519102509611369344068787 21778653764417054016103181)
            ·
              refine ⟨8166995161656395256038693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21778653764417054016103181 8166995161656395256038693)
              ·
                refine ⟨1531311592810574110507255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8166995161656395256038693 1531311592810574110507255)
                ·
                  refine ⟨2296967389215861165760883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1531311592810574110507255 2296967389215861165760883)
                  ·
                    refine ⟨3445451083823791748641325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2296967389215861165760883 3445451083823791748641325)
                    ·
                      refine ⟨1292044156433921905740497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3445451083823791748641325 1292044156433921905740497)
                      ·
                        rfl

theorem cell23_2516247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 4, 1, 1, 3].length) (baseStart_2516247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2516247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2516247 prefixEnd_2516247 := by exact prefixLift 2516247
  have htrace : WordTrace (prefixWord ++ tailWord_2516247) baseStart_2516247 baseEnd_2516247 := by
    simpa [prefixWord, tailWord_2516247, baseEnd_2516247] using wordTrace_append hprefix tailTrace_2516247
  have hstable : (prefixWord ++ tailWord_2516247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2516247).length < 2 ^ (prefixWord ++ tailWord_2516247).sum := by decide
  have hdescent : baseEnd_2516247 < baseStart_2516247 := by decide
  rcases family_descends (prefixWord ++ tailWord_2516247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2516287 : List Nat := [1, 1, 2, 2, 4, 4, 2, 1, 1, 1, 4]
def baseStart_2516287 : Nat := 118140960795 + 2516287 * 2 ^ 59
def prefixEnd_2516287 : Nat := 4983230072969 + 3 ^ 40 * 2516287 * 2
def baseEnd_2516287 : Nat := 1292064695660101749240313

theorem tailTrace_2516287 : CollatzResearch.WordTrace tailWord_2516287 prefixEnd_2516287 1292064695660101749240313 := by
  unfold tailWord_2516287
  simp only [CollatzResearch.WordTrace]
  refine ⟨91776526634929421450755115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61184351089952947633836743 91776526634929421450755115)
  ·
    refine ⟨137664789952394132176132673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91776526634929421450755115 137664789952394132176132673)
    ·
      refine ⟨103248592464295599132099505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137664789952394132176132673 103248592464295599132099505)
      ·
        refine ⟨77436444348221699349074629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103248592464295599132099505 77436444348221699349074629)
        ·
          refine ⟨14519333315291568627951493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 77436444348221699349074629 14519333315291568627951493)
          ·
            refine ⟨2722374996617169117740905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14519333315291568627951493 2722374996617169117740905)
            ·
              refine ⟨2041781247462876838305679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2722374996617169117740905 2041781247462876838305679)
              ·
                refine ⟨3062671871194315257458519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2041781247462876838305679 3062671871194315257458519)
                ·
                  refine ⟨4594007806791472886187779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3062671871194315257458519 4594007806791472886187779)
                  ·
                    refine ⟨6891011710187209329281669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4594007806791472886187779 6891011710187209329281669)
                    ·
                      refine ⟨1292064695660101749240313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6891011710187209329281669 1292064695660101749240313)
                      ·
                        rfl

theorem cell23_2516287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 2, 1, 1, 1, 4].length) (baseStart_2516287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2516287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2516287 prefixEnd_2516287 := by exact prefixLift 2516287
  have htrace : WordTrace (prefixWord ++ tailWord_2516287) baseStart_2516287 baseEnd_2516287 := by
    simpa [prefixWord, tailWord_2516287, baseEnd_2516287] using wordTrace_append hprefix tailTrace_2516287
  have hstable : (prefixWord ++ tailWord_2516287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2516287).length < 2 ^ (prefixWord ++ tailWord_2516287).sum := by decide
  have hdescent : baseEnd_2516287 < baseStart_2516287 := by decide
  rcases family_descends (prefixWord ++ tailWord_2516287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2516296 : List Nat := [2, 1, 3, 1, 1, 2, 1, 2, 2, 2, 6]
def baseStart_2516296 : Nat := 118140960795 + 2516296 * 2 ^ 59
def prefixEnd_2516296 : Nat := 4983230072969 + 3 ^ 40 * 2516296 * 2
def baseEnd_2516296 : Nat := 1292069316985992214027771

theorem tailTrace_2516296 : CollatzResearch.WordTrace tailWord_2516296 prefixEnd_2516296 1292069316985992214027771 := by
  unfold tailWord_2516296
  simp only [CollatzResearch.WordTrace]
  refine ⟨45888427445948407993916371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61184569927931210658555161 45888427445948407993916371)
  ·
    refine ⟨68832641168922611990874557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45888427445948407993916371 68832641168922611990874557)
    ·
      refine ⟨25812240438345979496577959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68832641168922611990874557 25812240438345979496577959)
      ·
        refine ⟨38718360657518969244866939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25812240438345979496577959 38718360657518969244866939)
        ·
          refine ⟨58077540986278453867300409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38718360657518969244866939 58077540986278453867300409)
          ·
            refine ⟨43558155739708840400475307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58077540986278453867300409 43558155739708840400475307)
            ·
              refine ⟨65337233609563260600712961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43558155739708840400475307 65337233609563260600712961)
              ·
                refine ⟨49002925207172445450534721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65337233609563260600712961 49002925207172445450534721)
                ·
                  refine ⟨36752193905379334087901041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49002925207172445450534721 36752193905379334087901041)
                  ·
                    refine ⟨27564145429034500565925781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36752193905379334087901041 27564145429034500565925781)
                    ·
                      refine ⟨1292069316985992214027771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27564145429034500565925781 1292069316985992214027771)
                      ·
                        rfl

theorem cell23_2516296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 2, 2, 2, 6].length) (baseStart_2516296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2516296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2516296 prefixEnd_2516296 := by exact prefixLift 2516296
  have htrace : WordTrace (prefixWord ++ tailWord_2516296) baseStart_2516296 baseEnd_2516296 := by
    simpa [prefixWord, tailWord_2516296, baseEnd_2516296] using wordTrace_append hprefix tailTrace_2516296
  have hstable : (prefixWord ++ tailWord_2516296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2516296).length < 2 ^ (prefixWord ++ tailWord_2516296).sum := by decide
  have hdescent : baseEnd_2516296 < baseStart_2516296 := by decide
  rcases family_descends (prefixWord ++ tailWord_2516296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2516320 : List Nat := [2, 1, 1, 3, 4, 1, 3, 1, 1, 3, 3]
def baseStart_2516320 : Nat := 118140960795 + 2516320 * 2 ^ 59
def prefixEnd_2516320 : Nat := 4983230072969 + 3 ^ 40 * 2516320 * 2
def baseEnd_2516320 : Nat := 1292081640521700120127661

theorem tailTrace_2516320 : CollatzResearch.WordTrace tailWord_2516320 prefixEnd_2516320 1292081640521700120127661 := by
  unfold tailWord_2516320
  simp only [CollatzResearch.WordTrace]
  refine ⟨45888865121904934043353207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61185153495873245391137609 45888865121904934043353207)
  ·
    refine ⟨68833297682857401065029811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45888865121904934043353207 68833297682857401065029811)
    ·
      refine ⟨103249946524286101597544717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68833297682857401065029811 103249946524286101597544717)
      ·
        refine ⟨38718729946607288099079269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103249946524286101597544717 38718729946607288099079269)
        ·
          refine ⟨7259761864988866518577363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38718729946607288099079269 7259761864988866518577363)
          ·
            refine ⟨10889642797483299777866045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7259761864988866518577363 10889642797483299777866045)
            ·
              refine ⟨4083616049056237416699767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10889642797483299777866045 4083616049056237416699767)
              ·
                refine ⟨6125424073584356125049651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4083616049056237416699767 6125424073584356125049651)
                ·
                  refine ⟨9188136110376534187574477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6125424073584356125049651 9188136110376534187574477)
                  ·
                    refine ⟨3445551041391200320340429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9188136110376534187574477 3445551041391200320340429)
                    ·
                      refine ⟨1292081640521700120127661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3445551041391200320340429 1292081640521700120127661)
                      ·
                        rfl

theorem cell23_2516320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 3, 1, 1, 3, 3].length) (baseStart_2516320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2516320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2516320 prefixEnd_2516320 := by exact prefixLift 2516320
  have htrace : WordTrace (prefixWord ++ tailWord_2516320) baseStart_2516320 baseEnd_2516320 := by
    simpa [prefixWord, tailWord_2516320, baseEnd_2516320] using wordTrace_append hprefix tailTrace_2516320
  have hstable : (prefixWord ++ tailWord_2516320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2516320).length < 2 ^ (prefixWord ++ tailWord_2516320).sum := by decide
  have hdescent : baseEnd_2516320 < baseStart_2516320 := by decide
  rcases family_descends (prefixWord ++ tailWord_2516320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2516327 : List Nat := [1, 1, 5, 1, 5, 1, 2, 7]
def baseStart_2516327 : Nat := 118140960795 + 2516327 * 2 ^ 59
def prefixEnd_2516327 : Nat := 4983230072969 + 3 ^ 40 * 2516327 * 2
def baseEnd_2516327 : Nat := 47855008699491910842227

theorem tailTrace_2516327 : CollatzResearch.WordTrace tailWord_2516327 prefixEnd_2516327 47855008699491910842227 := by
  unfold tailWord_2516327
  simp only [CollatzResearch.WordTrace]
  refine ⟨91777985554784508282211235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61185323703189672188140823 91777985554784508282211235)
  ·
    refine ⟨137666978332176762423316853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91777985554784508282211235 137666978332176762423316853)
    ·
      refine ⟨12906279218641571477185955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 137666978332176762423316853 12906279218641571477185955)
      ·
        refine ⟨19359418827962357215778933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12906279218641571477185955 19359418827962357215778933)
        ·
          refine ⟨1814945515121470988979275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19359418827962357215778933 1814945515121470988979275)
          ·
            refine ⟨2722418272682206483468913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1814945515121470988979275 2722418272682206483468913)
            ·
              refine ⟨2041813704511654862601685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2722418272682206483468913 2041813704511654862601685)
              ·
                refine ⟨47855008699491910842227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2041813704511654862601685 47855008699491910842227)
                ·
                  rfl

theorem cell23_2516327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 2, 7].length) (baseStart_2516327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2516327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2516327 prefixEnd_2516327 := by exact prefixLift 2516327
  have htrace : WordTrace (prefixWord ++ tailWord_2516327) baseStart_2516327 baseEnd_2516327 := by
    simpa [prefixWord, tailWord_2516327, baseEnd_2516327] using wordTrace_append hprefix tailTrace_2516327
  have hstable : (prefixWord ++ tailWord_2516327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2516327).length < 2 ^ (prefixWord ++ tailWord_2516327).sum := by decide
  have hdescent : baseEnd_2516327 < baseStart_2516327 := by decide
  rcases family_descends (prefixWord ++ tailWord_2516327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2516333 : List Nat := [1, 5, 1, 1, 1, 3, 1, 1, 2, 2, 5]
def baseStart_2516333 : Nat := 118140960795 + 2516333 * 2 ^ 59
def prefixEnd_2516333 : Nat := 4983230072969 + 3 ^ 40 * 2516333 * 2
def baseEnd_2516333 : Nat := 1292088315770208569265101

theorem tailTrace_2516333 : CollatzResearch.WordTrace tailWord_2516333 prefixEnd_2516333 1292088315770208569265101 := by
  unfold tailWord_2516333
  simp only [CollatzResearch.WordTrace]
  refine ⟨91778204392762771306929653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61185469595175180871286435 91778204392762771306929653)
  ·
    refine ⟨8604206661821509810024655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 91778204392762771306929653 8604206661821509810024655)
    ·
      refine ⟨12906309992732264715036983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8604206661821509810024655 12906309992732264715036983)
      ·
        refine ⟨19359464989098397072555475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12906309992732264715036983 19359464989098397072555475)
        ·
          refine ⟨29039197483647595608833213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19359464989098397072555475 29039197483647595608833213)
          ·
            refine ⟨10889699056367848353312455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29039197483647595608833213 10889699056367848353312455)
            ·
              refine ⟨16334548584551772529968683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10889699056367848353312455 16334548584551772529968683)
              ·
                refine ⟨24501822876827658794953025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16334548584551772529968683 24501822876827658794953025)
                ·
                  refine ⟨18376367157620744096214769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24501822876827658794953025 18376367157620744096214769)
                  ·
                    refine ⟨13782275368215558072161077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18376367157620744096214769 13782275368215558072161077)
                    ·
                      refine ⟨1292088315770208569265101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13782275368215558072161077 1292088315770208569265101)
                      ·
                        rfl

theorem cell23_2516333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 1, 2, 2, 5].length) (baseStart_2516333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2516333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2516333 prefixEnd_2516333 := by exact prefixLift 2516333
  have htrace : WordTrace (prefixWord ++ tailWord_2516333) baseStart_2516333 baseEnd_2516333 := by
    simpa [prefixWord, tailWord_2516333, baseEnd_2516333] using wordTrace_append hprefix tailTrace_2516333
  have hstable : (prefixWord ++ tailWord_2516333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2516333).length < 2 ^ (prefixWord ++ tailWord_2516333).sum := by decide
  have hdescent : baseEnd_2516333 < baseStart_2516333 := by decide
  rcases family_descends (prefixWord ++ tailWord_2516333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2516354 : List Nat := [3, 4, 2, 1, 1, 1, 2, 1, 4, 1, 3]
def baseStart_2516354 : Nat := 118140960795 + 2516354 * 2 ^ 59
def prefixEnd_2516354 : Nat := 4983230072969 + 3 ^ 40 * 2516354 * 2
def baseEnd_2516354 : Nat := 1292099098863952987102505

theorem tailTrace_2516354 : CollatzResearch.WordTrace tailWord_2516354 prefixEnd_2516354 1292099098863952987102505 := by
  unfold tailWord_2516354
  simp only [CollatzResearch.WordTrace]
  refine ⟨22944742581421672973361029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61185980217124461262296077 22944742581421672973361029)
  ·
    refine ⟨4302139234016563682505193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22944742581421672973361029 4302139234016563682505193)
    ·
      refine ⟨3226604425512422761878895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4302139234016563682505193 3226604425512422761878895)
      ·
        refine ⟨4839906638268634142818343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3226604425512422761878895 4839906638268634142818343)
        ·
          refine ⟨7259859957402951214227515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4839906638268634142818343 7259859957402951214227515)
          ·
            refine ⟨10889789936104426821341273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7259859957402951214227515 10889789936104426821341273)
            ·
              refine ⟨8167342452078320116005955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10889789936104426821341273 8167342452078320116005955)
              ·
                refine ⟨12251013678117480174008933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8167342452078320116005955 12251013678117480174008933)
                ·
                  refine ⟨2297065064647027532626675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12251013678117480174008933 2297065064647027532626675)
                  ·
                    refine ⟨3445597596970541298940013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2297065064647027532626675 3445597596970541298940013)
                    ·
                      refine ⟨1292099098863952987102505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3445597596970541298940013 1292099098863952987102505)
                      ·
                        rfl

theorem cell23_2516354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_2516354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2516354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2516354 prefixEnd_2516354 := by exact prefixLift 2516354
  have htrace : WordTrace (prefixWord ++ tailWord_2516354) baseStart_2516354 baseEnd_2516354 := by
    simpa [prefixWord, tailWord_2516354, baseEnd_2516354] using wordTrace_append hprefix tailTrace_2516354
  have hstable : (prefixWord ++ tailWord_2516354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2516354).length < 2 ^ (prefixWord ++ tailWord_2516354).sum := by decide
  have hdescent : baseEnd_2516354 < baseStart_2516354 := by decide
  rcases family_descends (prefixWord ++ tailWord_2516354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2516363 : List Nat := [1, 1, 1, 1, 4, 3, 2, 1, 2, 4, 3]
def baseStart_2516363 : Nat := 118140960795 + 2516363 * 2 ^ 59
def prefixEnd_2516363 : Nat := 4983230072969 + 3 ^ 40 * 2516363 * 2
def baseEnd_2516363 : Nat := 1292103720189843451889963

theorem tailTrace_2516363 : CollatzResearch.WordTrace tailWord_2516363 prefixEnd_2516363 1292103720189843451889963 := by
  unfold tailWord_2516363
  simp only [CollatzResearch.WordTrace]
  refine ⟨91779298582654086430521743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61186199055102724287014495 91779298582654086430521743)
  ·
    refine ⟨137668947873981129645782615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91779298582654086430521743 137668947873981129645782615)
    ·
      refine ⟨206503421810971694468673923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137668947873981129645782615 206503421810971694468673923)
      ·
        refine ⟨309755132716457541703010885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206503421810971694468673923 309755132716457541703010885)
        ·
          refine ⟨58079087384335789069314541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 309755132716457541703010885 58079087384335789069314541)
          ·
            refine ⟨21779657769125920900992953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58079087384335789069314541 21779657769125920900992953)
            ·
              refine ⟨16334743326844440675744715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21779657769125920900992953 16334743326844440675744715)
              ·
                refine ⟨24502114990266661013617073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16334743326844440675744715 24502114990266661013617073)
                ·
                  refine ⟨18376586242699995760212805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24502114990266661013617073 18376586242699995760212805)
                  ·
                    refine ⟨3445609920506249205039901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18376586242699995760212805 3445609920506249205039901)
                    ·
                      refine ⟨1292103720189843451889963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3445609920506249205039901 1292103720189843451889963)
                      ·
                        rfl

theorem cell23_2516363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 1, 2, 4, 3].length) (baseStart_2516363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2516363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2516363 prefixEnd_2516363 := by exact prefixLift 2516363
  have htrace : WordTrace (prefixWord ++ tailWord_2516363) baseStart_2516363 baseEnd_2516363 := by
    simpa [prefixWord, tailWord_2516363, baseEnd_2516363] using wordTrace_append hprefix tailTrace_2516363
  have hstable : (prefixWord ++ tailWord_2516363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2516363).length < 2 ^ (prefixWord ++ tailWord_2516363).sum := by decide
  have hdescent : baseEnd_2516363 < baseStart_2516363 := by decide
  rcases family_descends (prefixWord ++ tailWord_2516363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2516373 : List Nat := [1, 3, 2, 1, 1, 2, 2, 3, 2, 2, 4]
def baseStart_2516373 : Nat := 118140960795 + 2516373 * 2 ^ 59
def prefixEnd_2516373 : Nat := 4983230072969 + 3 ^ 40 * 2516373 * 2
def baseEnd_2516373 : Nat := 1292108854996388412764917

theorem tailTrace_2516373 : CollatzResearch.WordTrace tailWord_2516373 prefixEnd_2516373 1292108854996388412764917 := by
  unfold tailWord_2516373
  simp only [CollatzResearch.WordTrace]
  refine ⟨91779663312617858138385773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61186442208411905425590515 91779663312617858138385773)
  ·
    refine ⟨34417373742231696801894665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91779663312617858138385773 34417373742231696801894665)
    ·
      refine ⟨25813030306673772601420999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34417373742231696801894665 25813030306673772601420999)
      ·
        refine ⟨38719545460010658902131499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25813030306673772601420999 38719545460010658902131499)
        ·
          refine ⟨58079318190015988353197249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38719545460010658902131499 58079318190015988353197249)
          ·
            refine ⟨43559488642511991264897937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58079318190015988353197249 43559488642511991264897937)
            ·
              refine ⟨32669616481883993448673453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43559488642511991264897937 32669616481883993448673453)
              ·
                refine ⟨12251106180706497543252545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32669616481883993448673453 12251106180706497543252545)
                ·
                  refine ⟨9188329635529873157439409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12251106180706497543252545 9188329635529873157439409)
                  ·
                    refine ⟨6891247226647404868079557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9188329635529873157439409 6891247226647404868079557)
                    ·
                      refine ⟨1292108854996388412764917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6891247226647404868079557 1292108854996388412764917)
                      ·
                        rfl

theorem cell23_2516373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 3, 2, 2, 4].length) (baseStart_2516373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2516373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2516373 prefixEnd_2516373 := by exact prefixLift 2516373
  have htrace : WordTrace (prefixWord ++ tailWord_2516373) baseStart_2516373 baseEnd_2516373 := by
    simpa [prefixWord, tailWord_2516373, baseEnd_2516373] using wordTrace_append hprefix tailTrace_2516373
  have hstable : (prefixWord ++ tailWord_2516373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2516373).length < 2 ^ (prefixWord ++ tailWord_2516373).sum := by decide
  have hdescent : baseEnd_2516373 < baseStart_2516373 := by decide
  rcases family_descends (prefixWord ++ tailWord_2516373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2516393 : List Nat := [1, 2, 1, 1, 1, 1, 3, 1, 6, 3, 3]
def baseStart_2516393 : Nat := 118140960795 + 2516393 * 2 ^ 59
def prefixEnd_2516393 : Nat := 4983230072969 + 3 ^ 40 * 2516393 * 2
def baseEnd_2516393 : Nat := 1292119124609478334514825

theorem tailTrace_2516393 : CollatzResearch.WordTrace tailWord_2516393 prefixEnd_2516393 1292119124609478334514825 := by
  unfold tailWord_2516393
  simp only [CollatzResearch.WordTrace]
  refine ⟨91780392772545401554113833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61186928515030267702742555 91780392772545401554113833)
  ·
    refine ⟨68835294579409051165585375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91780392772545401554113833 68835294579409051165585375)
    ·
      refine ⟨103252941869113576748378063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68835294579409051165585375 103252941869113576748378063)
      ·
        refine ⟨154879412803670365122567095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103252941869113576748378063 154879412803670365122567095)
        ·
          refine ⟨232319119205505547683850643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154879412803670365122567095 232319119205505547683850643)
          ·
            refine ⟨348478678808258321525775965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 232319119205505547683850643 348478678808258321525775965)
            ·
              refine ⟨130679504553096870572165987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 348478678808258321525775965 130679504553096870572165987)
              ·
                refine ⟨196019256829645305858248981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 130679504553096870572165987 196019256829645305858248981)
                ·
                  refine ⟨9188402663889623712105421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 196019256829645305858248981 9188402663889623712105421)
                  ·
                    refine ⟨3445650998958608892039533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9188402663889623712105421 3445650998958608892039533)
                    ·
                      refine ⟨1292119124609478334514825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3445650998958608892039533 1292119124609478334514825)
                      ·
                        rfl

theorem cell23_2516393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 6, 3, 3].length) (baseStart_2516393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2516393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2516393 prefixEnd_2516393 := by exact prefixLift 2516393
  have htrace : WordTrace (prefixWord ++ tailWord_2516393) baseStart_2516393 baseEnd_2516393 := by
    simpa [prefixWord, tailWord_2516393, baseEnd_2516393] using wordTrace_append hprefix tailTrace_2516393
  have hstable : (prefixWord ++ tailWord_2516393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2516393).length < 2 ^ (prefixWord ++ tailWord_2516393).sum := by decide
  have hdescent : baseEnd_2516393 < baseStart_2516393 := by decide
  rcases family_descends (prefixWord ++ tailWord_2516393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2516423 : List Nat := [1, 1, 4, 1, 1, 3, 1, 3, 1, 2, 5]
def baseStart_2516423 : Nat := 118140960795 + 2516423 * 2 ^ 59
def prefixEnd_2516423 : Nat := 4983230072969 + 3 ^ 40 * 2516423 * 2
def baseEnd_2516423 : Nat := 1292134529029113217139687

theorem tailTrace_2516423 : CollatzResearch.WordTrace tailWord_2516423 prefixEnd_2516423 1292134529029113217139687 := by
  unfold tailWord_2516423
  simp only [CollatzResearch.WordTrace]
  refine ⟨91781486962436716677705923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61187657974957811118470615 91781486962436716677705923)
  ·
    refine ⟨137672230443655075016558885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91781486962436716677705923 137672230443655075016558885)
    ·
      refine ⟨25813543208185326565604791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 137672230443655075016558885 25813543208185326565604791)
      ·
        refine ⟨38720314812277989848407187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25813543208185326565604791 38720314812277989848407187)
        ·
          refine ⟨58080472218416984772610781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38720314812277989848407187 58080472218416984772610781)
          ·
            refine ⟨21780177081906369289729043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58080472218416984772610781 21780177081906369289729043)
            ·
              refine ⟨32670265622859553934593565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21780177081906369289729043 32670265622859553934593565)
              ·
                refine ⟨12251349608572332725472587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32670265622859553934593565 12251349608572332725472587)
                ·
                  refine ⟨18377024412858499088208881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12251349608572332725472587 18377024412858499088208881)
                  ·
                    refine ⟨13782768309643874316156661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18377024412858499088208881 13782768309643874316156661)
                    ·
                      refine ⟨1292134529029113217139687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13782768309643874316156661 1292134529029113217139687)
                      ·
                        rfl

theorem cell23_2516423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 3, 1, 2, 5].length) (baseStart_2516423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2516423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2516423 prefixEnd_2516423 := by exact prefixLift 2516423
  have htrace : WordTrace (prefixWord ++ tailWord_2516423) baseStart_2516423 baseEnd_2516423 := by
    simpa [prefixWord, tailWord_2516423, baseEnd_2516423] using wordTrace_append hprefix tailTrace_2516423
  have hstable : (prefixWord ++ tailWord_2516423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2516423).length < 2 ^ (prefixWord ++ tailWord_2516423).sum := by decide
  have hdescent : baseEnd_2516423 < baseStart_2516423 := by decide
  rcases family_descends (prefixWord ++ tailWord_2516423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2516463 : List Nat := [1, 1, 2, 1, 4, 1, 3, 1, 2, 1, 6]
def baseStart_2516463 : Nat := 118140960795 + 2516463 * 2 ^ 59
def prefixEnd_2516463 : Nat := 4983230072969 + 3 ^ 40 * 2516463 * 2
def baseEnd_2516463 : Nat := 1292155068255293060639503

theorem tailTrace_2516463 : CollatzResearch.WordTrace tailWord_2516463 prefixEnd_2516463 1292155068255293060639503 := by
  unfold tailWord_2516463
  simp only [CollatzResearch.WordTrace]
  refine ⟨91782945882291803509162043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61188630588194535672774695 91782945882291803509162043)
  ·
    refine ⟨137674418823437705263743065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91782945882291803509162043 137674418823437705263743065)
    ·
      refine ⟨103255814117578278947807299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137674418823437705263743065 103255814117578278947807299)
      ·
        refine ⟨154883721176367418421710949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103255814117578278947807299 154883721176367418421710949)
        ·
          refine ⟨29040697720568890954070803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 154883721176367418421710949 29040697720568890954070803)
          ·
            refine ⟨43561046580853336431106205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29040697720568890954070803 43561046580853336431106205)
            ·
              refine ⟨16335392467820001161664827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43561046580853336431106205 16335392467820001161664827)
              ·
                refine ⟨24503088701730001742497241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16335392467820001161664827 24503088701730001742497241)
                ·
                  refine ⟨18377316526297501306872931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24503088701730001742497241 18377316526297501306872931)
                  ·
                    refine ⟨27565974789446251960309397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18377316526297501306872931 27565974789446251960309397)
                    ·
                      refine ⟨1292155068255293060639503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27565974789446251960309397 1292155068255293060639503)
                      ·
                        rfl

theorem cell23_2516463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 1, 2, 1, 6].length) (baseStart_2516463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2516463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2516463 prefixEnd_2516463 := by exact prefixLift 2516463
  have htrace : WordTrace (prefixWord ++ tailWord_2516463) baseStart_2516463 baseEnd_2516463 := by
    simpa [prefixWord, tailWord_2516463, baseEnd_2516463] using wordTrace_append hprefix tailTrace_2516463
  have hstable : (prefixWord ++ tailWord_2516463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2516463).length < 2 ^ (prefixWord ++ tailWord_2516463).sum := by decide
  have hdescent : baseEnd_2516463 < baseStart_2516463 := by decide
  rcases family_descends (prefixWord ++ tailWord_2516463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2516477 : List Nat := [1, 4, 1, 1, 1, 5, 2, 1, 3, 4]
def baseStart_2516477 : Nat := 118140960795 + 2516477 * 2 ^ 59
def prefixEnd_2516477 : Nat := 4983230072969 + 3 ^ 40 * 2516477 * 2
def baseEnd_2516477 : Nat := 430720752328152001954813

theorem tailTrace_2516477 : CollatzResearch.WordTrace tailWord_2516477 prefixEnd_2516477 430720752328152001954813 := by
  unfold tailWord_2516477
  simp only [CollatzResearch.WordTrace]
  refine ⟨91783456504241083900171685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61188971002827389266781123 91783456504241083900171685)
  ·
    refine ⟨17209398094545203231282191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 91783456504241083900171685 17209398094545203231282191)
    ·
      refine ⟨25814097141817804846923287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17209398094545203231282191 25814097141817804846923287)
      ·
        refine ⟨38721145712726707270384931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25814097141817804846923287 38721145712726707270384931)
        ·
          refine ⟨58081718569090060905577397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38721145712726707270384931 58081718569090060905577397)
          ·
            refine ⟨5445161115852193209897881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 58081718569090060905577397 5445161115852193209897881)
            ·
              refine ⟨4083870836889144907423411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5445161115852193209897881 4083870836889144907423411)
              ·
                refine ⟨6125806255333717361135117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4083870836889144907423411 6125806255333717361135117)
                ·
                  refine ⟨2297177345750144010425669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6125806255333717361135117 2297177345750144010425669)
                  ·
                    refine ⟨430720752328152001954813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2297177345750144010425669 430720752328152001954813)
                    ·
                      rfl

theorem cell23_2516477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 2, 1, 3, 4].length) (baseStart_2516477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2516477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2516477 prefixEnd_2516477 := by exact prefixLift 2516477
  have htrace : WordTrace (prefixWord ++ tailWord_2516477) baseStart_2516477 baseEnd_2516477 := by
    simpa [prefixWord, tailWord_2516477, baseEnd_2516477] using wordTrace_append hprefix tailTrace_2516477
  have hstable : (prefixWord ++ tailWord_2516477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2516477).length < 2 ^ (prefixWord ++ tailWord_2516477).sum := by decide
  have hdescent : baseEnd_2516477 < baseStart_2516477 := by decide
  rcases family_descends (prefixWord ++ tailWord_2516477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2516541 : List Nat := [1, 4, 1, 3, 4, 1, 2, 1, 6]
def baseStart_2516541 : Nat := 118140960795 + 2516541 * 2 ^ 59
def prefixEnd_2516541 : Nat := 4983230072969 + 3 ^ 40 * 2516541 * 2
def baseEnd_2516541 : Nat := 143577235527371528384905

theorem tailTrace_2516541 : CollatzResearch.WordTrace tailWord_2516541 prefixEnd_2516541 143577235527371528384905 := by
  unfold tailWord_2516541
  simp only [CollatzResearch.WordTrace]
  refine ⟨91785790776009222830501477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61190527184006148553667651 91785790776009222830501477)
  ·
    refine ⟨17209835770501729280719027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 91785790776009222830501477 17209835770501729280719027)
    ·
      refine ⟨25814753655752593921078541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17209835770501729280719027 25814753655752593921078541)
      ·
        refine ⟨9680532620907222720404453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25814753655752593921078541 9680532620907222720404453)
        ·
          refine ⟨1815099866420104260075835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9680532620907222720404453 1815099866420104260075835)
          ·
            refine ⟨2722649799630156390113753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1815099866420104260075835 2722649799630156390113753)
            ·
              refine ⟨2041987349722617292585315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2722649799630156390113753 2041987349722617292585315)
              ·
                refine ⟨3062981024583925938877973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2041987349722617292585315 3062981024583925938877973)
                ·
                  refine ⟨143577235527371528384905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3062981024583925938877973 143577235527371528384905)
                  ·
                    rfl

theorem cell23_2516541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 2, 1, 6].length) (baseStart_2516541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2516541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2516541 prefixEnd_2516541 := by exact prefixLift 2516541
  have htrace : WordTrace (prefixWord ++ tailWord_2516541) baseStart_2516541 baseEnd_2516541 := by
    simpa [prefixWord, tailWord_2516541, baseEnd_2516541] using wordTrace_append hprefix tailTrace_2516541
  have hstable : (prefixWord ++ tailWord_2516541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2516541).length < 2 ^ (prefixWord ++ tailWord_2516541).sum := by decide
  have hdescent : baseEnd_2516541 < baseStart_2516541 := by decide
  rcases family_descends (prefixWord ++ tailWord_2516541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2516584 : List Nat := [2, 1, 4, 3, 1, 1, 1, 4, 2, 4]
def baseStart_2516584 : Nat := 118140960795 + 2516584 * 2 ^ 59
def prefixEnd_2516584 : Nat := 4983230072969 + 3 ^ 40 * 2516584 * 2
def baseEnd_2516584 : Nat := 430739066471495695742149

theorem tailTrace_2516584 : CollatzResearch.WordTrace tailWord_2516584 prefixEnd_2516584 430739066471495695742149 := by
  unfold tailWord_2516584
  simp only [CollatzResearch.WordTrace]
  refine ⟨45893679557426720587158403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61191572743235627449544537 45893679557426720587158403)
  ·
    refine ⟨68840519336140080880737605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45893679557426720587158403 68840519336140080880737605)
    ·
      refine ⟨12907597375526265165138301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68840519336140080880737605 12907597375526265165138301)
      ·
        refine ⟨4840349015822349436926863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12907597375526265165138301 4840349015822349436926863)
        ·
          refine ⟨7260523523733524155390295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4840349015822349436926863 7260523523733524155390295)
          ·
            refine ⟨10890785285600286233085443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7260523523733524155390295 10890785285600286233085443)
            ·
              refine ⟨16336177928400429349628165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10890785285600286233085443 16336177928400429349628165)
              ·
                refine ⟨3063033361575080503055281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16336177928400429349628165 3063033361575080503055281)
                ·
                  refine ⟨2297275021181310377291461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3063033361575080503055281 2297275021181310377291461)
                  ·
                    refine ⟨430739066471495695742149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2297275021181310377291461 430739066471495695742149)
                    ·
                      rfl

theorem cell23_2516584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 4, 2, 4].length) (baseStart_2516584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2516584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2516584 prefixEnd_2516584 := by exact prefixLift 2516584
  have htrace : WordTrace (prefixWord ++ tailWord_2516584) baseStart_2516584 baseEnd_2516584 := by
    simpa [prefixWord, tailWord_2516584, baseEnd_2516584] using wordTrace_append hprefix tailTrace_2516584
  have hstable : (prefixWord ++ tailWord_2516584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2516584).length < 2 ^ (prefixWord ++ tailWord_2516584).sum := by decide
  have hdescent : baseEnd_2516584 < baseStart_2516584 := by decide
  rcases family_descends (prefixWord ++ tailWord_2516584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2516597 : List Nat := [1, 3, 4, 2, 1, 1, 3, 8]
def baseStart_2516597 : Nat := 118140960795 + 2516597 * 2 ^ 59
def prefixEnd_2516597 : Nat := 4983230072969 + 3 ^ 40 * 2516597 * 2
def baseEnd_2516597 : Nat := 47860143506036871717181

theorem tailTrace_2516597 : CollatzResearch.WordTrace tailWord_2516597 prefixEnd_2516597 47860143506036871717181 := by
  unfold tailWord_2516597
  simp only [CollatzResearch.WordTrace]
  refine ⟨91787833263806344394540045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61191888842537562929693363 91787833263806344394540045)
  ·
    refine ⟨34420437473927379147952517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91787833263806344394540045 34420437473927379147952517)
    ·
      refine ⟨6453832026361383590241097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34420437473927379147952517 6453832026361383590241097)
      ·
        refine ⟨4840374019771037692680823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6453832026361383590241097 4840374019771037692680823)
        ·
          refine ⟨7260561029656556539021235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4840374019771037692680823 7260561029656556539021235)
          ·
            refine ⟨10890841544484834808531853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7260561029656556539021235 10890841544484834808531853)
            ·
              refine ⟨4084065579181813053199445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10890841544484834808531853 4084065579181813053199445)
              ·
                refine ⟨47860143506036871717181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4084065579181813053199445 47860143506036871717181)
                ·
                  rfl

theorem cell23_2516597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 3, 8].length) (baseStart_2516597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2516597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2516597 prefixEnd_2516597 := by exact prefixLift 2516597
  have htrace : WordTrace (prefixWord ++ tailWord_2516597) baseStart_2516597 baseEnd_2516597 := by
    simpa [prefixWord, tailWord_2516597, baseEnd_2516597] using wordTrace_append hprefix tailTrace_2516597
  have hstable : (prefixWord ++ tailWord_2516597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2516597).length < 2 ^ (prefixWord ++ tailWord_2516597).sum := by decide
  have hdescent : baseEnd_2516597 < baseStart_2516597 := by decide
  rcases family_descends (prefixWord ++ tailWord_2516597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2516620 : List Nat := [2, 2, 1, 2, 1, 1, 4, 1, 2, 2, 5]
def baseStart_2516620 : Nat := 118140960795 + 2516620 * 2 ^ 59
def prefixEnd_2516620 : Nat := 4983230072969 + 3 ^ 40 * 2516620 * 2
def baseEnd_2516620 : Nat := 1292235684718048946376281

theorem tailTrace_2516620 : CollatzResearch.WordTrace tailWord_2516620 prefixEnd_2516620 1292235684718048946376281 := by
  unfold tailWord_2516620
  simp only [CollatzResearch.WordTrace]
  refine ⟨45894336071361509661313657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61192448095148679548418209 45894336071361509661313657)
  ·
    refine ⟨34420752053521132245985243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45894336071361509661313657 34420752053521132245985243)
    ·
      refine ⟨51631128080281698368977865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34420752053521132245985243 51631128080281698368977865)
      ·
        refine ⟨38723346060211273776733399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51631128080281698368977865 38723346060211273776733399)
        ·
          refine ⟨58085019090316910665100099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38723346060211273776733399 58085019090316910665100099)
          ·
            refine ⟨87127528635475365997650149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58085019090316910665100099 87127528635475365997650149)
            ·
              refine ⟨16336411619151631124559403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 87127528635475365997650149 16336411619151631124559403)
              ·
                refine ⟨24504617428727446686839105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16336411619151631124559403 24504617428727446686839105)
                ·
                  refine ⟨18378463071545585015129329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24504617428727446686839105 18378463071545585015129329)
                  ·
                    refine ⟨13783847303659188761346997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18378463071545585015129329 13783847303659188761346997)
                    ·
                      refine ⟨1292235684718048946376281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13783847303659188761346997 1292235684718048946376281)
                      ·
                        rfl

theorem cell23_2516620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 2, 2, 5].length) (baseStart_2516620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2516620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2516620 prefixEnd_2516620 := by exact prefixLift 2516620
  have htrace : WordTrace (prefixWord ++ tailWord_2516620) baseStart_2516620 baseEnd_2516620 := by
    simpa [prefixWord, tailWord_2516620, baseEnd_2516620] using wordTrace_append hprefix tailTrace_2516620
  have hstable : (prefixWord ++ tailWord_2516620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2516620).length < 2 ^ (prefixWord ++ tailWord_2516620).sum := by decide
  have hdescent : baseEnd_2516620 < baseStart_2516620 := by decide
  rcases family_descends (prefixWord ++ tailWord_2516620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2516641 : List Nat := [1, 2, 3, 3, 2, 1, 3, 2, 2, 1, 3]
def baseStart_2516641 : Nat := 118140960795 + 2516641 * 2 ^ 59
def prefixEnd_2516641 : Nat := 4983230072969 + 3 ^ 40 * 2516641 * 2
def baseEnd_2516641 : Nat := 1292246467811793364213685

theorem tailTrace_2516641 : CollatzResearch.WordTrace tailWord_2516641 prefixEnd_2516641 1292246467811793364213685 := by
  unfold tailWord_2516641
  simp only [CollatzResearch.WordTrace]
  refine ⟨91789438075646939909141777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61192958717097959939427851 91789438075646939909141777)
  ·
    refine ⟨68842078556735204931856333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91789438075646939909141777 68842078556735204931856333)
    ·
      refine ⟨25815779458775701849446125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68842078556735204931856333 25815779458775701849446125)
      ·
        refine ⟨9680917297040888193542297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25815779458775701849446125 9680917297040888193542297)
        ·
          refine ⟨7260687972780666145156723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9680917297040888193542297 7260687972780666145156723)
          ·
            refine ⟨10891031959170999217735085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7260687972780666145156723 10891031959170999217735085)
            ·
              refine ⟨4084136984689124706650657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10891031959170999217735085 4084136984689124706650657)
              ·
                refine ⟨3063102738516843529987993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4084136984689124706650657 3063102738516843529987993)
                ·
                  refine ⟨2297327053887632647490995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3063102738516843529987993 2297327053887632647490995)
                  ·
                    refine ⟨3445990580831448971236493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2297327053887632647490995 3445990580831448971236493)
                    ·
                      refine ⟨1292246467811793364213685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3445990580831448971236493 1292246467811793364213685)
                      ·
                        rfl

theorem cell23_2516641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 3, 2, 2, 1, 3].length) (baseStart_2516641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2516641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2516641 prefixEnd_2516641 := by exact prefixLift 2516641
  have htrace : WordTrace (prefixWord ++ tailWord_2516641) baseStart_2516641 baseEnd_2516641 := by
    simpa [prefixWord, tailWord_2516641, baseEnd_2516641] using wordTrace_append hprefix tailTrace_2516641
  have hstable : (prefixWord ++ tailWord_2516641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2516641).length < 2 ^ (prefixWord ++ tailWord_2516641).sum := by decide
  have hdescent : baseEnd_2516641 < baseStart_2516641 := by decide
  rcases family_descends (prefixWord ++ tailWord_2516641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2516684 : List Nat := [2, 2, 1, 5, 2, 1, 1, 1, 2, 1, 5]
def baseStart_2516684 : Nat := 118140960795 + 2516684 * 2 ^ 59
def prefixEnd_2516684 : Nat := 4983230072969 + 3 ^ 40 * 2516684 * 2
def baseEnd_2516684 : Nat := 1292268547479936695975987

theorem tailTrace_2516684 : CollatzResearch.WordTrace tailWord_2516684 prefixEnd_2516684 1292268547479936695975987 := by
  unfold tailWord_2516684
  simp only [CollatzResearch.WordTrace]
  refine ⟨45895503207245579126478553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61194004276327438835304737 45895503207245579126478553)
  ·
    refine ⟨34421627405434184344858915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45895503207245579126478553 34421627405434184344858915)
    ·
      refine ⟨51632441108151276517288373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34421627405434184344858915 51632441108151276517288373)
      ·
        refine ⟨4840541353889182173495785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 51632441108151276517288373 4840541353889182173495785)
        ·
          refine ⟨3630406015416886630121839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4840541353889182173495785 3630406015416886630121839)
          ·
            refine ⟨5445609023125329945182759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3630406015416886630121839 5445609023125329945182759)
            ·
              refine ⟨8168413534687994917774139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5445609023125329945182759 8168413534687994917774139)
              ·
                refine ⟨12252620302031992376661209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8168413534687994917774139 12252620302031992376661209)
                ·
                  refine ⟨9189465226523994282495907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12252620302031992376661209 9189465226523994282495907)
                  ·
                    refine ⟨13784197839785991423743861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9189465226523994282495907 13784197839785991423743861)
                    ·
                      refine ⟨1292268547479936695975987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13784197839785991423743861 1292268547479936695975987)
                      ·
                        rfl

theorem cell23_2516684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_2516684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2516684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2516684 prefixEnd_2516684 := by exact prefixLift 2516684
  have htrace : WordTrace (prefixWord ++ tailWord_2516684) baseStart_2516684 baseEnd_2516684 := by
    simpa [prefixWord, tailWord_2516684, baseEnd_2516684] using wordTrace_append hprefix tailTrace_2516684
  have hstable : (prefixWord ++ tailWord_2516684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2516684).length < 2 ^ (prefixWord ++ tailWord_2516684).sum := by decide
  have hdescent : baseEnd_2516684 < baseStart_2516684 := by decide
  rcases family_descends (prefixWord ++ tailWord_2516684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2516737 : List Nat := [1, 2, 4, 1, 1, 1, 2, 3, 1, 3, 4]
def baseStart_2516737 : Nat := 118140960795 + 2516737 * 2 ^ 59
def prefixEnd_2516737 : Nat := 4983230072969 + 3 ^ 40 * 2516737 * 2
def baseEnd_2516737 : Nat := 1292295761954624988613243

theorem tailTrace_2516737 : CollatzResearch.WordTrace tailWord_2516737 prefixEnd_2516737 1292295761954624988613243 := by
  unfold tailWord_2516737
  simp only [CollatzResearch.WordTrace]
  refine ⟨91792939483299148304636465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61195292988866098869757643 91792939483299148304636465)
  ·
    refine ⟨68844704612474361228477349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91792939483299148304636465 68844704612474361228477349)
    ·
      refine ⟨12908382114838942730339503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68844704612474361228477349 12908382114838942730339503)
      ·
        refine ⟨19362573172258414095509255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12908382114838942730339503 19362573172258414095509255)
        ·
          refine ⟨29043859758387621143263883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19362573172258414095509255 29043859758387621143263883)
          ·
            refine ⟨43565789637581431714895825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29043859758387621143263883 43565789637581431714895825)
            ·
              refine ⟨32674342228186073786171869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43565789637581431714895825 32674342228186073786171869)
              ·
                refine ⟨12252878335569777669814451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32674342228186073786171869 12252878335569777669814451)
                ·
                  refine ⟨18379317503354666504721677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12252878335569777669814451 18379317503354666504721677)
                  ·
                    refine ⟨6892244063757999939270629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18379317503354666504721677 6892244063757999939270629)
                    ·
                      refine ⟨1292295761954624988613243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6892244063757999939270629 1292295761954624988613243)
                      ·
                        rfl

theorem cell23_2516737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 3, 1, 3, 4].length) (baseStart_2516737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2516737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2516737 prefixEnd_2516737 := by exact prefixLift 2516737
  have htrace : WordTrace (prefixWord ++ tailWord_2516737) baseStart_2516737 baseEnd_2516737 := by
    simpa [prefixWord, tailWord_2516737, baseEnd_2516737] using wordTrace_append hprefix tailTrace_2516737
  have hstable : (prefixWord ++ tailWord_2516737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2516737).length < 2 ^ (prefixWord ++ tailWord_2516737).sum := by decide
  have hdescent : baseEnd_2516737 < baseStart_2516737 := by decide
  rcases family_descends (prefixWord ++ tailWord_2516737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2516764 : List Nat := [2, 2, 3, 1, 1, 2, 2, 3, 3, 4]
def baseStart_2516764 : Nat := 118140960795 + 2516764 * 2 ^ 59
def prefixEnd_2516764 : Nat := 4983230072969 + 3 ^ 40 * 2516764 * 2
def baseEnd_2516764 : Nat := 430769875310765460991873

theorem tailTrace_2516764 : CollatzResearch.WordTrace tailWord_2516764 prefixEnd_2516764 430769875310765460991873 := by
  unfold tailWord_2516764
  simp only [CollatzResearch.WordTrace]
  refine ⟨45896962127100665957934673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61195949502800887943912897 45896962127100665957934673)
  ·
    refine ⟨34422721595325499468451005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45896962127100665957934673 34422721595325499468451005)
    ·
      refine ⟨12908520598247062300669127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34422721595325499468451005 12908520598247062300669127)
      ·
        refine ⟨19362780897370593451003691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12908520598247062300669127 19362780897370593451003691)
        ·
          refine ⟨29044171346055890176505537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19362780897370593451003691 29044171346055890176505537)
          ·
            refine ⟨21783128509541917632379153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29044171346055890176505537 21783128509541917632379153)
            ·
              refine ⟨16337346382156438224284365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21783128509541917632379153 16337346382156438224284365)
              ·
                refine ⟨6126504893308664334106637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16337346382156438224284365 6126504893308664334106637)
                ·
                  refine ⟨2297439334990749125289989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6126504893308664334106637 2297439334990749125289989)
                  ·
                    refine ⟨430769875310765460991873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2297439334990749125289989 430769875310765460991873)
                    ·
                      rfl

theorem cell23_2516764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 3, 3, 4].length) (baseStart_2516764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2516764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2516764 prefixEnd_2516764 := by exact prefixLift 2516764
  have htrace : WordTrace (prefixWord ++ tailWord_2516764) baseStart_2516764 baseEnd_2516764 := by
    simpa [prefixWord, tailWord_2516764, baseEnd_2516764] using wordTrace_append hprefix tailTrace_2516764
  have hstable : (prefixWord ++ tailWord_2516764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2516764).length < 2 ^ (prefixWord ++ tailWord_2516764).sum := by decide
  have hdescent : baseEnd_2516764 < baseStart_2516764 := by decide
  rcases family_descends (prefixWord ++ tailWord_2516764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2516788 : List Nat := [2, 5, 1, 1, 2, 3, 1, 1, 2, 1, 4]
def baseStart_2516788 : Nat := 118140960795 + 2516788 * 2 ^ 59
def prefixEnd_2516788 : Nat := 4983230072969 + 3 ^ 40 * 2516788 * 2
def baseEnd_2516788 : Nat := 1292321949468004289075509

theorem tailTrace_2516788 : CollatzResearch.WordTrace tailWord_2516788 prefixEnd_2516788 1292321949468004289075509 := by
  unfold tailWord_2516788
  simp only [CollatzResearch.WordTrace]
  refine ⟨45897399803057192007371509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61196533070742922676495345 45897399803057192007371509)
  ·
    refine ⟨4302881231536611750691079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 45897399803057192007371509 4302881231536611750691079)
    ·
      refine ⟨6454321847304917626036619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4302881231536611750691079 6454321847304917626036619)
      ·
        refine ⟨9681482770957376439054929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6454321847304917626036619 9681482770957376439054929)
        ·
          refine ⟨7261112078218032329291197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9681482770957376439054929 7261112078218032329291197)
          ·
            refine ⟨2722917029331762123484199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7261112078218032329291197 2722917029331762123484199)
            ·
              refine ⟨4084375543997643185226299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2722917029331762123484199 4084375543997643185226299)
              ·
                refine ⟨6126563315996464777839449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4084375543997643185226299 6126563315996464777839449)
                ·
                  refine ⟨4594922486997348583379587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6126563315996464777839449 4594922486997348583379587)
                  ·
                    refine ⟨6892383730496022875069381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4594922486997348583379587 6892383730496022875069381)
                    ·
                      refine ⟨1292321949468004289075509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6892383730496022875069381 1292321949468004289075509)
                      ·
                        rfl

theorem cell23_2516788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 1, 1, 2, 1, 4].length) (baseStart_2516788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2516788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2516788 prefixEnd_2516788 := by exact prefixLift 2516788
  have htrace : WordTrace (prefixWord ++ tailWord_2516788) baseStart_2516788 baseEnd_2516788 := by
    simpa [prefixWord, tailWord_2516788, baseEnd_2516788] using wordTrace_append hprefix tailTrace_2516788
  have hstable : (prefixWord ++ tailWord_2516788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2516788).length < 2 ^ (prefixWord ++ tailWord_2516788).sum := by decide
  have hdescent : baseEnd_2516788 < baseStart_2516788 := by decide
  rcases family_descends (prefixWord ++ tailWord_2516788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2516798 : List Nat := [4, 2, 1, 2, 2, 1, 1, 5, 1, 4]
def baseStart_2516798 : Nat := 118140960795 + 2516798 * 2 ^ 59
def prefixEnd_2516798 : Nat := 4983230072969 + 3 ^ 40 * 2516798 * 2
def baseEnd_2516798 : Nat := 430775694758183083316821

theorem tailTrace_2516798 : CollatzResearch.WordTrace tailWord_2516798 prefixEnd_2516798 430775694758183083316821 := by
  unfold tailWord_2516798
  simp only [CollatzResearch.WordTrace]
  refine ⟨11474395542009769465325881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61196776224052103815071365 11474395542009769465325881)
  ·
    refine ⟨8605796656507327098994411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11474395542009769465325881 8605796656507327098994411)
    ·
      refine ⟨12908694984760990648491617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8605796656507327098994411 12908694984760990648491617)
      ·
        refine ⟨9681521238570742986368713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12908694984760990648491617 9681521238570742986368713)
        ·
          refine ⟨7261140928928057239776535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9681521238570742986368713 7261140928928057239776535)
          ·
            refine ⟨10891711393392085859664803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7261140928928057239776535 10891711393392085859664803)
            ·
              refine ⟨16337567090088128789497205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10891711393392085859664803 16337567090088128789497205)
              ·
                refine ⟨1531646914695762074015363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16337567090088128789497205 1531646914695762074015363)
                ·
                  refine ⟨2297470372043643111023045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1531646914695762074015363 2297470372043643111023045)
                  ·
                    refine ⟨430775694758183083316821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2297470372043643111023045 430775694758183083316821)
                    ·
                      rfl

theorem cell23_2516798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 5, 1, 4].length) (baseStart_2516798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2516798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2516798 prefixEnd_2516798 := by exact prefixLift 2516798
  have htrace : WordTrace (prefixWord ++ tailWord_2516798) baseStart_2516798 baseEnd_2516798 := by
    simpa [prefixWord, tailWord_2516798, baseEnd_2516798] using wordTrace_append hprefix tailTrace_2516798
  have hstable : (prefixWord ++ tailWord_2516798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2516798).length < 2 ^ (prefixWord ++ tailWord_2516798).sum := by decide
  have hdescent : baseEnd_2516798 < baseStart_2516798 := by decide
  rcases family_descends (prefixWord ++ tailWord_2516798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2516821 : List Nat := [1, 3, 2, 2, 2, 2, 1, 3, 3, 1, 3]
def baseStart_2516821 : Nat := 118140960795 + 2516821 * 2 ^ 59
def prefixEnd_2516821 : Nat := 4983230072969 + 3 ^ 40 * 2516821 * 2
def baseEnd_2516821 : Nat := 1292338894329602659962857

theorem tailTrace_2516821 : CollatzResearch.WordTrace tailWord_2516821 prefixEnd_2516821 1292338894329602659962857 := by
  unfold tailWord_2516821
  simp only [CollatzResearch.WordTrace]
  refine ⟨91796003214994830650694317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61197335476663220433796211 91796003214994830650694317)
  ·
    refine ⟨34423501205623061494010369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91796003214994830650694317 34423501205623061494010369)
    ·
      refine ⟨25817625904217296120507777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34423501205623061494010369 25817625904217296120507777)
      ·
        refine ⟨19363219428162972090380833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25817625904217296120507777 19363219428162972090380833)
        ·
          refine ⟨14522414571122229067785625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19363219428162972090380833 14522414571122229067785625)
          ·
            refine ⟨10891810928341671800839219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14522414571122229067785625 10891810928341671800839219)
            ·
              refine ⟨16337716392512507701258829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10891810928341671800839219 16337716392512507701258829)
              ·
                refine ⟨6126643647192190387972061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16337716392512507701258829 6126643647192190387972061)
                ·
                  refine ⟨2297491367697071395489523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6126643647192190387972061 2297491367697071395489523)
                  ·
                    refine ⟨3446237051545607093234285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2297491367697071395489523 3446237051545607093234285)
                    ·
                      refine ⟨1292338894329602659962857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3446237051545607093234285 1292338894329602659962857)
                      ·
                        rfl

theorem cell23_2516821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 3, 3, 1, 3].length) (baseStart_2516821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2516821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2516821 prefixEnd_2516821 := by exact prefixLift 2516821
  have htrace : WordTrace (prefixWord ++ tailWord_2516821) baseStart_2516821 baseEnd_2516821 := by
    simpa [prefixWord, tailWord_2516821, baseEnd_2516821] using wordTrace_append hprefix tailTrace_2516821
  have hstable : (prefixWord ++ tailWord_2516821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2516821).length < 2 ^ (prefixWord ++ tailWord_2516821).sum := by decide
  have hdescent : baseEnd_2516821 < baseStart_2516821 := by decide
  rcases family_descends (prefixWord ++ tailWord_2516821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2516828 : List Nat := [2, 2, 4, 2, 2, 1, 3, 1, 6]
def baseStart_2516828 : Nat := 118140960795 + 2516828 * 2 ^ 59
def prefixEnd_2516828 : Nat := 4983230072969 + 3 ^ 40 * 2516828 * 2
def baseEnd_2516828 : Nat := 143593609854909348063925

theorem tailTrace_2516828 : CollatzResearch.WordTrace tailWord_2516828 prefixEnd_2516828 143593609854909348063925 := by
  unfold tailWord_2516828
  simp only [CollatzResearch.WordTrace]
  refine ⟨45898129262984735423099569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61197505683979647230799425 45898129262984735423099569)
  ·
    refine ⟨34423596947238551567324677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45898129262984735423099569 34423596947238551567324677)
    ·
      refine ⟨6454424427607228418873377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34423596947238551567324677 6454424427607228418873377)
      ·
        refine ⟨4840818320705421314155033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6454424427607228418873377 4840818320705421314155033)
        ·
          refine ⟨3630613740529065985616275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4840818320705421314155033 3630613740529065985616275)
          ·
            refine ⟨5445920610793598978424413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3630613740529065985616275 5445920610793598978424413)
            ·
              refine ⟨2042220229047599616909155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5445920610793598978424413 2042220229047599616909155)
              ·
                refine ⟨3063330343571399425363733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2042220229047599616909155 3063330343571399425363733)
                ·
                  refine ⟨143593609854909348063925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3063330343571399425363733 143593609854909348063925)
                  ·
                    rfl

theorem cell23_2516828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 3, 1, 6].length) (baseStart_2516828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2516828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2516828 prefixEnd_2516828 := by exact prefixLift 2516828
  have htrace : WordTrace (prefixWord ++ tailWord_2516828) baseStart_2516828 baseEnd_2516828 := by
    simpa [prefixWord, tailWord_2516828, baseEnd_2516828] using wordTrace_append hprefix tailTrace_2516828
  have hstable : (prefixWord ++ tailWord_2516828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2516828).length < 2 ^ (prefixWord ++ tailWord_2516828).sum := by decide
  have hdescent : baseEnd_2516828 < baseStart_2516828 := by decide
  rcases family_descends (prefixWord ++ tailWord_2516828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2516864 : List Nat := [2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 5]
def baseStart_2516864 : Nat := 118140960795 + 2516864 * 2 ^ 59
def prefixEnd_2516864 : Nat := 4983230072969 + 3 ^ 40 * 2516864 * 2
def baseEnd_2516864 : Nat := 1292360973997745991725159

theorem tailTrace_2516864 : CollatzResearch.WordTrace tailWord_2516864 prefixEnd_2516864 1292360973997745991725159 := by
  unfold tailWord_2516864
  simp only [CollatzResearch.WordTrace]
  refine ⟨45898785776919524497254823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61198381035892699329673097 45898785776919524497254823)
  ·
    refine ⟨68848178665379286745882235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45898785776919524497254823 68848178665379286745882235)
    ·
      refine ⟨103272267998068930118823353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68848178665379286745882235 103272267998068930118823353)
      ·
        refine ⟨77454200998551697589117515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103272267998068930118823353 77454200998551697589117515)
        ·
          refine ⟨116181301497827546383676273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77454200998551697589117515 116181301497827546383676273)
          ·
            refine ⟨87135976123370659787757205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116181301497827546383676273 87135976123370659787757205)
            ·
              refine ⟨4084498880782999677551119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 87135976123370659787757205 4084498880782999677551119)
              ·
                refine ⟨6126748321174499516326679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4084498880782999677551119 6126748321174499516326679)
                ·
                  refine ⟨9190122481761749274490019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6126748321174499516326679 9190122481761749274490019)
                  ·
                    refine ⟨13785183722642623911735029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9190122481761749274490019 13785183722642623911735029)
                    ·
                      refine ⟨1292360973997745991725159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13785183722642623911735029 1292360973997745991725159)
                      ·
                        rfl

theorem cell23_2516864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 5].length) (baseStart_2516864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2516864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2516864 prefixEnd_2516864 := by exact prefixLift 2516864
  have htrace : WordTrace (prefixWord ++ tailWord_2516864) baseStart_2516864 baseEnd_2516864 := by
    simpa [prefixWord, tailWord_2516864, baseEnd_2516864] using wordTrace_append hprefix tailTrace_2516864
  have hstable : (prefixWord ++ tailWord_2516864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2516864).length < 2 ^ (prefixWord ++ tailWord_2516864).sum := by decide
  have hdescent : baseEnd_2516864 < baseStart_2516864 := by decide
  rcases family_descends (prefixWord ++ tailWord_2516864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2516865 : List Nat := [1, 2, 4, 4, 1, 1, 1, 2, 2, 3, 2]
def baseStart_2516865 : Nat := 118140960795 + 2516865 * 2 ^ 59
def prefixEnd_2516865 : Nat := 4983230072969 + 3 ^ 40 * 2516865 * 2
def baseEnd_2516865 : Nat := 1292361487478400487812655

theorem tailTrace_2516865 : CollatzResearch.WordTrace tailWord_2516865 prefixEnd_2516865 1292361487478400487812655 := by
  unfold tailWord_2516865
  simp only [CollatzResearch.WordTrace]
  refine ⟨91797608026835426165296049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61198405351223617443530699 91797608026835426165296049)
  ·
    refine ⟨68848206020126569623972037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91797608026835426165296049 68848206020126569623972037)
    ·
      refine ⟨12909038628773731804494757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68848206020126569623972037 12909038628773731804494757)
      ·
        refine ⟨2420444742895074713342767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12909038628773731804494757 2420444742895074713342767)
        ·
          refine ⟨3630667114342612070014151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2420444742895074713342767 3630667114342612070014151)
          ·
            refine ⟨5446000671513918105021227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3630667114342612070014151 5446000671513918105021227)
            ·
              refine ⟨8169001007270877157531841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5446000671513918105021227 8169001007270877157531841)
              ·
                refine ⟨6126750755453157868148881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8169001007270877157531841 6126750755453157868148881)
                ·
                  refine ⟨4595063066589868401111661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6126750755453157868148881 4595063066589868401111661)
                  ·
                    refine ⟨1723148649971200650416873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4595063066589868401111661 1723148649971200650416873)
                    ·
                      refine ⟨1292361487478400487812655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1723148649971200650416873 1292361487478400487812655)
                      ·
                        rfl

theorem cell23_2516865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_2516865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2516865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2516865 prefixEnd_2516865 := by exact prefixLift 2516865
  have htrace : WordTrace (prefixWord ++ tailWord_2516865) baseStart_2516865 baseEnd_2516865 := by
    simpa [prefixWord, tailWord_2516865, baseEnd_2516865] using wordTrace_append hprefix tailTrace_2516865
  have hstable : (prefixWord ++ tailWord_2516865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2516865).length < 2 ^ (prefixWord ++ tailWord_2516865).sum := by decide
  have hdescent : baseEnd_2516865 < baseStart_2516865 := by decide
  rcases family_descends (prefixWord ++ tailWord_2516865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2516867 : List Nat := [1, 1, 1, 3, 4, 2, 11]
def baseStart_2516867 : Nat := 118140960795 + 2516867 * 2 ^ 59
def prefixEnd_2516867 : Nat := 4983230072969 + 3 ^ 40 * 2516867 * 2
def baseEnd_2516867 : Nat := 15955092770860610864045

theorem tailTrace_2516867 : CollatzResearch.WordTrace tailWord_2516867 prefixEnd_2516867 15955092770860610864045 := by
  unfold tailWord_2516867
  simp only [CollatzResearch.WordTrace]
  refine ⟨91797680972828180506868855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61198453981885453671245903 91797680972828180506868855)
  ·
    refine ⟨137696521459242270760303283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91797680972828180506868855 137696521459242270760303283)
    ·
      refine ⟨206544782188863406140454925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137696521459242270760303283 206544782188863406140454925)
      ·
        refine ⟨77454293320823777302670597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 206544782188863406140454925 77454293320823777302670597)
        ·
          refine ⟨14522679997654458244250737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 77454293320823777302670597 14522679997654458244250737)
          ·
            refine ⟨10892009998240843683188053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14522679997654458244250737 10892009998240843683188053)
            ·
              refine ⟨15955092770860610864045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 10892009998240843683188053 15955092770860610864045)
              ·
                rfl

theorem cell23_2516867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 11].length) (baseStart_2516867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2516867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2516867 prefixEnd_2516867 := by exact prefixLift 2516867
  have htrace : WordTrace (prefixWord ++ tailWord_2516867) baseStart_2516867 baseEnd_2516867 := by
    simpa [prefixWord, tailWord_2516867, baseEnd_2516867] using wordTrace_append hprefix tailTrace_2516867
  have hstable : (prefixWord ++ tailWord_2516867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2516867).length < 2 ^ (prefixWord ++ tailWord_2516867).sum := by decide
  have hdescent : baseEnd_2516867 < baseStart_2516867 := by decide
  rcases family_descends (prefixWord ++ tailWord_2516867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2516872 : List Nat := [2, 1, 3, 3, 3, 1, 3, 2, 1, 1, 3]
def baseStart_2516872 : Nat := 118140960795 + 2516872 * 2 ^ 59
def prefixEnd_2516872 : Nat := 4983230072969 + 3 ^ 40 * 2516872 * 2
def baseEnd_2516872 : Nat := 1292365081842981960425123

theorem tailTrace_2516872 : CollatzResearch.WordTrace tailWord_2516872 prefixEnd_2516872 1292365081842981960425123 := by
  unfold tailWord_2516872
  simp only [CollatzResearch.WordTrace]
  refine ⟨45898931668905033180400435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61198575558540044240533913 45898931668905033180400435)
  ·
    refine ⟨68848397503357549770600653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45898931668905033180400435 68848397503357549770600653)
    ·
      refine ⟨25818149063759081163975245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68848397503357549770600653 25818149063759081163975245)
      ·
        refine ⟨9681805898909655436490717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25818149063759081163975245 9681805898909655436490717)
        ·
          refine ⟨3630677212091120788684019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9681805898909655436490717 3630677212091120788684019)
          ·
            refine ⟨5446015818136681183026029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3630677212091120788684019 5446015818136681183026029)
            ·
              refine ⟨2042255931801255443634761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5446015818136681183026029 2042255931801255443634761)
              ·
                refine ⟨1531691948850941582726071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2042255931801255443634761 1531691948850941582726071)
                ·
                  refine ⟨2297537923276412374089107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1531691948850941582726071 2297537923276412374089107)
                  ·
                    refine ⟨3446306884914618561133661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2297537923276412374089107 3446306884914618561133661)
                    ·
                      refine ⟨1292365081842981960425123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3446306884914618561133661 1292365081842981960425123)
                      ·
                        rfl

theorem cell23_2516872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 3, 2, 1, 1, 3].length) (baseStart_2516872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2516872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2516872 prefixEnd_2516872 := by exact prefixLift 2516872
  have htrace : WordTrace (prefixWord ++ tailWord_2516872) baseStart_2516872 baseEnd_2516872 := by
    simpa [prefixWord, tailWord_2516872, baseEnd_2516872] using wordTrace_append hprefix tailTrace_2516872
  have hstable : (prefixWord ++ tailWord_2516872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2516872).length < 2 ^ (prefixWord ++ tailWord_2516872).sum := by decide
  have hdescent : baseEnd_2516872 < baseStart_2516872 := by decide
  rcases family_descends (prefixWord ++ tailWord_2516872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2516884 : List Nat := [2, 4, 2, 1, 1, 2, 1, 10]
def baseStart_2516884 : Nat := 118140960795 + 2516884 * 2 ^ 59
def prefixEnd_2516884 : Nat := 4983230072969 + 3 ^ 40 * 2516884 * 2
def baseEnd_2516884 : Nat := 47865601615216144943521

theorem tailTrace_2516884 : CollatzResearch.WordTrace tailWord_2516884 prefixEnd_2516884 47865601615216144943521 := by
  unfold tailWord_2516884
  simp only [CollatzResearch.WordTrace]
  refine ⟨45899150506883296205118853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61198867342511061606825137 45899150506883296205118853)
  ·
    refine ⟨8606090720040618038459785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45899150506883296205118853 8606090720040618038459785)
    ·
      refine ⟨6454568040030463528844839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8606090720040618038459785 6454568040030463528844839)
      ·
        refine ⟨9681852060045695293267259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6454568040030463528844839 9681852060045695293267259)
        ·
          refine ⟨14522778090068542939900889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9681852060045695293267259 14522778090068542939900889)
          ·
            refine ⟨10892083567551407204925667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14522778090068542939900889 10892083567551407204925667)
            ·
              refine ⟨16338125351327110807388501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10892083567551407204925667 16338125351327110807388501)
              ·
                refine ⟨47865601615216144943521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 16338125351327110807388501 47865601615216144943521)
                ·
                  rfl

theorem cell23_2516884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 10].length) (baseStart_2516884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2516884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2516884 prefixEnd_2516884 := by exact prefixLift 2516884
  have htrace : WordTrace (prefixWord ++ tailWord_2516884) baseStart_2516884 baseEnd_2516884 := by
    simpa [prefixWord, tailWord_2516884, baseEnd_2516884] using wordTrace_append hprefix tailTrace_2516884
  have hstable : (prefixWord ++ tailWord_2516884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2516884).length < 2 ^ (prefixWord ++ tailWord_2516884).sum := by decide
  have hdescent : baseEnd_2516884 < baseStart_2516884 := by decide
  rcases family_descends (prefixWord ++ tailWord_2516884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2516895 : List Nat := [1, 1, 2, 5, 4, 1, 1, 2, 1, 1, 4]
def baseStart_2516895 : Nat := 118140960795 + 2516895 * 2 ^ 59
def prefixEnd_2516895 : Nat := 4983230072969 + 3 ^ 40 * 2516895 * 2
def baseEnd_2516895 : Nat := 1292376891898035370437517

theorem tailTrace_2516895 : CollatzResearch.WordTrace tailWord_2516895 prefixEnd_2516895 1292376891898035370437517 := by
  unfold tailWord_2516895
  simp only [CollatzResearch.WordTrace]
  refine ⟨91798702216726741288888139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61199134811151160859258759 91798702216726741288888139)
  ·
    refine ⟨137698053325090111933332209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91798702216726741288888139 137698053325090111933332209)
    ·
      refine ⟨103273539993817583949999157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137698053325090111933332209 103273539993817583949999157)
      ·
        refine ⟨9681894374420398495312421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 103273539993817583949999157 9681894374420398495312421)
        ·
          refine ⟨1815355195203824717871079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9681894374420398495312421 1815355195203824717871079)
          ·
            refine ⟨2723032792805737076806619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1815355195203824717871079 2723032792805737076806619)
            ·
              refine ⟨4084549189208605615209929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2723032792805737076806619 4084549189208605615209929)
              ·
                refine ⟨3063411891906454211407447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4084549189208605615209929 3063411891906454211407447)
                ·
                  refine ⟨4595117837859681317111171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3063411891906454211407447 4595117837859681317111171)
                  ·
                    refine ⟨6892676756789521975666757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4595117837859681317111171 6892676756789521975666757)
                    ·
                      refine ⟨1292376891898035370437517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6892676756789521975666757 1292376891898035370437517)
                      ·
                        rfl

theorem cell23_2516895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 1, 2, 1, 1, 4].length) (baseStart_2516895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2516895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2516895 prefixEnd_2516895 := by exact prefixLift 2516895
  have htrace : WordTrace (prefixWord ++ tailWord_2516895) baseStart_2516895 baseEnd_2516895 := by
    simpa [prefixWord, tailWord_2516895, baseEnd_2516895] using wordTrace_append hprefix tailTrace_2516895
  have hstable : (prefixWord ++ tailWord_2516895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2516895).length < 2 ^ (prefixWord ++ tailWord_2516895).sum := by decide
  have hdescent : baseEnd_2516895 < baseStart_2516895 := by decide
  rcases family_descends (prefixWord ++ tailWord_2516895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2516898 : List Nat := [3, 3, 1, 2, 3, 1, 1, 1, 3, 2, 3]
def baseStart_2516898 : Nat := 118140960795 + 2516898 * 2 ^ 59
def prefixEnd_2516898 : Nat := 4983230072969 + 3 ^ 40 * 2516898 * 2
def baseEnd_2516898 : Nat := 1292378432339998858700003

theorem tailTrace_2516898 : CollatzResearch.WordTrace tailWord_2516898 prefixEnd_2516898 1292378432339998858700003 := by
  unfold tailWord_2516898
  simp only [CollatzResearch.WordTrace]
  refine ⟨22949702908928968200311837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61199207757143915200831565 22949702908928968200311837)
  ·
    refine ⟨8606138590848363075116939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22949702908928968200311837 8606138590848363075116939)
    ·
      refine ⟨12909207886272544612675409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8606138590848363075116939 12909207886272544612675409)
      ·
        refine ⟨9681905914704408459506557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12909207886272544612675409 9681905914704408459506557)
        ·
          refine ⟨3630714718014153172314959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9681905914704408459506557 3630714718014153172314959)
          ·
            refine ⟨5446072077021229758472439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3630714718014153172314959 5446072077021229758472439)
            ·
              refine ⟨8169108115531844637708659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5446072077021229758472439 8169108115531844637708659)
              ·
                refine ⟨12253662173297766956562989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8169108115531844637708659 12253662173297766956562989)
                ·
                  refine ⟨4595123314986662608711121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12253662173297766956562989 4595123314986662608711121)
                  ·
                    refine ⟨3446342486239996956533341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4595123314986662608711121 3446342486239996956533341)
                    ·
                      refine ⟨1292378432339998858700003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3446342486239996956533341 1292378432339998858700003)
                      ·
                        rfl

theorem cell23_2516898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 1, 3, 2, 3].length) (baseStart_2516898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2516898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2516898 prefixEnd_2516898 := by exact prefixLift 2516898
  have htrace : WordTrace (prefixWord ++ tailWord_2516898) baseStart_2516898 baseEnd_2516898 := by
    simpa [prefixWord, tailWord_2516898, baseEnd_2516898] using wordTrace_append hprefix tailTrace_2516898
  have hstable : (prefixWord ++ tailWord_2516898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2516898).length < 2 ^ (prefixWord ++ tailWord_2516898).sum := by decide
  have hdescent : baseEnd_2516898 < baseStart_2516898 := by decide
  rcases family_descends (prefixWord ++ tailWord_2516898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2516928 : List Nat := [2, 1, 1, 2, 3, 2, 4, 2, 2, 1, 3]
def baseStart_2516928 : Nat := 118140960795 + 2516928 * 2 ^ 59
def prefixEnd_2516928 : Nat := 4983230072969 + 3 ^ 40 * 2516928 * 2
def baseEnd_2516928 : Nat := 1292393836759633741324865

theorem tailTrace_2516928 : CollatzResearch.WordTrace tailWord_2516928 prefixEnd_2516928 1292393836759633741324865 := by
  unfold tailWord_2516928
  simp only [CollatzResearch.WordTrace]
  refine ⟨45899952912803593962419719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61199937217071458616559625 45899952912803593962419719)
  ·
    refine ⟨68849929369205390943629579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45899952912803593962419719 68849929369205390943629579)
    ·
      refine ⟨103274894053808086415444369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68849929369205390943629579 103274894053808086415444369)
      ·
        refine ⟨77456170540356064811583277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103274894053808086415444369 77456170540356064811583277)
        ·
          refine ⟨29046063952633524304343729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77456170540356064811583277 29046063952633524304343729)
          ·
            refine ⟨21784547964475143228257797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29046063952633524304343729 21784547964475143228257797)
            ·
              refine ⟨4084602743339089355298337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21784547964475143228257797 4084602743339089355298337)
              ·
                refine ⟨3063452057504317016473753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4084602743339089355298337 3063452057504317016473753)
                ·
                  refine ⟨2297589043128237762355315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3063452057504317016473753 2297589043128237762355315)
                  ·
                    refine ⟨3446383564692356643532973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2297589043128237762355315 3446383564692356643532973)
                    ·
                      refine ⟨1292393836759633741324865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3446383564692356643532973 1292393836759633741324865)
                      ·
                        rfl

theorem cell23_2516928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 4, 2, 2, 1, 3].length) (baseStart_2516928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2516928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2516928 prefixEnd_2516928 := by exact prefixLift 2516928
  have htrace : WordTrace (prefixWord ++ tailWord_2516928) baseStart_2516928 baseEnd_2516928 := by
    simpa [prefixWord, tailWord_2516928, baseEnd_2516928] using wordTrace_append hprefix tailTrace_2516928
  have hstable : (prefixWord ++ tailWord_2516928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2516928).length < 2 ^ (prefixWord ++ tailWord_2516928).sum := by decide
  have hdescent : baseEnd_2516928 < baseStart_2516928 := by decide
  rcases family_descends (prefixWord ++ tailWord_2516928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2516964 : List Nat := [2, 3, 1, 1, 1, 1, 3, 2, 1, 4, 4]
def baseStart_2516964 : Nat := 118140960795 + 2516964 * 2 ^ 59
def prefixEnd_2516964 : Nat := 4983230072969 + 3 ^ 40 * 2516964 * 2
def baseEnd_2516964 : Nat := 1292412322063195600474699

theorem tailTrace_2516964 : CollatzResearch.WordTrace tailWord_2516964 prefixEnd_2516964 1292412322063195600474699 := by
  unfold tailWord_2516964
  simp only [CollatzResearch.WordTrace]
  refine ⟨45900609426738383036574973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61200812568984510715433297 45900609426738383036574973)
  ·
    refine ⟨17212728535026893638715615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45900609426738383036574973 17212728535026893638715615)
    ·
      refine ⟨25819092802540340458073423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17212728535026893638715615 25819092802540340458073423)
      ·
        refine ⟨38728639203810510687110135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25819092802540340458073423 38728639203810510687110135)
        ·
          refine ⟨58092958805715766030665203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38728639203810510687110135 58092958805715766030665203)
          ·
            refine ⟨87139438208573649045997805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58092958805715766030665203 87139438208573649045997805)
            ·
              refine ⟨32677289328215118392249177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 87139438208573649045997805 32677289328215118392249177)
              ·
                refine ⟨24507966996161338794186883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32677289328215118392249177 24507966996161338794186883)
                ·
                  refine ⟨36761950494242008191280325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24507966996161338794186883 36761950494242008191280325)
                  ·
                    refine ⟨6892865717670376535865061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36761950494242008191280325 6892865717670376535865061)
                    ·
                      refine ⟨1292412322063195600474699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6892865717670376535865061 1292412322063195600474699)
                      ·
                        rfl

theorem cell23_2516964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 2, 1, 4, 4].length) (baseStart_2516964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2516964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2516964 prefixEnd_2516964 := by exact prefixLift 2516964
  have htrace : WordTrace (prefixWord ++ tailWord_2516964) baseStart_2516964 baseEnd_2516964 := by
    simpa [prefixWord, tailWord_2516964, baseEnd_2516964] using wordTrace_append hprefix tailTrace_2516964
  have hstable : (prefixWord ++ tailWord_2516964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2516964).length < 2 ^ (prefixWord ++ tailWord_2516964).sum := by decide
  have hdescent : baseEnd_2516964 < baseStart_2516964 := by decide
  rcases family_descends (prefixWord ++ tailWord_2516964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2516968 : List Nat := [2, 1, 4, 1, 1, 1, 1, 4, 4, 2, 2]
def baseStart_2516968 : Nat := 118140960795 + 2516968 * 2 ^ 59
def prefixEnd_2516968 : Nat := 4983230072969 + 3 ^ 40 * 2516968 * 2
def baseEnd_2516968 : Nat := 1292414375985813584824681

theorem tailTrace_2516968 : CollatzResearch.WordTrace tailWord_2516968 prefixEnd_2516968 1292414375985813584824681 := by
  unfold tailWord_2516968
  simp only [CollatzResearch.WordTrace]
  refine ⟨45900682372731137378147779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61200909830308183170863705 45900682372731137378147779)
  ·
    refine ⟨68851023559096706067221669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45900682372731137378147779 68851023559096706067221669)
    ·
      refine ⟨12909566917330632387604063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68851023559096706067221669 12909566917330632387604063)
      ·
        refine ⟨19364350375995948581406095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12909566917330632387604063 19364350375995948581406095)
        ·
          refine ⟨29046525563993922872109143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19364350375995948581406095 29046525563993922872109143)
          ·
            refine ⟨43569788345990884308163715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29046525563993922872109143 43569788345990884308163715)
            ·
              refine ⟨65354682518986326462245573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43569788345990884308163715 65354682518986326462245573)
              ·
                refine ⟨12254002972309936211671045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 65354682518986326462245573 12254002972309936211671045)
                ·
                  refine ⟨2297625557308113039688321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12254002972309936211671045 2297625557308113039688321)
                  ·
                    refine ⟨1723219167981084779766241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2297625557308113039688321 1723219167981084779766241)
                    ·
                      refine ⟨1292414375985813584824681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1723219167981084779766241 1292414375985813584824681)
                      ·
                        rfl

theorem cell23_2516968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 4, 4, 2, 2].length) (baseStart_2516968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2516968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2516968 prefixEnd_2516968 := by exact prefixLift 2516968
  have htrace : WordTrace (prefixWord ++ tailWord_2516968) baseStart_2516968 baseEnd_2516968 := by
    simpa [prefixWord, tailWord_2516968, baseEnd_2516968] using wordTrace_append hprefix tailTrace_2516968
  have hstable : (prefixWord ++ tailWord_2516968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2516968).length < 2 ^ (prefixWord ++ tailWord_2516968).sum := by decide
  have hdescent : baseEnd_2516968 < baseStart_2516968 := by decide
  rcases family_descends (prefixWord ++ tailWord_2516968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2516985 : List Nat := [1, 2, 1, 3, 1, 4, 3, 2, 2, 2, 2]
def baseStart_2516985 : Nat := 118140960795 + 2516985 * 2 ^ 59
def prefixEnd_2516985 : Nat := 4983230072969 + 3 ^ 40 * 2516985 * 2
def baseEnd_2516985 : Nat := 1292423105156940018312103

theorem tailTrace_2516985 : CollatzResearch.WordTrace tailWord_2516985 prefixEnd_2516985 1292423105156940018312103 := by
  unfold tailWord_2516985
  simp only [CollatzResearch.WordTrace]
  refine ⟨91801984786400686659664409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61201323190933791106442939 91801984786400686659664409)
  ·
    refine ⟨68851488589800514994748307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91801984786400686659664409 68851488589800514994748307)
    ·
      refine ⟨103277232884700772492122461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68851488589800514994748307 103277232884700772492122461)
      ·
        refine ⟨38728962331762789684545923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103277232884700772492122461 38728962331762789684545923)
        ·
          refine ⟨58093443497644184526818885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38728962331762789684545923 58093443497644184526818885)
          ·
            refine ⟨10892520655808284598778541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58093443497644184526818885 10892520655808284598778541)
            ·
              refine ⟨4084695245928106724541953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10892520655808284598778541 4084695245928106724541953)
              ·
                refine ⟨3063521434446080043406465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4084695245928106724541953 3063521434446080043406465)
                ·
                  refine ⟨2297641075834560032554849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3063521434446080043406465 2297641075834560032554849)
                  ·
                    refine ⟨1723230806875920024416137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2297641075834560032554849 1723230806875920024416137)
                    ·
                      refine ⟨1292423105156940018312103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1723230806875920024416137 1292423105156940018312103)
                      ·
                        rfl

theorem cell23_2516985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 3, 2, 2, 2, 2].length) (baseStart_2516985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2516985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2516985 prefixEnd_2516985 := by exact prefixLift 2516985
  have htrace : WordTrace (prefixWord ++ tailWord_2516985) baseStart_2516985 baseEnd_2516985 := by
    simpa [prefixWord, tailWord_2516985, baseEnd_2516985] using wordTrace_append hprefix tailTrace_2516985
  have hstable : (prefixWord ++ tailWord_2516985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2516985).length < 2 ^ (prefixWord ++ tailWord_2516985).sum := by decide
  have hdescent : baseEnd_2516985 < baseStart_2516985 := by decide
  rcases family_descends (prefixWord ++ tailWord_2516985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2517002 : List Nat := [3, 1, 2, 2, 5, 1, 1, 1, 1, 4, 2]
def baseStart_2517002 : Nat := 118140960795 + 2517002 * 2 ^ 59
def prefixEnd_2517002 : Nat := 4983230072969 + 3 ^ 40 * 2517002 * 2
def baseEnd_2517002 : Nat := 1292431834328066451799525

theorem tailTrace_2517002 : CollatzResearch.WordTrace tailWord_2517002 prefixEnd_2517002 1292431834328066451799525 := by
  unfold tailWord_2517002
  simp only [CollatzResearch.WordTrace]
  refine ⟨22950651206834774640758315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61201736551559399042022173 22950651206834774640758315)
  ·
    refine ⟨34425976810252161961137473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22950651206834774640758315 34425976810252161961137473)
    ·
      refine ⟨25819482607689121470853105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34425976810252161961137473 25819482607689121470853105)
      ·
        refine ⟨19364611955766841103139829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25819482607689121470853105 19364611955766841103139829)
        ·
          refine ⟨1815432370853141353419359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19364611955766841103139829 1815432370853141353419359)
          ·
            refine ⟨2723148556279712030129039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1815432370853141353419359 2723148556279712030129039)
            ·
              refine ⟨4084722834419568045193559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2723148556279712030129039 4084722834419568045193559)
              ·
                refine ⟨6127084251629352067790339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4084722834419568045193559 6127084251629352067790339)
                ·
                  refine ⟨9190626377444028101685509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6127084251629352067790339 9190626377444028101685509)
                  ·
                    refine ⟨1723242445770755269066033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9190626377444028101685509 1723242445770755269066033)
                    ·
                      refine ⟨1292431834328066451799525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1723242445770755269066033 1292431834328066451799525)
                      ·
                        rfl

theorem cell23_2517002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 1, 1, 1, 4, 2].length) (baseStart_2517002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2517002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2517002 prefixEnd_2517002 := by exact prefixLift 2517002
  have htrace : WordTrace (prefixWord ++ tailWord_2517002) baseStart_2517002 baseEnd_2517002 := by
    simpa [prefixWord, tailWord_2517002, baseEnd_2517002] using wordTrace_append hprefix tailTrace_2517002
  have hstable : (prefixWord ++ tailWord_2517002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2517002).length < 2 ^ (prefixWord ++ tailWord_2517002).sum := by decide
  have hdescent : baseEnd_2517002 < baseStart_2517002 := by decide
  rcases family_descends (prefixWord ++ tailWord_2517002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2517004 : List Nat := [2, 2, 1, 2, 3, 1, 1, 1, 3, 7]
def baseStart_2517004 : Nat := 118140960795 + 2517004 * 2 ^ 59
def prefixEnd_2517004 : Nat := 4983230072969 + 3 ^ 40 * 2517004 * 2
def baseEnd_2517004 : Nat := 430810953763125147991505

theorem tailTrace_2517004 : CollatzResearch.WordTrace tailWord_2517004 prefixEnd_2517004 430810953763125147991505 := by
  unfold tailWord_2517004
  simp only [CollatzResearch.WordTrace]
  refine ⟨45901338886665926452303033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61201785182221235269737377 45901338886665926452303033)
  ·
    refine ⟨34426004164999444839227275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45901338886665926452303033 34426004164999444839227275)
    ·
      refine ⟨51639006247499167258840913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34426004164999444839227275 51639006247499167258840913)
      ·
        refine ⟨38729254685624375444130685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51639006247499167258840913 38729254685624375444130685)
        ·
          refine ⟨14523470507109140791549007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38729254685624375444130685 14523470507109140791549007)
          ·
            refine ⟨21785205760663711187323511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14523470507109140791549007 21785205760663711187323511)
            ·
              refine ⟨32677808640995566780985267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21785205760663711187323511 32677808640995566780985267)
              ·
                refine ⟨49016712961493350171477901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32677808640995566780985267 49016712961493350171477901)
                ·
                  refine ⟨18381267360560006314304213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49016712961493350171477901 18381267360560006314304213)
                  ·
                    refine ⟨430810953763125147991505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18381267360560006314304213 430810953763125147991505)
                    ·
                      rfl

theorem cell23_2517004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 1, 3, 7].length) (baseStart_2517004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2517004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2517004 prefixEnd_2517004 := by exact prefixLift 2517004
  have htrace : WordTrace (prefixWord ++ tailWord_2517004) baseStart_2517004 baseEnd_2517004 := by
    simpa [prefixWord, tailWord_2517004, baseEnd_2517004] using wordTrace_append hprefix tailTrace_2517004
  have hstable : (prefixWord ++ tailWord_2517004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2517004).length < 2 ^ (prefixWord ++ tailWord_2517004).sum := by decide
  have hdescent : baseEnd_2517004 < baseStart_2517004 := by decide
  rcases family_descends (prefixWord ++ tailWord_2517004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2517011 : List Nat := [1, 1, 1, 2, 1, 4, 2, 2, 2, 5, 2]
def baseStart_2517011 : Nat := 118140960795 + 2517011 * 2 ^ 59
def prefixEnd_2517011 : Nat := 4983230072969 + 3 ^ 40 * 2517011 * 2
def baseEnd_2517011 : Nat := 1292436455653956916586983

theorem tailTrace_2517011 : CollatzResearch.WordTrace tailWord_2517011 prefixEnd_2517011 1292436455653956916586983 := by
  unfold tailWord_2517011
  simp only [CollatzResearch.WordTrace]
  refine ⟨91802933084306493100110887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61201955389537662066740591 91802933084306493100110887)
  ·
    refine ⟨137704399626459739650166331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91802933084306493100110887 137704399626459739650166331)
    ·
      refine ⟨206556599439689609475249497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137704399626459739650166331 206556599439689609475249497)
      ·
        refine ⟨154917449579767207106437123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 206556599439689609475249497 154917449579767207106437123)
        ·
          refine ⟨232376174369650810659655685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154917449579767207106437123 232376174369650810659655685)
          ·
            refine ⟨43570532694309526998685441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 232376174369650810659655685 43570532694309526998685441)
            ·
              refine ⟨32677899520732145249014081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43570532694309526998685441 32677899520732145249014081)
              ·
                refine ⟨24508424640549108936760561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32677899520732145249014081 24508424640549108936760561)
                ·
                  refine ⟨18381318480411831702570421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24508424640549108936760561 18381318480411831702570421)
                  ·
                    refine ⟨1723248607538609222115977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18381318480411831702570421 1723248607538609222115977)
                    ·
                      refine ⟨1292436455653956916586983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1723248607538609222115977 1292436455653956916586983)
                      ·
                        rfl

theorem cell23_2517011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 2, 2, 5, 2].length) (baseStart_2517011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2517011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2517011 prefixEnd_2517011 := by exact prefixLift 2517011
  have htrace : WordTrace (prefixWord ++ tailWord_2517011) baseStart_2517011 baseEnd_2517011 := by
    simpa [prefixWord, tailWord_2517011, baseEnd_2517011] using wordTrace_append hprefix tailTrace_2517011
  have hstable : (prefixWord ++ tailWord_2517011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2517011).length < 2 ^ (prefixWord ++ tailWord_2517011).sum := by decide
  have hdescent : baseEnd_2517011 < baseStart_2517011 := by decide
  rcases family_descends (prefixWord ++ tailWord_2517011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2517021 : List Nat := [1, 4, 2, 2, 2, 1, 2, 1, 1, 7]
def baseStart_2517021 : Nat := 118140960795 + 2517021 * 2 ^ 59
def prefixEnd_2517021 : Nat := 4983230072969 + 3 ^ 40 * 2517021 * 2
def baseEnd_2517021 : Nat := 430813863486833959153979

theorem tailTrace_2517021 : CollatzResearch.WordTrace tailWord_2517021 prefixEnd_2517021 430813863486833959153979 := by
  unfold tailWord_2517021
  simp only [CollatzResearch.WordTrace]
  refine ⟨91803297814270264807974917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61202198542846843205316611 91803297814270264807974917)
  ·
    refine ⟨17213118340175674651495297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 91803297814270264807974917 17213118340175674651495297)
    ·
      refine ⟨12909838755131755988621473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17213118340175674651495297 12909838755131755988621473)
      ·
        refine ⟨9682379066348816991466105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12909838755131755988621473 9682379066348816991466105)
        ·
          refine ⟨7261784299761612743599579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9682379066348816991466105 7261784299761612743599579)
          ·
            refine ⟨10892676449642419115399369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7261784299761612743599579 10892676449642419115399369)
            ·
              refine ⟨8169507337231814336549527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10892676449642419115399369 8169507337231814336549527)
              ·
                refine ⟨12254261005847721504824291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8169507337231814336549527 12254261005847721504824291)
                ·
                  refine ⟨18381391508771582257236437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12254261005847721504824291 18381391508771582257236437)
                  ·
                    refine ⟨430813863486833959153979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18381391508771582257236437 430813863486833959153979)
                    ·
                      rfl

theorem cell23_2517021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 1, 1, 7].length) (baseStart_2517021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2517021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2517021 prefixEnd_2517021 := by exact prefixLift 2517021
  have htrace : WordTrace (prefixWord ++ tailWord_2517021) baseStart_2517021 baseEnd_2517021 := by
    simpa [prefixWord, tailWord_2517021, baseEnd_2517021] using wordTrace_append hprefix tailTrace_2517021
  have hstable : (prefixWord ++ tailWord_2517021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2517021).length < 2 ^ (prefixWord ++ tailWord_2517021).sum := by decide
  have hdescent : baseEnd_2517021 < baseStart_2517021 := by decide
  rcases family_descends (prefixWord ++ tailWord_2517021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2517025 : List Nat := [1, 2, 3, 2, 4, 2, 1, 3, 5]
def baseStart_2517025 : Nat := 118140960795 + 2517025 * 2 ^ 59
def prefixEnd_2517025 : Nat := 4983230072969 + 3 ^ 40 * 2517025 * 2
def baseEnd_2517025 : Nat := 143604849375902206867991

theorem tailTrace_2517025 : CollatzResearch.WordTrace tailWord_2517025 prefixEnd_2517025 143604849375902206867991 := by
  unfold tailWord_2517025
  simp only [CollatzResearch.WordTrace]
  refine ⟨91803443706255773491120529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61202295804170515660747019 91803443706255773491120529)
  ·
    refine ⟨68852582779691830118340397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91803443706255773491120529 68852582779691830118340397)
    ·
      refine ⟨25819718542384436294377649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68852582779691830118340397 25819718542384436294377649)
      ·
        refine ⟨19364788906788327220783237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25819718542384436294377649 19364788906788327220783237)
        ·
          refine ⟨3630897920022811353896857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19364788906788327220783237 3630897920022811353896857)
          ·
            refine ⟨2723173440017108515422643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3630897920022811353896857 2723173440017108515422643)
            ·
              refine ⟨4084760160025662773133965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2723173440017108515422643 4084760160025662773133965)
              ·
                refine ⟨1531785060009623539925237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4084760160025662773133965 1531785060009623539925237)
                ·
                  refine ⟨143604849375902206867991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1531785060009623539925237 143604849375902206867991)
                  ·
                    rfl

theorem cell23_2517025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 1, 3, 5].length) (baseStart_2517025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2517025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2517025 prefixEnd_2517025 := by exact prefixLift 2517025
  have htrace : WordTrace (prefixWord ++ tailWord_2517025) baseStart_2517025 baseEnd_2517025 := by
    simpa [prefixWord, tailWord_2517025, baseEnd_2517025] using wordTrace_append hprefix tailTrace_2517025
  have hstable : (prefixWord ++ tailWord_2517025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2517025).length < 2 ^ (prefixWord ++ tailWord_2517025).sum := by decide
  have hdescent : baseEnd_2517025 < baseStart_2517025 := by decide
  rcases family_descends (prefixWord ++ tailWord_2517025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2517038 : List Nat := [4, 1, 3, 1, 1, 3, 1, 2, 2, 5]
def baseStart_2517038 : Nat := 118140960795 + 2517038 * 2 ^ 59
def prefixEnd_2517038 : Nat := 4983230072969 + 3 ^ 40 * 2517038 * 2
def baseEnd_2517038 : Nat := 430816773210542770316453

theorem tailTrace_2517038 : CollatzResearch.WordTrace tailWord_2517038 prefixEnd_2517038 430816773210542770316453 := by
  unfold tailWord_2517038
  simp only [CollatzResearch.WordTrace]
  refine ⟨11475489731901084588917971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61202611903472451140895845 11475489731901084588917971)
  ·
    refine ⟨17213234597851626883376957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11475489731901084588917971 17213234597851626883376957)
    ·
      refine ⟨6454962974194360081266359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17213234597851626883376957 6454962974194360081266359)
      ·
        refine ⟨9682444461291540121899539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6454962974194360081266359 9682444461291540121899539)
        ·
          refine ⟨14523666691937310182849309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9682444461291540121899539 14523666691937310182849309)
          ·
            refine ⟨5446375009476491318568491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14523666691937310182849309 5446375009476491318568491)
            ·
              refine ⟨8169562514214736977852737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5446375009476491318568491 8169562514214736977852737)
              ·
                refine ⟨6127171885661052733389553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8169562514214736977852737 6127171885661052733389553)
                ·
                  refine ⟨4595378914245789550042165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6127171885661052733389553 4595378914245789550042165)
                  ·
                    refine ⟨430816773210542770316453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4595378914245789550042165 430816773210542770316453)
                    ·
                      rfl

theorem cell23_2517038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 2, 2, 5].length) (baseStart_2517038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2517038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2517038 prefixEnd_2517038 := by exact prefixLift 2517038
  have htrace : WordTrace (prefixWord ++ tailWord_2517038) baseStart_2517038 baseEnd_2517038 := by
    simpa [prefixWord, tailWord_2517038, baseEnd_2517038] using wordTrace_append hprefix tailTrace_2517038
  have hstable : (prefixWord ++ tailWord_2517038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2517038).length < 2 ^ (prefixWord ++ tailWord_2517038).sum := by decide
  have hdescent : baseEnd_2517038 < baseStart_2517038 := by decide
  rcases family_descends (prefixWord ++ tailWord_2517038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2517041 : List Nat := [1, 2, 2, 3, 1, 3, 1, 1, 4, 1, 4]
def baseStart_2517041 : Nat := 118140960795 + 2517041 * 2 ^ 59
def prefixEnd_2517041 : Nat := 4983230072969 + 3 ^ 40 * 2517041 * 2
def baseEnd_2517041 : Nat := 1292451860073591799211845

theorem tailTrace_2517041 : CollatzResearch.WordTrace tailWord_2517041 prefixEnd_2517041 1292451860073591799211845 := by
  unfold tailWord_2517041
  simp only [CollatzResearch.WordTrace]
  refine ⟨91804027274197808223702977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61202684849465205482468651 91804027274197808223702977)
  ·
    refine ⟨68853020455648356167777233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91804027274197808223702977 68853020455648356167777233)
    ·
      refine ⟨51639765341736267125832925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68853020455648356167777233 51639765341736267125832925)
      ·
        refine ⟨19364912003151100172187347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51639765341736267125832925 19364912003151100172187347)
        ·
          refine ⟨29047368004726650258281021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19364912003151100172187347 29047368004726650258281021)
          ·
            refine ⟨10892763001772493846855383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29047368004726650258281021 10892763001772493846855383)
            ·
              refine ⟨16339144502658740770283075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10892763001772493846855383 16339144502658740770283075)
              ·
                refine ⟨24508716753988111155424613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16339144502658740770283075 24508716753988111155424613)
                ·
                  refine ⟨4595384391372770841642115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24508716753988111155424613 4595384391372770841642115)
                  ·
                    refine ⟨6893076587059156262463173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4595384391372770841642115 6893076587059156262463173)
                    ·
                      refine ⟨1292451860073591799211845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6893076587059156262463173 1292451860073591799211845)
                      ·
                        rfl

theorem cell23_2517041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 1, 4, 1, 4].length) (baseStart_2517041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2517041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2517041 prefixEnd_2517041 := by exact prefixLift 2517041
  have htrace : WordTrace (prefixWord ++ tailWord_2517041) baseStart_2517041 baseEnd_2517041 := by
    simpa [prefixWord, tailWord_2517041, baseEnd_2517041] using wordTrace_append hprefix tailTrace_2517041
  have hstable : (prefixWord ++ tailWord_2517041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2517041).length < 2 ^ (prefixWord ++ tailWord_2517041).sum := by decide
  have hdescent : baseEnd_2517041 < baseStart_2517041 := by decide
  rcases family_descends (prefixWord ++ tailWord_2517041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2517061 : List Nat := [1, 3, 1, 1, 1, 3, 1, 1, 6, 2, 3]
def baseStart_2517061 : Nat := 118140960795 + 2517061 * 2 ^ 59
def prefixEnd_2517061 : Nat := 4983230072969 + 3 ^ 40 * 2517061 * 2
def baseEnd_2517061 : Nat := 1292462129686681720961753

theorem tailTrace_2517061 : CollatzResearch.WordTrace tailWord_2517061 prefixEnd_2517061 1292462129686681720961753 := by
  unfold tailWord_2517061
  simp only [CollatzResearch.WordTrace]
  refine ⟨91804756734125351639431037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61203171156083567759620691 91804756734125351639431037)
  ·
    refine ⟨34426783775297006864786639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91804756734125351639431037 34426783775297006864786639)
    ·
      refine ⟨51640175662945510297179959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34426783775297006864786639 51640175662945510297179959)
      ·
        refine ⟨77460263494418265445769939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51640175662945510297179959 77460263494418265445769939)
        ·
          refine ⟨116190395241627398168654909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77460263494418265445769939 116190395241627398168654909)
          ·
            refine ⟨43571398215610274313245591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 116190395241627398168654909 43571398215610274313245591)
            ·
              refine ⟨65357097323415411469868387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43571398215610274313245591 65357097323415411469868387)
              ·
                refine ⟨98035645985123117204802581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65357097323415411469868387 98035645985123117204802581)
                ·
                  refine ⟨4595420905552646118975121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 98035645985123117204802581 4595420905552646118975121)
                  ·
                    refine ⟨3446565679164484589231341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4595420905552646118975121 3446565679164484589231341)
                    ·
                      refine ⟨1292462129686681720961753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3446565679164484589231341 1292462129686681720961753)
                      ·
                        rfl

theorem cell23_2517061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 6, 2, 3].length) (baseStart_2517061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2517061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2517061 prefixEnd_2517061 := by exact prefixLift 2517061
  have htrace : WordTrace (prefixWord ++ tailWord_2517061) baseStart_2517061 baseEnd_2517061 := by
    simpa [prefixWord, tailWord_2517061, baseEnd_2517061] using wordTrace_append hprefix tailTrace_2517061
  have hstable : (prefixWord ++ tailWord_2517061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2517061).length < 2 ^ (prefixWord ++ tailWord_2517061).sum := by decide
  have hdescent : baseEnd_2517061 < baseStart_2517061 := by decide
  rcases family_descends (prefixWord ++ tailWord_2517061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2517064 : List Nat := [2, 1, 3, 1, 1, 1, 2, 2, 10]
def baseStart_2517064 : Nat := 118140960795 + 2517064 * 2 ^ 59
def prefixEnd_2517064 : Nat := 4983230072969 + 3 ^ 40 * 2517064 * 2
def baseEnd_2517064 : Nat := 143607074458738356580471

theorem tailTrace_2517064 : CollatzResearch.WordTrace tailWord_2517064 prefixEnd_2517064 143607074458738356580471 := by
  unfold tailWord_2517064
  simp only [CollatzResearch.WordTrace]
  refine ⟨45902433076557241575895123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61203244102076322101193497 45902433076557241575895123)
  ·
    refine ⟨68853649614835862363842685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45902433076557241575895123 68853649614835862363842685)
    ·
      refine ⟨25820118605563448386441007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68853649614835862363842685 25820118605563448386441007)
      ·
        refine ⟨38730177908345172579661511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25820118605563448386441007 38730177908345172579661511)
        ·
          refine ⟨58095266862517758869492267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38730177908345172579661511 58095266862517758869492267)
          ·
            refine ⟨87142900293776638304238401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58095266862517758869492267 87142900293776638304238401)
            ·
              refine ⟨65357175220332478728178801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87142900293776638304238401 65357175220332478728178801)
              ·
                refine ⟨49017881415249359046134101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65357175220332478728178801 49017881415249359046134101)
                ·
                  refine ⟨143607074458738356580471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 49017881415249359046134101 143607074458738356580471)
                  ·
                    rfl

theorem cell23_2517064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 2, 10].length) (baseStart_2517064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2517064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2517064 prefixEnd_2517064 := by exact prefixLift 2517064
  have htrace : WordTrace (prefixWord ++ tailWord_2517064) baseStart_2517064 baseEnd_2517064 := by
    simpa [prefixWord, tailWord_2517064, baseEnd_2517064] using wordTrace_append hprefix tailTrace_2517064
  have hstable : (prefixWord ++ tailWord_2517064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2517064).length < 2 ^ (prefixWord ++ tailWord_2517064).sum := by decide
  have hdescent : baseEnd_2517064 < baseStart_2517064 := by decide
  rcases family_descends (prefixWord ++ tailWord_2517064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2517101 : List Nat := [1, 5, 1, 1, 2, 1, 2, 1, 1, 2, 6]
def baseStart_2517101 : Nat := 118140960795 + 2517101 * 2 ^ 59
def prefixEnd_2517101 : Nat := 4983230072969 + 3 ^ 40 * 2517101 * 2
def baseEnd_2517101 : Nat := 1292482668912861564461569

theorem tailTrace_2517101 : CollatzResearch.WordTrace tailWord_2517101 prefixEnd_2517101 1292482668912861564461569 := by
  unfold tailWord_2517101
  simp only [CollatzResearch.WordTrace]
  refine ⟨91806215653980438470887157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61204143769320292313924771 91806215653980438470887157)
  ·
    refine ⟨8606832717560666106645671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 91806215653980438470887157 8606832717560666106645671)
    ·
      refine ⟨12910249076340999159968507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8606832717560666106645671 12910249076340999159968507)
      ·
        refine ⟨19365373614511498739952761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12910249076340999159968507 19365373614511498739952761)
        ·
          refine ⟨14524030210883624054964571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19365373614511498739952761 14524030210883624054964571)
          ·
            refine ⟨21786045316325436082446857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14524030210883624054964571 21786045316325436082446857)
            ·
              refine ⟨16339533987244077061835143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21786045316325436082446857 16339533987244077061835143)
              ·
                refine ⟨24509300980866115592752715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16339533987244077061835143 24509300980866115592752715)
                ·
                  refine ⟨36763951471299173389129073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24509300980866115592752715 36763951471299173389129073)
                  ·
                    refine ⟨27572963603474380041846805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36763951471299173389129073 27572963603474380041846805)
                    ·
                      refine ⟨1292482668912861564461569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27572963603474380041846805 1292482668912861564461569)
                      ·
                        rfl

theorem cell23_2517101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 1, 1, 2, 6].length) (baseStart_2517101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2517101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2517101 prefixEnd_2517101 := by exact prefixLift 2517101
  have htrace : WordTrace (prefixWord ++ tailWord_2517101) baseStart_2517101 baseEnd_2517101 := by
    simpa [prefixWord, tailWord_2517101, baseEnd_2517101] using wordTrace_append hprefix tailTrace_2517101
  have hstable : (prefixWord ++ tailWord_2517101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2517101).length < 2 ^ (prefixWord ++ tailWord_2517101).sum := by decide
  have hdescent : baseEnd_2517101 < baseStart_2517101 := by decide
  rcases family_descends (prefixWord ++ tailWord_2517101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2517111 : List Nat := [1, 1, 3, 1, 1, 5, 1, 2, 3, 5]
def baseStart_2517111 : Nat := 118140960795 + 2517111 * 2 ^ 59
def prefixEnd_2517111 : Nat := 4983230072969 + 3 ^ 40 * 2517111 * 2
def baseEnd_2517111 : Nat := 430829267906468841778841

theorem tailTrace_2517111 : CollatzResearch.WordTrace tailWord_2517111 prefixEnd_2517111 430829267906468841778841 := by
  unfold tailWord_2517111
  simp only [CollatzResearch.WordTrace]
  refine ⟨91806580383944210178751187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61204386922629473452500791 91806580383944210178751187)
  ·
    refine ⟨137709870575916315268126781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91806580383944210178751187 137709870575916315268126781)
    ·
      refine ⟨51641201465968618225547543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137709870575916315268126781 51641201465968618225547543)
      ·
        refine ⟨77461802198952927338321315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51641201465968618225547543 77461802198952927338321315)
        ·
          refine ⟨116192703298429391007481973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77461802198952927338321315 116192703298429391007481973)
          ·
            refine ⟨10893065934227755406951435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 116192703298429391007481973 10893065934227755406951435)
            ·
              refine ⟨16339598901341633110427153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10893065934227755406951435 16339598901341633110427153)
              ·
                refine ⟨12254699176006224832820365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16339598901341633110427153 12254699176006224832820365)
                ·
                  refine ⟨4595512191002334312307637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12254699176006224832820365 4595512191002334312307637)
                  ·
                    refine ⟨430829267906468841778841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4595512191002334312307637 430829267906468841778841)
                    ·
                      rfl

theorem cell23_2517111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 2, 3, 5].length) (baseStart_2517111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2517111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2517111 prefixEnd_2517111 := by exact prefixLift 2517111
  have htrace : WordTrace (prefixWord ++ tailWord_2517111) baseStart_2517111 baseEnd_2517111 := by
    simpa [prefixWord, tailWord_2517111, baseEnd_2517111] using wordTrace_append hprefix tailTrace_2517111
  have hstable : (prefixWord ++ tailWord_2517111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2517111).length < 2 ^ (prefixWord ++ tailWord_2517111).sum := by decide
  have hdescent : baseEnd_2517111 < baseStart_2517111 := by decide
  rcases family_descends (prefixWord ++ tailWord_2517111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2517125 : List Nat := [1, 3, 1, 1, 5, 2, 1, 2, 3, 1, 3]
def baseStart_2517125 : Nat := 118140960795 + 2517125 * 2 ^ 59
def prefixEnd_2517125 : Nat := 4983230072969 + 3 ^ 40 * 2517125 * 2
def baseEnd_2517125 : Nat := 1292494992448569470561459

theorem tailTrace_2517125 : CollatzResearch.WordTrace tailWord_2517125 prefixEnd_2517125 1292494992448569470561459 := by
  unfold tailWord_2517125
  simp only [CollatzResearch.WordTrace]
  refine ⟨91807091005893490569760829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61204727337262327046507219 91807091005893490569760829)
  ·
    refine ⟨34427659127210058963660311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91807091005893490569760829 34427659127210058963660311)
    ·
      refine ⟨51641488690815088445490467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34427659127210058963660311 51641488690815088445490467)
      ·
        refine ⟨77462233036222632668235701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51641488690815088445490467 77462233036222632668235701)
        ·
          refine ⟨7262084347145871812647097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 77462233036222632668235701 7262084347145871812647097)
          ·
            refine ⟨5446563260359403859485323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7262084347145871812647097 5446563260359403859485323)
            ·
              refine ⟨8169844890539105789227985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5446563260359403859485323 8169844890539105789227985)
              ·
                refine ⟨6127383667904329341920989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8169844890539105789227985 6127383667904329341920989)
                ·
                  refine ⟨2297768875464123503220371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6127383667904329341920989 2297768875464123503220371)
                  ·
                    refine ⟨3446653313196185254830557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2297768875464123503220371 3446653313196185254830557)
                    ·
                      refine ⟨1292494992448569470561459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3446653313196185254830557 1292494992448569470561459)
                      ·
                        rfl

theorem cell23_2517125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 2, 3, 1, 3].length) (baseStart_2517125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2517125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2517125 prefixEnd_2517125 := by exact prefixLift 2517125
  have htrace : WordTrace (prefixWord ++ tailWord_2517125) baseStart_2517125 baseEnd_2517125 := by
    simpa [prefixWord, tailWord_2517125, baseEnd_2517125] using wordTrace_append hprefix tailTrace_2517125
  have hstable : (prefixWord ++ tailWord_2517125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2517125).length < 2 ^ (prefixWord ++ tailWord_2517125).sum := by decide
  have hdescent : baseEnd_2517125 < baseStart_2517125 := by decide
  rcases family_descends (prefixWord ++ tailWord_2517125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2517128 : List Nat := [2, 1, 3, 4, 1, 1, 2, 1, 3, 5]
def baseStart_2517128 : Nat := 118140960795 + 2517128 * 2 ^ 59
def prefixEnd_2517128 : Nat := 4983230072969 + 3 ^ 40 * 2517128 * 2
def baseEnd_2517128 : Nat := 430832177630177652941315

theorem tailTrace_2517128 : CollatzResearch.WordTrace tailWord_2517128 prefixEnd_2517128 430832177630177652941315 := by
  unfold tailWord_2517128
  simp only [CollatzResearch.WordTrace]
  refine ⟨45903600212441311041060019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61204800283255081388080025 45903600212441311041060019)
  ·
    refine ⟨68855400318661966561590029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45903600212441311041060019 68855400318661966561590029)
    ·
      refine ⟨25820775119498237460596261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68855400318661966561590029 25820775119498237460596261)
      ·
        refine ⟨4841395334905919523861799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25820775119498237460596261 4841395334905919523861799)
        ·
          refine ⟨7262093002358879285792699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4841395334905919523861799 7262093002358879285792699)
          ·
            refine ⟨10893139503538318928689049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7262093002358879285792699 10893139503538318928689049)
            ·
              refine ⟨8169854627653739196516787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10893139503538318928689049 8169854627653739196516787)
              ·
                refine ⟨12254781941480608794775181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8169854627653739196516787 12254781941480608794775181)
                ·
                  refine ⟨4595543228055228298040693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12254781941480608794775181 4595543228055228298040693)
                  ·
                    refine ⟨430832177630177652941315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4595543228055228298040693 430832177630177652941315)
                    ·
                      rfl

theorem cell23_2517128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 1, 3, 5].length) (baseStart_2517128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2517128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2517128 prefixEnd_2517128 := by exact prefixLift 2517128
  have htrace : WordTrace (prefixWord ++ tailWord_2517128) baseStart_2517128 baseEnd_2517128 := by
    simpa [prefixWord, tailWord_2517128, baseEnd_2517128] using wordTrace_append hprefix tailTrace_2517128
  have hstable : (prefixWord ++ tailWord_2517128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2517128).length < 2 ^ (prefixWord ++ tailWord_2517128).sum := by decide
  have hdescent : baseEnd_2517128 < baseStart_2517128 := by decide
  rcases family_descends (prefixWord ++ tailWord_2517128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2517141 : List Nat := [1, 3, 2, 1, 1, 1, 3, 4, 1, 6]
def baseStart_2517141 : Nat := 118140960795 + 2517141 * 2 ^ 59
def prefixEnd_2517141 : Nat := 4983230072969 + 3 ^ 40 * 2517141 * 2
def baseEnd_2517141 : Nat := 430834402713013802653795

theorem tailTrace_2517141 : CollatzResearch.WordTrace tailWord_2517141 prefixEnd_2517141 430834402713013802653795 := by
  unfold tailWord_2517141
  simp only [CollatzResearch.WordTrace]
  refine ⟨91807674573835525302343277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61205116382557016868228851 91807674573835525302343277)
  ·
    refine ⟨34427877965188321988378729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91807674573835525302343277 34427877965188321988378729)
    ·
      refine ⟨25820908473891241491284047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34427877965188321988378729 25820908473891241491284047)
      ·
        refine ⟨38731362710836862236926071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25820908473891241491284047 38731362710836862236926071)
        ·
          refine ⟨58097044066255293355389107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38731362710836862236926071 58097044066255293355389107)
          ·
            refine ⟨87145566099382940033083661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58097044066255293355389107 87145566099382940033083661)
            ·
              refine ⟨32679587287268602512406373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 87145566099382940033083661 32679587287268602512406373)
              ·
                refine ⟨6127422616362862971076195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32679587287268602512406373 6127422616362862971076195)
                ·
                  refine ⟨9191133924544294456614293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6127422616362862971076195 9191133924544294456614293)
                  ·
                    refine ⟨430834402713013802653795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9191133924544294456614293 430834402713013802653795)
                    ·
                      rfl

theorem cell23_2517141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 4, 1, 6].length) (baseStart_2517141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2517141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2517141 prefixEnd_2517141 := by exact prefixLift 2517141
  have htrace : WordTrace (prefixWord ++ tailWord_2517141) baseStart_2517141 baseEnd_2517141 := by
    simpa [prefixWord, tailWord_2517141, baseEnd_2517141] using wordTrace_append hprefix tailTrace_2517141
  have hstable : (prefixWord ++ tailWord_2517141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2517141).length < 2 ^ (prefixWord ++ tailWord_2517141).sum := by decide
  have hdescent : baseEnd_2517141 < baseStart_2517141 := by decide
  rcases family_descends (prefixWord ++ tailWord_2517141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2517178 : List Nat := [3, 1, 1, 1, 2, 2, 5, 1, 1, 2, 4]
def baseStart_2517178 : Nat := 118140960795 + 2517178 * 2 ^ 59
def prefixEnd_2517178 : Nat := 4983230072969 + 3 ^ 40 * 2517178 * 2
def baseEnd_2517178 : Nat := 1292522206923257763198715

theorem tailTrace_2517178 : CollatzResearch.WordTrace tailWord_2517178 prefixEnd_2517178 1292522206923257763198715 := by
  unfold tailWord_2517178
  simp only [CollatzResearch.WordTrace]
  refine ⟨22952256018675370155360047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61206016049800987080960125 22952256018675370155360047)
  ·
    refine ⟨34428384028013055233040071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22952256018675370155360047 34428384028013055233040071)
    ·
      refine ⟨51642576042019582849560107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34428384028013055233040071 51642576042019582849560107)
      ·
        refine ⟨77463864063029374274340161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51642576042019582849560107 77463864063029374274340161)
        ·
          refine ⟨58097898047272030705755121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77463864063029374274340161 58097898047272030705755121)
          ·
            refine ⟨43573423535454023029316341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58097898047272030705755121 43573423535454023029316341)
            ·
              refine ⟨4085008456448814658998407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43573423535454023029316341 4085008456448814658998407)
              ·
                refine ⟨6127512684673221988497611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4085008456448814658998407 6127512684673221988497611)
                ·
                  refine ⟨9191269027009832982746417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6127512684673221988497611 9191269027009832982746417)
                  ·
                    refine ⟨6893451770257374737059813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9191269027009832982746417 6893451770257374737059813)
                    ·
                      refine ⟨1292522206923257763198715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6893451770257374737059813 1292522206923257763198715)
                      ·
                        rfl

theorem cell23_2517178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 5, 1, 1, 2, 4].length) (baseStart_2517178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2517178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2517178 prefixEnd_2517178 := by exact prefixLift 2517178
  have htrace : WordTrace (prefixWord ++ tailWord_2517178) baseStart_2517178 baseEnd_2517178 := by
    simpa [prefixWord, tailWord_2517178, baseEnd_2517178] using wordTrace_append hprefix tailTrace_2517178
  have hstable : (prefixWord ++ tailWord_2517178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2517178).length < 2 ^ (prefixWord ++ tailWord_2517178).sum := by decide
  have hdescent : baseEnd_2517178 < baseStart_2517178 := by decide
  rcases family_descends (prefixWord ++ tailWord_2517178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2517182 : List Nat := [4, 2, 1, 1, 4, 1, 2, 2, 1, 1, 4]
def baseStart_2517182 : Nat := 118140960795 + 2517182 * 2 ^ 59
def prefixEnd_2517182 : Nat := 4983230072969 + 3 ^ 40 * 2517182 * 2
def baseEnd_2517182 : Nat := 1292524260845875747548697

theorem tailTrace_2517182 : CollatzResearch.WordTrace tailWord_2517182 prefixEnd_2517182 1292524260845875747548697 := by
  unfold tailWord_2517182
  simp only [CollatzResearch.WordTrace]
  refine ⟨11476146245835873663073225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61206113311124659536390533 11476146245835873663073225)
  ·
    refine ⟨8607109684376905247304919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11476146245835873663073225 8607109684376905247304919)
    ·
      refine ⟨12910664526565357870957379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8607109684376905247304919 12910664526565357870957379)
      ·
        refine ⟨19365996789848036806436069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12910664526565357870957379 19365996789848036806436069)
        ·
          refine ⟨3631124398096506901206763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19365996789848036806436069 3631124398096506901206763)
          ·
            refine ⟨5446686597144760351810145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3631124398096506901206763 5446686597144760351810145)
            ·
              refine ⟨4085014947858570263857609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5446686597144760351810145 4085014947858570263857609)
              ·
                refine ⟨3063761210893927697893207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4085014947858570263857609 3063761210893927697893207)
                ·
                  refine ⟨4595641816340891546839811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3063761210893927697893207 4595641816340891546839811)
                  ·
                    refine ⟨6893462724511337320259717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4595641816340891546839811 6893462724511337320259717)
                    ·
                      refine ⟨1292524260845875747548697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6893462724511337320259717 1292524260845875747548697)
                      ·
                        rfl

theorem cell23_2517182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 2, 2, 1, 1, 4].length) (baseStart_2517182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2517182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2517182 prefixEnd_2517182 := by exact prefixLift 2517182
  have htrace : WordTrace (prefixWord ++ tailWord_2517182) baseStart_2517182 baseEnd_2517182 := by
    simpa [prefixWord, tailWord_2517182, baseEnd_2517182] using wordTrace_append hprefix tailTrace_2517182
  have hstable : (prefixWord ++ tailWord_2517182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2517182).length < 2 ^ (prefixWord ++ tailWord_2517182).sum := by decide
  have hdescent : baseEnd_2517182 < baseStart_2517182 := by decide
  rcases family_descends (prefixWord ++ tailWord_2517182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2517188 : List Nat := [2, 3, 3, 1, 2, 2, 1, 9]
def baseStart_2517188 : Nat := 118140960795 + 2517188 * 2 ^ 59
def prefixEnd_2517188 : Nat := 4983230072969 + 3 ^ 40 * 2517188 * 2
def baseEnd_2517188 : Nat := 47871383027029730521247

theorem tailTrace_2517188 : CollatzResearch.WordTrace tailWord_2517188 prefixEnd_2517188 47871383027029730521247 := by
  unfold tailWord_2517188
  simp only [CollatzResearch.WordTrace]
  refine ⟨45904694402332626164652109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61206259203110168219536145 45904694402332626164652109)
  ·
    refine ⟨17214260400874734811744541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45904694402332626164652109 17214260400874734811744541)
    ·
      refine ⟨6455347650328025554404203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17214260400874734811744541 6455347650328025554404203)
      ·
        refine ⟨9683021475492038331606305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6455347650328025554404203 9683021475492038331606305)
        ·
          refine ⟨7262266106619028748704729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9683021475492038331606305 7262266106619028748704729)
          ·
            refine ⟨5446699579964271561528547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7262266106619028748704729 5446699579964271561528547)
            ·
              refine ⟨8170049369946407342292821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5446699579964271561528547 8170049369946407342292821)
              ·
                refine ⟨47871383027029730521247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8170049369946407342292821 47871383027029730521247)
                ·
                  rfl

theorem cell23_2517188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 9].length) (baseStart_2517188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2517188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2517188 prefixEnd_2517188 := by exact prefixLift 2517188
  have htrace : WordTrace (prefixWord ++ tailWord_2517188) baseStart_2517188 baseEnd_2517188 := by
    simpa [prefixWord, tailWord_2517188, baseEnd_2517188] using wordTrace_append hprefix tailTrace_2517188
  have hstable : (prefixWord ++ tailWord_2517188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2517188).length < 2 ^ (prefixWord ++ tailWord_2517188).sum := by decide
  have hdescent : baseEnd_2517188 < baseStart_2517188 := by decide
  rcases family_descends (prefixWord ++ tailWord_2517188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2517205 : List Nat := [1, 3, 2, 4, 3, 1, 9]
def baseStart_2517205 : Nat := 118140960795 + 2517205 * 2 ^ 59
def prefixEnd_2517205 : Nat := 4983230072969 + 3 ^ 40 * 2517205 * 2
def baseEnd_2517205 : Nat := 15957235443221347624211

theorem tailTrace_2517205 : CollatzResearch.WordTrace tailWord_2517205 prefixEnd_2517205 15957235443221347624211 := by
  unfold tailWord_2517205
  simp only [CollatzResearch.WordTrace]
  refine ⟨91810008845603664232673069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61206672563735776155115379 91810008845603664232673069)
  ·
    refine ⟨34428753317101374087252401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91810008845603664232673069 34428753317101374087252401)
    ·
      refine ⟨25821564987826030565439301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34428753317101374087252401 25821564987826030565439301)
      ·
        refine ⟨4841543435217380731019869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25821564987826030565439301 4841543435217380731019869)
        ·
          refine ⟨1815578788206517774132451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4841543435217380731019869 1815578788206517774132451)
          ·
            refine ⟨2723368182309776661198677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1815578788206517774132451 2723368182309776661198677)
            ·
              refine ⟨15957235443221347624211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2723368182309776661198677 15957235443221347624211)
              ·
                rfl

theorem cell23_2517205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 9].length) (baseStart_2517205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2517205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2517205 prefixEnd_2517205 := by exact prefixLift 2517205
  have htrace : WordTrace (prefixWord ++ tailWord_2517205) baseStart_2517205 baseEnd_2517205 := by
    simpa [prefixWord, tailWord_2517205, baseEnd_2517205] using wordTrace_append hprefix tailTrace_2517205
  have hstable : (prefixWord ++ tailWord_2517205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2517205).length < 2 ^ (prefixWord ++ tailWord_2517205).sum := by decide
  have hdescent : baseEnd_2517205 < baseStart_2517205 := by decide
  rcases family_descends (prefixWord ++ tailWord_2517205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2517215 : List Nat := [1, 1, 2, 3, 2, 1, 1, 6, 2, 1, 3]
def baseStart_2517215 : Nat := 118140960795 + 2517215 * 2 ^ 59
def prefixEnd_2517215 : Nat := 4983230072969 + 3 ^ 40 * 2517215 * 2
def baseEnd_2517215 : Nat := 1292541205707474118436045

theorem tailTrace_2517215 : CollatzResearch.WordTrace tailWord_2517215 prefixEnd_2517215 1292541205707474118436045 := by
  unfold tailWord_2517215
  simp only [CollatzResearch.WordTrace]
  refine ⟨91810373575567435940537099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61206915717044957293691399 91810373575567435940537099)
  ·
    refine ⟨137715560363351153910805649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91810373575567435940537099 137715560363351153910805649)
    ·
      refine ⟨103286670272513365433104237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137715560363351153910805649 103286670272513365433104237)
      ·
        refine ⟨38732501352192512037414089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103286670272513365433104237 38732501352192512037414089)
        ·
          refine ⟨29049376014144384028060567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38732501352192512037414089 29049376014144384028060567)
          ·
            refine ⟨43574064021216576042090851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29049376014144384028060567 43574064021216576042090851)
            ·
              refine ⟨65361096031824864063136277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43574064021216576042090851 65361096031824864063136277)
              ·
                refine ⟨3063801376491790502959513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 65361096031824864063136277 3063801376491790502959513)
                ·
                  refine ⟨2297851032368842877219635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3063801376491790502959513 2297851032368842877219635)
                  ·
                    refine ⟨3446776548553264315829453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2297851032368842877219635 3446776548553264315829453)
                    ·
                      refine ⟨1292541205707474118436045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3446776548553264315829453 1292541205707474118436045)
                      ·
                        rfl

theorem cell23_2517215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 6, 2, 1, 3].length) (baseStart_2517215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2517215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2517215 prefixEnd_2517215 := by exact prefixLift 2517215
  have htrace : WordTrace (prefixWord ++ tailWord_2517215) baseStart_2517215 baseEnd_2517215 := by
    simpa [prefixWord, tailWord_2517215, baseEnd_2517215] using wordTrace_append hprefix tailTrace_2517215
  have hstable : (prefixWord ++ tailWord_2517215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2517215).length < 2 ^ (prefixWord ++ tailWord_2517215).sum := by decide
  have hdescent : baseEnd_2517215 < baseStart_2517215 := by decide
  rcases family_descends (prefixWord ++ tailWord_2517215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2517242 : List Nat := [3, 1, 1, 1, 1, 5, 3, 2, 1, 3, 2]
def baseStart_2517242 : Nat := 118140960795 + 2517242 * 2 ^ 59
def prefixEnd_2517242 : Nat := 4983230072969 + 3 ^ 40 * 2517242 * 2
def baseEnd_2517242 : Nat := 1292555069685145512798421

theorem tailTrace_2517242 : CollatzResearch.WordTrace tailWord_2517242 prefixEnd_2517242 1292555069685145512798421 := by
  unfold tailWord_2517242
  simp only [CollatzResearch.WordTrace]
  refine ⟨22952839586617404887942495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61207572230979746367846653 22952839586617404887942495)
  ·
    refine ⟨34429259379926107331913743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22952839586617404887942495 34429259379926107331913743)
    ·
      refine ⟨51643889069889160997870615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34429259379926107331913743 51643889069889160997870615)
      ·
        refine ⟨77465833604833741496805923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51643889069889160997870615 77465833604833741496805923)
        ·
          refine ⟨116198750407250612245208885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77465833604833741496805923 116198750407250612245208885)
          ·
            refine ⟨10893632850679744897988333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 116198750407250612245208885 10893632850679744897988333)
            ·
              refine ⟨4085112319004904336745625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10893632850679744897988333 4085112319004904336745625)
              ·
                refine ⟨3063834239253678252559219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4085112319004904336745625 3063834239253678252559219)
                ·
                  refine ⟨4595751358880517378838829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3063834239253678252559219 4595751358880517378838829)
                  ·
                    refine ⟨1723406759580194017064561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4595751358880517378838829 1723406759580194017064561)
                    ·
                      refine ⟨1292555069685145512798421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1723406759580194017064561 1292555069685145512798421)
                      ·
                        rfl

theorem cell23_2517242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 3, 2, 1, 3, 2].length) (baseStart_2517242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2517242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2517242 prefixEnd_2517242 := by exact prefixLift 2517242
  have htrace : WordTrace (prefixWord ++ tailWord_2517242) baseStart_2517242 baseEnd_2517242 := by
    simpa [prefixWord, tailWord_2517242, baseEnd_2517242] using wordTrace_append hprefix tailTrace_2517242
  have hstable : (prefixWord ++ tailWord_2517242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2517242).length < 2 ^ (prefixWord ++ tailWord_2517242).sum := by decide
  have hdescent : baseEnd_2517242 < baseStart_2517242 := by decide
  rcases family_descends (prefixWord ++ tailWord_2517242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2517258 : List Nat := [3, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5]
def baseStart_2517258 : Nat := 118140960795 + 2517258 * 2 ^ 59
def prefixEnd_2517258 : Nat := 4983230072969 + 3 ^ 40 * 2517258 * 2
def baseEnd_2517258 : Nat := 1292563285375617450198347

theorem tailTrace_2517258 : CollatzResearch.WordTrace tailWord_2517258 prefixEnd_2517258 1292563285375617450198347 := by
  unfold tailWord_2517258
  simp only [CollatzResearch.WordTrace]
  refine ⟨22952985478602913571088107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61207961276274436189568285 22952985478602913571088107)
  ·
    refine ⟨34429478217904370356632161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22952985478602913571088107 34429478217904370356632161)
    ·
      refine ⟨25822108663428277767474121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34429478217904370356632161 25822108663428277767474121)
      ·
        refine ⟨19366581497571208325605591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25822108663428277767474121 19366581497571208325605591)
        ·
          refine ⟨29049872246356812488408387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19366581497571208325605591 29049872246356812488408387)
          ·
            refine ⟨43574808369535218732612581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29049872246356812488408387 43574808369535218732612581)
            ·
              refine ⟨8170276569287853512364859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43574808369535218732612581 8170276569287853512364859)
              ·
                refine ⟨12255414853931780268547289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8170276569287853512364859 12255414853931780268547289)
                ·
                  refine ⟨9191561140448835201410467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12255414853931780268547289 9191561140448835201410467)
                  ·
                    refine ⟨13787341710673252802115701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9191561140448835201410467 13787341710673252802115701)
                    ·
                      refine ⟨1292563285375617450198347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13787341710673252802115701 1292563285375617450198347)
                      ·
                        rfl

theorem cell23_2517258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5].length) (baseStart_2517258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2517258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2517258 prefixEnd_2517258 := by exact prefixLift 2517258
  have htrace : WordTrace (prefixWord ++ tailWord_2517258) baseStart_2517258 baseEnd_2517258 := by
    simpa [prefixWord, tailWord_2517258, baseEnd_2517258] using wordTrace_append hprefix tailTrace_2517258
  have hstable : (prefixWord ++ tailWord_2517258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2517258).length < 2 ^ (prefixWord ++ tailWord_2517258).sum := by decide
  have hdescent : baseEnd_2517258 < baseStart_2517258 := by decide
  rcases family_descends (prefixWord ++ tailWord_2517258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2517285 : List Nat := [1, 3, 1, 2, 5, 1, 1, 1, 2, 2, 4]
def baseStart_2517285 : Nat := 118140960795 + 2517285 * 2 ^ 59
def prefixEnd_2517285 : Nat := 4983230072969 + 3 ^ 40 * 2517285 * 2
def baseEnd_2517285 : Nat := 1292577149353288844560723

theorem tailTrace_2517285 : CollatzResearch.WordTrace tailWord_2517285 prefixEnd_2517285 1292577149353288844560723 := by
  unfold tailWord_2517285
  simp only [CollatzResearch.WordTrace]
  refine ⟨91812926685313837895585309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61208617790209225263723539 91812926685313837895585309)
  ·
    refine ⟨34429847506992689210844491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91812926685313837895585309 34429847506992689210844491)
    ·
      refine ⟨51644771260489033816266737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34429847506992689210844491 51644771260489033816266737)
      ·
        refine ⟨38733578445366775362200053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51644771260489033816266737 38733578445366775362200053)
        ·
          refine ⟨3631272979253135190206255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38733578445366775362200053 3631272979253135190206255)
          ·
            refine ⟨5446909468879702785309383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3631272979253135190206255 5446909468879702785309383)
            ·
              refine ⟨8170364203319554177964075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5446909468879702785309383 8170364203319554177964075)
              ·
                refine ⟨12255546304979331266946113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8170364203319554177964075 12255546304979331266946113)
                ·
                  refine ⟨9191659728734498450209585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12255546304979331266946113 9191659728734498450209585)
                  ·
                    refine ⟨6893744796550873837657189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9191659728734498450209585 6893744796550873837657189)
                    ·
                      refine ⟨1292577149353288844560723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6893744796550873837657189 1292577149353288844560723)
                      ·
                        rfl

theorem cell23_2517285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 1, 2, 2, 4].length) (baseStart_2517285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2517285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2517285 prefixEnd_2517285 := by exact prefixLift 2517285
  have htrace : WordTrace (prefixWord ++ tailWord_2517285) baseStart_2517285 baseEnd_2517285 := by
    simpa [prefixWord, tailWord_2517285, baseEnd_2517285] using wordTrace_append hprefix tailTrace_2517285
  have hstable : (prefixWord ++ tailWord_2517285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2517285).length < 2 ^ (prefixWord ++ tailWord_2517285).sum := by decide
  have hdescent : baseEnd_2517285 < baseStart_2517285 := by decide
  rcases family_descends (prefixWord ++ tailWord_2517285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2517308 : List Nat := [2, 2, 2, 2, 1, 2, 3, 1, 1, 7]
def baseStart_2517308 : Nat := 118140960795 + 2517308 * 2 ^ 59
def prefixEnd_2517308 : Nat := 4983230072969 + 3 ^ 40 * 2517308 * 2
def baseEnd_2517308 : Nat := 430862986469447418191039

theorem tailTrace_2517308 : CollatzResearch.WordTrace tailWord_2517308 prefixEnd_2517308 430862986469447418191039 := by
  unfold tailWord_2517308
  simp only [CollatzResearch.WordTrace]
  refine ⟨45906882782115256411836289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61209177042820341882448385 45906882782115256411836289)
  ·
    refine ⟨34430162086586442308877217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45906882782115256411836289 34430162086586442308877217)
    ·
      refine ⟨25822621564939831731657913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34430162086586442308877217 25822621564939831731657913)
      ·
        refine ⟨19366966173704873798743435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25822621564939831731657913 19366966173704873798743435)
        ·
          refine ⟨29050449260557310698115153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19366966173704873798743435 29050449260557310698115153)
          ·
            refine ⟨21787836945417983023586365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29050449260557310698115153 21787836945417983023586365)
            ·
              refine ⟨8170438854531743633844887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21787836945417983023586365 8170438854531743633844887)
              ·
                refine ⟨12255658281797615450767331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8170438854531743633844887 12255658281797615450767331)
                ·
                  refine ⟨18383487422696423176150997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12255658281797615450767331 18383487422696423176150997)
                  ·
                    refine ⟨430862986469447418191039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18383487422696423176150997 430862986469447418191039)
                    ·
                      rfl

theorem cell23_2517308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 1, 1, 7].length) (baseStart_2517308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2517308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2517308 prefixEnd_2517308 := by exact prefixLift 2517308
  have htrace : WordTrace (prefixWord ++ tailWord_2517308) baseStart_2517308 baseEnd_2517308 := by
    simpa [prefixWord, tailWord_2517308, baseEnd_2517308] using wordTrace_append hprefix tailTrace_2517308
  have hstable : (prefixWord ++ tailWord_2517308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2517308).length < 2 ^ (prefixWord ++ tailWord_2517308).sum := by decide
  have hdescent : baseEnd_2517308 < baseStart_2517308 := by decide
  rcases family_descends (prefixWord ++ tailWord_2517308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2517372 : List Nat := [2, 2, 2, 1, 1, 1, 2, 7, 1, 4]
def baseStart_2517372 : Nat := 118140960795 + 2517372 * 2 ^ 59
def prefixEnd_2517372 : Nat := 4983230072969 + 3 ^ 40 * 2517372 * 2
def baseEnd_2517372 : Nat := 430873940723410001390941

theorem tailTrace_2517372 : CollatzResearch.WordTrace tailWord_2517372 prefixEnd_2517372 430873940723410001390941 := by
  unfold tailWord_2517372
  simp only [CollatzResearch.WordTrace]
  refine ⟨45908049917999325877001185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61210733223999101169334913 45908049917999325877001185)
  ·
    refine ⟨34431037438499494407750889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45908049917999325877001185 34431037438499494407750889)
    ·
      refine ⟨25823278078874620805813167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34431037438499494407750889 25823278078874620805813167)
      ·
        refine ⟨38734917118311931208719751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25823278078874620805813167 38734917118311931208719751)
        ·
          refine ⟨58102375677467896813079627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38734917118311931208719751 58102375677467896813079627)
          ·
            refine ⟨87153563516201845219619441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58102375677467896813079627 87153563516201845219619441)
            ·
              refine ⟨65365172637151383914714581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87153563516201845219619441 65365172637151383914714581)
              ·
                refine ⟨1531996233683235560501123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 65365172637151383914714581 1531996233683235560501123)
                ·
                  refine ⟨2297994350524853340751685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1531996233683235560501123 2297994350524853340751685)
                  ·
                    refine ⟨430873940723410001390941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2297994350524853340751685 430873940723410001390941)
                    ·
                      rfl

theorem cell23_2517372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 7, 1, 4].length) (baseStart_2517372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2517372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2517372 prefixEnd_2517372 := by exact prefixLift 2517372
  have htrace : WordTrace (prefixWord ++ tailWord_2517372) baseStart_2517372 baseEnd_2517372 := by
    simpa [prefixWord, tailWord_2517372, baseEnd_2517372] using wordTrace_append hprefix tailTrace_2517372
  have hstable : (prefixWord ++ tailWord_2517372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2517372).length < 2 ^ (prefixWord ++ tailWord_2517372).sum := by decide
  have hdescent : baseEnd_2517372 < baseStart_2517372 := by decide
  rcases family_descends (prefixWord ++ tailWord_2517372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2517402 : List Nat := [3, 1, 1, 4, 1, 2, 4, 1, 6]
def baseStart_2517402 : Nat := 118140960795 + 2517402 * 2 ^ 59
def prefixEnd_2517402 : Nat := 4983230072969 + 3 ^ 40 * 2517402 * 2
def baseEnd_2517402 : Nat := 143626358509984987421965

theorem tailTrace_2517402 : CollatzResearch.WordTrace tailWord_2517402 prefixEnd_2517402 143626358509984987421965 := by
  unfold tailWord_2517402
  simp only [CollatzResearch.WordTrace]
  refine ⟨22954298506472491719398615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61211462683926644585062973 22954298506472491719398615)
  ·
    refine ⟨34431447759708737579097923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22954298506472491719398615 34431447759708737579097923)
    ·
      refine ⟨51647171639563106368646885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34431447759708737579097923 51647171639563106368646885)
      ·
        refine ⟨9683844682418082444121291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51647171639563106368646885 9683844682418082444121291)
        ·
          refine ⟨14525767023627123666181937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9683844682418082444121291 14525767023627123666181937)
          ·
            refine ⟨10894325267720342749636453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14525767023627123666181937 10894325267720342749636453)
            ·
              refine ⟨2042685987697564265556835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10894325267720342749636453 2042685987697564265556835)
              ·
                refine ⟨3064028981546346398335253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2042685987697564265556835 3064028981546346398335253)
                ·
                  refine ⟨143626358509984987421965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3064028981546346398335253 143626358509984987421965)
                  ·
                    rfl

theorem cell23_2517402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 4, 1, 6].length) (baseStart_2517402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2517402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2517402 prefixEnd_2517402 := by exact prefixLift 2517402
  have htrace : WordTrace (prefixWord ++ tailWord_2517402) baseStart_2517402 baseEnd_2517402 := by
    simpa [prefixWord, tailWord_2517402, baseEnd_2517402] using wordTrace_append hprefix tailTrace_2517402
  have hstable : (prefixWord ++ tailWord_2517402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2517402).length < 2 ^ (prefixWord ++ tailWord_2517402).sum := by decide
  have hdescent : baseEnd_2517402 < baseStart_2517402 := by decide
  rcases family_descends (prefixWord ++ tailWord_2517402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2517412 : List Nat := [2, 3, 1, 2, 1, 1, 2, 4, 3, 1, 3]
def baseStart_2517412 : Nat := 118140960795 + 2517412 * 2 ^ 59
def prefixEnd_2517412 : Nat := 4983230072969 + 3 ^ 40 * 2517412 * 2
def baseEnd_2517412 : Nat := 1292642361396409847672639

theorem tailTrace_2517412 : CollatzResearch.WordTrace tailWord_2517412 prefixEnd_2517412 1292642361396409847672639 := by
  unfold tailWord_2517412
  simp only [CollatzResearch.WordTrace]
  refine ⟨45908779377926869292729245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61211705837235825723638993 45908779377926869292729245)
  ·
    refine ⟨17215792266722575984773467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45908779377926869292729245 17215792266722575984773467)
    ·
      refine ⟨25823688400083863977160201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17215792266722575984773467 25823688400083863977160201)
      ·
        refine ⟨19367766300062897982870151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25823688400083863977160201 19367766300062897982870151)
        ·
          refine ⟨29051649450094346974305227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19367766300062897982870151 29051649450094346974305227)
          ·
            refine ⟨43577474175141520461457841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29051649450094346974305227 43577474175141520461457841)
            ·
              refine ⟨32683105631356140346093381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43577474175141520461457841 32683105631356140346093381)
              ·
                refine ⟨6128082305879276314892509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32683105631356140346093381 6128082305879276314892509)
                ·
                  refine ⟨2298030864704728618084691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6128082305879276314892509 2298030864704728618084691)
                  ·
                    refine ⟨3447046297057092927127037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2298030864704728618084691 3447046297057092927127037)
                    ·
                      refine ⟨1292642361396409847672639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3447046297057092927127037 1292642361396409847672639)
                      ·
                        rfl

theorem cell23_2517412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 4, 3, 1, 3].length) (baseStart_2517412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2517412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2517412 prefixEnd_2517412 := by exact prefixLift 2517412
  have htrace : WordTrace (prefixWord ++ tailWord_2517412) baseStart_2517412 baseEnd_2517412 := by
    simpa [prefixWord, tailWord_2517412, baseEnd_2517412] using wordTrace_append hprefix tailTrace_2517412
  have hstable : (prefixWord ++ tailWord_2517412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2517412).length < 2 ^ (prefixWord ++ tailWord_2517412).sum := by decide
  have hdescent : baseEnd_2517412 < baseStart_2517412 := by decide
  rcases family_descends (prefixWord ++ tailWord_2517412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2517435 : List Nat := [1, 1, 1, 1, 1, 2, 2, 1, 3, 8, 2]
def baseStart_2517435 : Nat := 118140960795 + 2517435 * 2 ^ 59
def prefixEnd_2517435 : Nat := 4983230072969 + 3 ^ 40 * 2517435 * 2
def baseEnd_2517435 : Nat := 1292654171451463257685033

theorem tailTrace_2517435 : CollatzResearch.WordTrace tailWord_2517435 prefixEnd_2517435 1292654171451463257685033 := by
  unfold tailWord_2517435
  simp only [CollatzResearch.WordTrace]
  refine ⟨91818397634770413513545759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61212265089846942342363839 91818397634770413513545759)
  ·
    refine ⟨137727596452155620270318639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91818397634770413513545759 137727596452155620270318639)
    ·
      refine ⟨206591394678233430405477959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137727596452155620270318639 206591394678233430405477959)
      ·
        refine ⟨309887092017350145608216939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206591394678233430405477959 309887092017350145608216939)
        ·
          refine ⟨464830638026025218412325409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 309887092017350145608216939 464830638026025218412325409)
          ·
            refine ⟨348622978519518913809244057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 464830638026025218412325409 348622978519518913809244057)
            ·
              refine ⟨261467233889639185356933043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 348622978519518913809244057 261467233889639185356933043)
              ·
                refine ⟨392200850834458778035399565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 261467233889639185356933043 392200850834458778035399565)
                ·
                  refine ⟨147075319062922041763274837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 392200850834458778035399565 147075319062922041763274837)
                  ·
                    refine ⟨1723538895268617676913377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 147075319062922041763274837 1723538895268617676913377)
                    ·
                      refine ⟨1292654171451463257685033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1723538895268617676913377 1292654171451463257685033)
                      ·
                        rfl

theorem cell23_2517435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 8, 2].length) (baseStart_2517435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2517435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2517435 prefixEnd_2517435 := by exact prefixLift 2517435
  have htrace : WordTrace (prefixWord ++ tailWord_2517435) baseStart_2517435 baseEnd_2517435 := by
    simpa [prefixWord, tailWord_2517435, baseEnd_2517435] using wordTrace_append hprefix tailTrace_2517435
  have hstable : (prefixWord ++ tailWord_2517435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2517435).length < 2 ^ (prefixWord ++ tailWord_2517435).sum := by decide
  have hdescent : baseEnd_2517435 < baseStart_2517435 := by decide
  rcases family_descends (prefixWord ++ tailWord_2517435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2517472 : List Nat := [2, 1, 1, 3, 1, 1, 4, 4, 1, 2, 3]
def baseStart_2517472 : Nat := 118140960795 + 2517472 * 2 ^ 59
def prefixEnd_2517472 : Nat := 4983230072969 + 3 ^ 40 * 2517472 * 2
def baseEnd_2517472 : Nat := 1292673170235679612922363

theorem tailTrace_2517472 : CollatzResearch.WordTrace tailWord_2517472 prefixEnd_2517472 1292673170235679612922363 := by
  unfold tailWord_2517472
  simp only [CollatzResearch.WordTrace]
  refine ⟨45909873567818184416321335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61213164757090912555095113 45909873567818184416321335)
  ·
    refine ⟨68864810351727276624482003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45909873567818184416321335 68864810351727276624482003)
    ·
      refine ⟨103297215527590914936723005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68864810351727276624482003 103297215527590914936723005)
      ·
        refine ⟨38736455822846593101271127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103297215527590914936723005 38736455822846593101271127)
        ·
          refine ⟨58104683734269889651906691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38736455822846593101271127 58104683734269889651906691)
          ·
            refine ⟨87157025601404834477860037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58104683734269889651906691 87157025601404834477860037)
            ·
              refine ⟨16341942300263406464598757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 87157025601404834477860037 16341942300263406464598757)
              ·
                refine ⟨3064114181299388712112267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16341942300263406464598757 3064114181299388712112267)
                ·
                  refine ⟨4596171271949083068168401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3064114181299388712112267 4596171271949083068168401)
                  ·
                    refine ⟨3447128453961812301126301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4596171271949083068168401 3447128453961812301126301)
                    ·
                      refine ⟨1292673170235679612922363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3447128453961812301126301 1292673170235679612922363)
                      ·
                        rfl

theorem cell23_2517472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 4, 1, 2, 3].length) (baseStart_2517472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2517472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2517472 prefixEnd_2517472 := by exact prefixLift 2517472
  have htrace : WordTrace (prefixWord ++ tailWord_2517472) baseStart_2517472 baseEnd_2517472 := by
    simpa [prefixWord, tailWord_2517472, baseEnd_2517472] using wordTrace_append hprefix tailTrace_2517472
  have hstable : (prefixWord ++ tailWord_2517472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2517472).length < 2 ^ (prefixWord ++ tailWord_2517472).sum := by decide
  have hdescent : baseEnd_2517472 < baseStart_2517472 := by decide
  rcases family_descends (prefixWord ++ tailWord_2517472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2517482 : List Nat := [3, 1, 3, 1, 3, 1, 2, 2, 1, 2, 4]
def baseStart_2517482 : Nat := 118140960795 + 2517482 * 2 ^ 59
def prefixEnd_2517482 : Nat := 4983230072969 + 3 ^ 40 * 2517482 * 2
def baseEnd_2517482 : Nat := 1292678305042224573797317

theorem tailTrace_2517482 : CollatzResearch.WordTrace tailWord_2517482 prefixEnd_2517482 1292678305042224573797317 := by
  unfold tailWord_2517482
  simp only [CollatzResearch.WordTrace]
  refine ⟨22955027966400035135126675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61213407910400093693671133 22955027966400035135126675)
  ·
    refine ⟨34432541949600052702690013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22955027966400035135126675 34432541949600052702690013)
    ·
      refine ⟨12912203231100019763508755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34432541949600052702690013 12912203231100019763508755)
      ·
        refine ⟨19368304846650029645263133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12912203231100019763508755 19368304846650029645263133)
        ·
          refine ⟨7263114317493761116973675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19368304846650029645263133 7263114317493761116973675)
          ·
            refine ⟨10894671476240641675460513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7263114317493761116973675 10894671476240641675460513)
            ·
              refine ⟨8171003607180481256595385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10894671476240641675460513 8171003607180481256595385)
              ·
                refine ⟨6128252705385360942446539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8171003607180481256595385 6128252705385360942446539)
                ·
                  refine ⟨9192379058078041413669809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6128252705385360942446539 9192379058078041413669809)
                  ·
                    refine ⟨6894284293558531060252357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9192379058078041413669809 6894284293558531060252357)
                    ·
                      refine ⟨1292678305042224573797317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6894284293558531060252357 1292678305042224573797317)
                      ·
                        rfl

theorem cell23_2517482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 2, 1, 2, 4].length) (baseStart_2517482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2517482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2517482 prefixEnd_2517482 := by exact prefixLift 2517482
  have htrace : WordTrace (prefixWord ++ tailWord_2517482) baseStart_2517482 baseEnd_2517482 := by
    simpa [prefixWord, tailWord_2517482, baseEnd_2517482] using wordTrace_append hprefix tailTrace_2517482
  have hstable : (prefixWord ++ tailWord_2517482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2517482).length < 2 ^ (prefixWord ++ tailWord_2517482).sum := by decide
  have hdescent : baseEnd_2517482 < baseStart_2517482 := by decide
  rcases family_descends (prefixWord ++ tailWord_2517482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2517486 : List Nat := [4, 1, 2, 1, 2, 4, 2, 1, 1, 1, 4]
def baseStart_2517486 : Nat := 118140960795 + 2517486 * 2 ^ 59
def prefixEnd_2517486 : Nat := 4983230072969 + 3 ^ 40 * 2517486 * 2
def baseEnd_2517486 : Nat := 1292680358964842558147299

theorem tailTrace_2517486 : CollatzResearch.WordTrace tailWord_2517486 prefixEnd_2517486 1292680358964842558147299 := by
  unfold tailWord_2517486
  simp only [CollatzResearch.WordTrace]
  refine ⟨11477532219698206152956539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61213505171723766149101541 11477532219698206152956539)
  ·
    refine ⟨17216298329547309229434809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11477532219698206152956539 17216298329547309229434809)
    ·
      refine ⟨12912223747160481922076107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17216298329547309229434809 12912223747160481922076107)
      ·
        refine ⟨19368335620740722883114161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12912223747160481922076107 19368335620740722883114161)
        ·
          refine ⟨14526251715555542162335621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19368335620740722883114161 14526251715555542162335621)
          ·
            refine ⟨2723672196666664155437929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14526251715555542162335621 2723672196666664155437929)
            ·
              refine ⟨2042754147499998116578447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2723672196666664155437929 2042754147499998116578447)
              ·
                refine ⟨3064131221249997174867671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2042754147499998116578447 3064131221249997174867671)
                ·
                  refine ⟨4596196831874995762301507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3064131221249997174867671 4596196831874995762301507)
                  ·
                    refine ⟨6894295247812493643452261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4596196831874995762301507 6894295247812493643452261)
                    ·
                      refine ⟨1292680358964842558147299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6894295247812493643452261 1292680358964842558147299)
                      ·
                        rfl

theorem cell23_2517486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 2, 1, 1, 1, 4].length) (baseStart_2517486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2517486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2517486 prefixEnd_2517486 := by exact prefixLift 2517486
  have htrace : WordTrace (prefixWord ++ tailWord_2517486) baseStart_2517486 baseEnd_2517486 := by
    simpa [prefixWord, tailWord_2517486, baseEnd_2517486] using wordTrace_append hprefix tailTrace_2517486
  have hstable : (prefixWord ++ tailWord_2517486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2517486).length < 2 ^ (prefixWord ++ tailWord_2517486).sum := by decide
  have hdescent : baseEnd_2517486 < baseStart_2517486 := by decide
  rcases family_descends (prefixWord ++ tailWord_2517486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2517546 : List Nat := [3, 1, 4, 1, 1, 2, 2, 3, 1, 3, 2]
def baseStart_2517546 : Nat := 118140960795 + 2517546 * 2 ^ 59
def prefixEnd_2517546 : Nat := 4983230072969 + 3 ^ 40 * 2517546 * 2
def baseEnd_2517546 : Nat := 1292711167804112323397023

theorem tailTrace_2517546 : CollatzResearch.WordTrace tailWord_2517546 prefixEnd_2517546 1292711167804112323397023 := by
  unfold tailWord_2517546
  simp only [CollatzResearch.WordTrace]
  refine ⟨22955611534342069867709123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61214964091578852980557661 22955611534342069867709123)
  ·
    refine ⟨34433417301513104801563685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22955611534342069867709123 34433417301513104801563685)
    ·
      refine ⟨6456265744033707150293191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34433417301513104801563685 6456265744033707150293191)
      ·
        refine ⟨9684398616050560725439787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6456265744033707150293191 9684398616050560725439787)
        ·
          refine ⟨14526597924075841088159681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9684398616050560725439787 14526597924075841088159681)
          ·
            refine ⟨10894948443056880816119761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14526597924075841088159681 10894948443056880816119761)
            ·
              refine ⟨8171211332292660612089821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10894948443056880816119761 8171211332292660612089821)
              ·
                refine ⟨3064204249609747729533683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8171211332292660612089821 3064204249609747729533683)
                ·
                  refine ⟨4596306374414621594300525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3064204249609747729533683 4596306374414621594300525)
                  ·
                    refine ⟨1723614890405483097862697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4596306374414621594300525 1723614890405483097862697)
                    ·
                      refine ⟨1292711167804112323397023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1723614890405483097862697 1292711167804112323397023)
                      ·
                        rfl

theorem cell23_2517546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 3, 1, 3, 2].length) (baseStart_2517546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2517546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2517546 prefixEnd_2517546 := by exact prefixLift 2517546
  have htrace : WordTrace (prefixWord ++ tailWord_2517546) baseStart_2517546 baseEnd_2517546 := by
    simpa [prefixWord, tailWord_2517546, baseEnd_2517546] using wordTrace_append hprefix tailTrace_2517546
  have hstable : (prefixWord ++ tailWord_2517546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2517546).length < 2 ^ (prefixWord ++ tailWord_2517546).sum := by decide
  have hdescent : baseEnd_2517546 < baseStart_2517546 := by decide
  rcases family_descends (prefixWord ++ tailWord_2517546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2517559 : List Nat := [1, 1, 3, 1, 2, 3, 1, 3, 4, 2, 2]
def baseStart_2517559 : Nat := 118140960795 + 2517559 * 2 ^ 59
def prefixEnd_2517559 : Nat := 4983230072969 + 3 ^ 40 * 2517559 * 2
def baseEnd_2517559 : Nat := 1292717843052620772534463

theorem tailTrace_2517559 : CollatzResearch.WordTrace tailWord_2517559 prefixEnd_2517559 1292717843052620772534463 := by
  unfold tailWord_2517559
  simp only [CollatzResearch.WordTrace]
  refine ⟨91822920286321182691059731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61215280190880788460706487 91822920286321182691059731)
  ·
    refine ⟨137734380429481774036589597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91822920286321182691059731 137734380429481774036589597)
    ·
      refine ⟨51650392661055665263721099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137734380429481774036589597 51650392661055665263721099)
      ·
        refine ⟨77475588991583497895581649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51650392661055665263721099 77475588991583497895581649)
        ·
          refine ⟨58106691743687623421686237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77475588991583497895581649 58106691743687623421686237)
          ·
            refine ⟨21790009403882858783132339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58106691743687623421686237 21790009403882858783132339)
            ·
              refine ⟨32685014105824288174698509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21790009403882858783132339 32685014105824288174698509)
              ·
                refine ⟨12256880289684108065511941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32685014105824288174698509 12256880289684108065511941)
                ·
                  refine ⟨2298165054315770262283489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12256880289684108065511941 2298165054315770262283489)
                  ·
                    refine ⟨1723623790736827696712617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2298165054315770262283489 1723623790736827696712617)
                    ·
                      refine ⟨1292717843052620772534463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1723623790736827696712617 1292717843052620772534463)
                      ·
                        rfl

theorem cell23_2517559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 3, 4, 2, 2].length) (baseStart_2517559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2517559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2517559 prefixEnd_2517559 := by exact prefixLift 2517559
  have htrace : WordTrace (prefixWord ++ tailWord_2517559) baseStart_2517559 baseEnd_2517559 := by
    simpa [prefixWord, tailWord_2517559, baseEnd_2517559] using wordTrace_append hprefix tailTrace_2517559
  have hstable : (prefixWord ++ tailWord_2517559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2517559).length < 2 ^ (prefixWord ++ tailWord_2517559).sum := by decide
  have hdescent : baseEnd_2517559 < baseStart_2517559 := by decide
  rcases family_descends (prefixWord ++ tailWord_2517559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2517612 : List Nat := [2, 2, 1, 1, 3, 1, 4, 2, 2, 5]
def baseStart_2517612 : Nat := 118140960795 + 2517612 * 2 ^ 59
def prefixEnd_2517612 : Nat := 4983230072969 + 3 ^ 40 * 2517612 * 2
def baseEnd_2517612 : Nat := 430915019175769688390573

theorem tailTrace_2517612 : CollatzResearch.WordTrace tailWord_2517612 prefixEnd_2517612 430915019175769688390573 := by
  unfold tailWord_2517612
  simp only [CollatzResearch.WordTrace]
  refine ⟨45912426677564586371369545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61216568903419448495159393 45912426677564586371369545)
  ·
    refine ⟨34434320008173439778527159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45912426677564586371369545 34434320008173439778527159)
    ·
      refine ⟨51651480012260159667790739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34434320008173439778527159 51651480012260159667790739)
      ·
        refine ⟨77477220018390239501686109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51651480012260159667790739 77477220018390239501686109)
        ·
          refine ⟨29053957506896339813132291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77477220018390239501686109 29053957506896339813132291)
          ·
            refine ⟨43580936260344509719698437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29053957506896339813132291 43580936260344509719698437)
            ·
              refine ⟨8171425548814595572443457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43580936260344509719698437 8171425548814595572443457)
              ·
                refine ⟨6128569161610946679332593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8171425548814595572443457 6128569161610946679332593)
                ·
                  refine ⟨4596426871208210009499445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6128569161610946679332593 4596426871208210009499445)
                  ·
                    refine ⟨430915019175769688390573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4596426871208210009499445 430915019175769688390573)
                    ·
                      rfl

theorem cell23_2517612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 5].length) (baseStart_2517612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2517612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2517612 prefixEnd_2517612 := by exact prefixLift 2517612
  have htrace : WordTrace (prefixWord ++ tailWord_2517612) baseStart_2517612 baseEnd_2517612 := by
    simpa [prefixWord, tailWord_2517612, baseEnd_2517612] using wordTrace_append hprefix tailTrace_2517612
  have hstable : (prefixWord ++ tailWord_2517612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2517612).length < 2 ^ (prefixWord ++ tailWord_2517612).sum := by decide
  have hdescent : baseEnd_2517612 < baseStart_2517612 := by decide
  rcases family_descends (prefixWord ++ tailWord_2517612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2517692 : List Nat := [2, 2, 2, 3, 1, 1, 1, 2, 1, 2, 6]
def baseStart_2517692 : Nat := 118140960795 + 2517692 * 2 ^ 59
def prefixEnd_2517692 : Nat := 4983230072969 + 3 ^ 40 * 2517692 * 2
def baseEnd_2517692 : Nat := 1292786135979668752171351

theorem tailTrace_2517692 : CollatzResearch.WordTrace tailWord_2517692 prefixEnd_2517692 1292786135979668752171351 := by
  unfold tailWord_2517692
  simp only [CollatzResearch.WordTrace]
  refine ⟨45913885597419673202825665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61218514129892897603767553 45913885597419673202825665)
  ·
    refine ⟨34435414198064754902119249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45913885597419673202825665 34435414198064754902119249)
    ·
      refine ⟨25826560648548566176589437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34435414198064754902119249 25826560648548566176589437)
      ·
        refine ⟨9684960243205712316221039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25826560648548566176589437 9684960243205712316221039)
        ·
          refine ⟨14527440364808568474331559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9684960243205712316221039 14527440364808568474331559)
          ·
            refine ⟨21791160547212852711497339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14527440364808568474331559 21791160547212852711497339)
            ·
              refine ⟨32686740820819279067246009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21791160547212852711497339 32686740820819279067246009)
              ·
                refine ⟨24515055615614459300434507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32686740820819279067246009 24515055615614459300434507)
                ·
                  refine ⟨36772583423421688950651761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24515055615614459300434507 36772583423421688950651761)
                  ·
                    refine ⟨27579437567566266712988821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36772583423421688950651761 27579437567566266712988821)
                    ·
                      refine ⟨1292786135979668752171351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27579437567566266712988821 1292786135979668752171351)
                      ·
                        rfl

theorem cell23_2517692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_2517692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2517692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2517692 prefixEnd_2517692 := by exact prefixLift 2517692
  have htrace : WordTrace (prefixWord ++ tailWord_2517692) baseStart_2517692 baseEnd_2517692 := by
    simpa [prefixWord, tailWord_2517692, baseEnd_2517692] using wordTrace_append hprefix tailTrace_2517692
  have hstable : (prefixWord ++ tailWord_2517692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2517692).length < 2 ^ (prefixWord ++ tailWord_2517692).sum := by decide
  have hdescent : baseEnd_2517692 < baseStart_2517692 := by decide
  rcases family_descends (prefixWord ++ tailWord_2517692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2517719 : List Nat := [1, 1, 3, 2, 1, 4, 2, 3, 1, 5]
def baseStart_2517719 : Nat := 118140960795 + 2517719 * 2 ^ 59
def prefixEnd_2517719 : Nat := 4983230072969 + 3 ^ 40 * 2517719 * 2
def baseEnd_2517719 : Nat := 430933333319113382177909

theorem tailTrace_2517719 : CollatzResearch.WordTrace tailWord_2517719 prefixEnd_2517719 430933333319113382177909 := by
  unfold tailWord_2517719
  simp only [CollatzResearch.WordTrace]
  refine ⟨91828755965741530016884211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61219170643827686677922807 91828755965741530016884211)
  ·
    refine ⟨137743133948612295025326317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91828755965741530016884211 137743133948612295025326317)
    ·
      refine ⟨51653675230729610634497369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137743133948612295025326317 51653675230729610634497369)
      ·
        refine ⟨38740256423047207975873027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51653675230729610634497369 38740256423047207975873027)
        ·
          refine ⟨58110384634570811963809541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38740256423047207975873027 58110384634570811963809541)
          ·
            refine ⟨10895697118982027243214289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58110384634570811963809541 10895697118982027243214289)
            ·
              refine ⟨8171772839236520432410717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10895697118982027243214289 8171772839236520432410717)
              ·
                refine ⟨3064414814713695162154019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8171772839236520432410717 3064414814713695162154019)
                ·
                  refine ⟨4596622222070542743231029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3064414814713695162154019 4596622222070542743231029)
                  ·
                    refine ⟨430933333319113382177909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4596622222070542743231029 430933333319113382177909)
                    ·
                      rfl

theorem cell23_2517719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 3, 1, 5].length) (baseStart_2517719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2517719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2517719 prefixEnd_2517719 := by exact prefixLift 2517719
  have htrace : WordTrace (prefixWord ++ tailWord_2517719) baseStart_2517719 baseEnd_2517719 := by
    simpa [prefixWord, tailWord_2517719, baseEnd_2517719] using wordTrace_append hprefix tailTrace_2517719
  have hstable : (prefixWord ++ tailWord_2517719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2517719).length < 2 ^ (prefixWord ++ tailWord_2517719).sum := by decide
  have hdescent : baseEnd_2517719 < baseStart_2517719 := by decide
  rcases family_descends (prefixWord ++ tailWord_2517719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2517733 : List Nat := [1, 3, 1, 4, 1, 4, 1, 1, 3, 1, 3]
def baseStart_2517733 : Nat := 118140960795 + 2517733 * 2 ^ 59
def prefixEnd_2517733 : Nat := 4983230072969 + 3 ^ 40 * 2517733 * 2
def baseEnd_2517733 : Nat := 1292807188686503091758663

theorem tailTrace_2517733 : CollatzResearch.WordTrace tailWord_2517733 prefixEnd_2517733 1292807188686503091758663 := by
  unfold tailWord_2517733
  simp only [CollatzResearch.WordTrace]
  refine ⟨91829266587690810407893853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61219511058460540271929235 91829266587690810407893853)
  ·
    refine ⟨34435974970384053902960195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91829266587690810407893853 34435974970384053902960195)
    ·
      refine ⟨51653962455576080854440293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34435974970384053902960195 51653962455576080854440293)
      ·
        refine ⟨9685117960420515160207555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51653962455576080854440293 9685117960420515160207555)
        ·
          refine ⟨14527676940630772740311333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9685117960420515160207555 14527676940630772740311333)
          ·
            refine ⟨2723939426368269888808375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14527676940630772740311333 2723939426368269888808375)
            ·
              refine ⟨4085909139552404833212563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2723939426368269888808375 4085909139552404833212563)
              ·
                refine ⟨6128863709328607249818845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4085909139552404833212563 6128863709328607249818845)
                ·
                  refine ⟨2298323890998227718682067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6128863709328607249818845 2298323890998227718682067)
                  ·
                    refine ⟨3447485836497341578023101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2298323890998227718682067 3447485836497341578023101)
                    ·
                      refine ⟨1292807188686503091758663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3447485836497341578023101 1292807188686503091758663)
                      ·
                        rfl

theorem cell23_2517733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 1, 1, 3, 1, 3].length) (baseStart_2517733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2517733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2517733 prefixEnd_2517733 := by exact prefixLift 2517733
  have htrace : WordTrace (prefixWord ++ tailWord_2517733) baseStart_2517733 baseEnd_2517733 := by
    simpa [prefixWord, tailWord_2517733, baseEnd_2517733] using wordTrace_append hprefix tailTrace_2517733
  have hstable : (prefixWord ++ tailWord_2517733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2517733).length < 2 ^ (prefixWord ++ tailWord_2517733).sum := by decide
  have hdescent : baseEnd_2517733 < baseStart_2517733 := by decide
  rcases family_descends (prefixWord ++ tailWord_2517733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2517752 : List Nat := [2, 1, 2, 1, 1, 2, 3, 3, 1, 1, 6]
def baseStart_2517752 : Nat := 118140960795 + 2517752 * 2 ^ 59
def prefixEnd_2517752 : Nat := 4983230072969 + 3 ^ 40 * 2517752 * 2
def baseEnd_2517752 : Nat := 1292816944818938517421075

theorem tailTrace_2517752 : CollatzResearch.WordTrace tailWord_2517752 prefixEnd_2517752 1292816944818938517421075 := by
  unfold tailWord_2517752
  simp only [CollatzResearch.WordTrace]
  refine ⟨45914979787310988326417755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61219973049747984435223673 45914979787310988326417755)
  ·
    refine ⟨68872469680966482489626633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45914979787310988326417755 68872469680966482489626633)
    ·
      refine ⟨51654352260724861867219975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68872469680966482489626633 51654352260724861867219975)
      ·
        refine ⟨77481528391087292800829963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51654352260724861867219975 77481528391087292800829963)
        ·
          refine ⟨116222292586630939201244945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77481528391087292800829963 116222292586630939201244945)
          ·
            refine ⟨87166719439973204400933709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116222292586630939201244945 87166719439973204400933709)
            ·
              refine ⟨32687519789989951650350141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 87166719439973204400933709 32687519789989951650350141)
              ·
                refine ⟨12257819921246231868881303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32687519789989951650350141 12257819921246231868881303)
                ·
                  refine ⟨18386729881869347803321955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12257819921246231868881303 18386729881869347803321955)
                  ·
                    refine ⟨27580094822804021704982933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18386729881869347803321955 27580094822804021704982933)
                    ·
                      refine ⟨1292816944818938517421075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27580094822804021704982933 1292816944818938517421075)
                      ·
                        rfl

theorem cell23_2517752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 3, 1, 1, 6].length) (baseStart_2517752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2517752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2517752 prefixEnd_2517752 := by exact prefixLift 2517752
  have htrace : WordTrace (prefixWord ++ tailWord_2517752) baseStart_2517752 baseEnd_2517752 := by
    simpa [prefixWord, tailWord_2517752, baseEnd_2517752] using wordTrace_append hprefix tailTrace_2517752
  have hstable : (prefixWord ++ tailWord_2517752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2517752).length < 2 ^ (prefixWord ++ tailWord_2517752).sum := by decide
  have hdescent : baseEnd_2517752 < baseStart_2517752 := by decide
  rcases family_descends (prefixWord ++ tailWord_2517752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2517756 : List Nat := [2, 2, 2, 1, 3, 2, 3, 2, 1, 1, 4]
def baseStart_2517756 : Nat := 118140960795 + 2517756 * 2 ^ 59
def prefixEnd_2517756 : Nat := 4983230072969 + 3 ^ 40 * 2517756 * 2
def baseEnd_2517756 : Nat := 1292818998741556501771057

theorem tailTrace_2517756 : CollatzResearch.WordTrace tailWord_2517756 prefixEnd_2517756 1292818998741556501771057 := by
  unfold tailWord_2517756
  simp only [CollatzResearch.WordTrace]
  refine ⟨45915052733303742667990561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61220070311071656890654081 45915052733303742667990561)
  ·
    refine ⟨34436289549977807000992921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45915052733303742667990561 34436289549977807000992921)
    ·
      refine ⟨25827217162483355250744691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34436289549977807000992921 25827217162483355250744691)
      ·
        refine ⟨38740825743725032876117037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25827217162483355250744691 38740825743725032876117037)
        ·
          refine ⟨14527809653896887328543889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38740825743725032876117037 14527809653896887328543889)
          ·
            refine ⟨10895857240422665496407917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14527809653896887328543889 10895857240422665496407917)
            ·
              refine ⟨4085946465158499561152969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10895857240422665496407917 4085946465158499561152969)
              ·
                refine ⟨3064459848868874670864727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4085946465158499561152969 3064459848868874670864727)
                ·
                  refine ⟨4596689773303312006297091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3064459848868874670864727 4596689773303312006297091)
                  ·
                    refine ⟨6895034659954968009445637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4596689773303312006297091 6895034659954968009445637)
                    ·
                      refine ⟨1292818998741556501771057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6895034659954968009445637 1292818998741556501771057)
                      ·
                        rfl

theorem cell23_2517756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 3, 2, 1, 1, 4].length) (baseStart_2517756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2517756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2517756 prefixEnd_2517756 := by exact prefixLift 2517756
  have htrace : WordTrace (prefixWord ++ tailWord_2517756) baseStart_2517756 baseEnd_2517756 := by
    simpa [prefixWord, tailWord_2517756, baseEnd_2517756] using wordTrace_append hprefix tailTrace_2517756
  have hstable : (prefixWord ++ tailWord_2517756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2517756).length < 2 ^ (prefixWord ++ tailWord_2517756).sum := by decide
  have hdescent : baseEnd_2517756 < baseStart_2517756 := by decide
  rcases family_descends (prefixWord ++ tailWord_2517756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2517783 : List Nat := [1, 1, 3, 4, 3, 1, 2, 2, 2, 4]
def baseStart_2517783 : Nat := 118140960795 + 2517783 * 2 ^ 59
def prefixEnd_2517783 : Nat := 4983230072969 + 3 ^ 40 * 2517783 * 2
def baseEnd_2517783 : Nat := 430944287573075965377811

theorem tailTrace_2517783 : CollatzResearch.WordTrace tailWord_2517783 prefixEnd_2517783 430944287573075965377811 := by
  unfold tailWord_2517783
  simp only [CollatzResearch.WordTrace]
  refine ⟨91831090237509668947214003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61220726825006445964809335 91831090237509668947214003)
  ·
    refine ⟨137746635356264503420821005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91831090237509668947214003 137746635356264503420821005)
    ·
      refine ⟨51654988258599188782807877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137746635356264503420821005 51654988258599188782807877)
      ·
        refine ⟨9685310298487347896776477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51654988258599188782807877 9685310298487347896776477)
        ·
          refine ⟨3631991361932755461291179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9685310298487347896776477 3631991361932755461291179)
          ·
            refine ⟨5447987042899133191936769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3631991361932755461291179 5447987042899133191936769)
            ·
              refine ⟨4085990282174349893952577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5447987042899133191936769 4085990282174349893952577)
              ·
                refine ⟨3064492711630762420464433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4085990282174349893952577 3064492711630762420464433)
                ·
                  refine ⟨2298369533723071815348325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3064492711630762420464433 2298369533723071815348325)
                  ·
                    refine ⟨430944287573075965377811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2298369533723071815348325 430944287573075965377811)
                    ·
                      rfl

theorem cell23_2517783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 2, 2, 2, 4].length) (baseStart_2517783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2517783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2517783 prefixEnd_2517783 := by exact prefixLift 2517783
  have htrace : WordTrace (prefixWord ++ tailWord_2517783) baseStart_2517783 baseEnd_2517783 := by
    simpa [prefixWord, tailWord_2517783, baseEnd_2517783] using wordTrace_append hprefix tailTrace_2517783
  have hstable : (prefixWord ++ tailWord_2517783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2517783).length < 2 ^ (prefixWord ++ tailWord_2517783).sum := by decide
  have hdescent : baseEnd_2517783 < baseStart_2517783 := by decide
  rcases family_descends (prefixWord ++ tailWord_2517783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2517796 : List Nat := [2, 3, 1, 3, 3, 2, 1, 8]
def baseStart_2517796 : Nat := 118140960795 + 2517796 * 2 ^ 59
def prefixEnd_2517796 : Nat := 4983230072969 + 3 ^ 40 * 2517796 * 2
def baseEnd_2517796 : Nat := 47882945850656901676699

theorem tailTrace_2517796 : CollatzResearch.WordTrace tailWord_2517796 prefixEnd_2517796 47882945850656901676699 := by
  unfold tailWord_2517796
  simp only [CollatzResearch.WordTrace]
  refine ⟨45915782193231286083718621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61221042924308381444958161 45915782193231286083718621)
  ·
    refine ⟨17218418322461732281394483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45915782193231286083718621 17218418322461732281394483)
    ·
      refine ⟨25827627483692598422091725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17218418322461732281394483 25827627483692598422091725)
      ·
        refine ⟨9685360306384724408284397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25827627483692598422091725 9685360306384724408284397)
        ·
          refine ⟨3632010114894271653106649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9685360306384724408284397 3632010114894271653106649)
          ·
            refine ⟨2724007586170703739829987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3632010114894271653106649 2724007586170703739829987)
            ·
              refine ⟨4086011379256055609744981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2724007586170703739829987 4086011379256055609744981)
              ·
                refine ⟨47882945850656901676699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4086011379256055609744981 47882945850656901676699)
                ·
                  rfl

theorem cell23_2517796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 1, 8].length) (baseStart_2517796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2517796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2517796 prefixEnd_2517796 := by exact prefixLift 2517796
  have htrace : WordTrace (prefixWord ++ tailWord_2517796) baseStart_2517796 baseEnd_2517796 := by
    simpa [prefixWord, tailWord_2517796, baseEnd_2517796] using wordTrace_append hprefix tailTrace_2517796
  have hstable : (prefixWord ++ tailWord_2517796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2517796).length < 2 ^ (prefixWord ++ tailWord_2517796).sum := by decide
  have hdescent : baseEnd_2517796 < baseStart_2517796 := by decide
  rcases family_descends (prefixWord ++ tailWord_2517796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2517816 : List Nat := [2, 1, 2, 1, 3, 2, 1, 3, 3, 3, 2]
def baseStart_2517816 : Nat := 118140960795 + 2517816 * 2 ^ 59
def prefixEnd_2517816 : Nat := 4983230072969 + 3 ^ 40 * 2517816 * 2
def baseEnd_2517816 : Nat := 1292849807580826267020781

theorem tailTrace_2517816 : CollatzResearch.WordTrace tailWord_2517816 prefixEnd_2517816 1292849807580826267020781 := by
  unfold tailWord_2517816
  simp only [CollatzResearch.WordTrace]
  refine ⟨45916146923195057791582651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61221529230926743722110201 45916146923195057791582651)
  ·
    refine ⟨68874220384792586687373977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45916146923195057791582651 68874220384792586687373977)
    ·
      refine ⟨51655665288594440015530483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68874220384792586687373977 51655665288594440015530483)
      ·
        refine ⟨77483497932891660023295725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51655665288594440015530483 77483497932891660023295725)
        ·
          refine ⟨29056311724834372508735897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77483497932891660023295725 29056311724834372508735897)
          ·
            refine ⟨21792233793625779381551923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29056311724834372508735897 21792233793625779381551923)
            ·
              refine ⟨32688350690438669072327885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21792233793625779381551923 32688350690438669072327885)
              ·
                refine ⟨12258131508914500902122957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32688350690438669072327885 12258131508914500902122957)
                ·
                  refine ⟨4596799315842937838296109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12258131508914500902122957 4596799315842937838296109)
                  ·
                    refine ⟨1723799743441101689361041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4596799315842937838296109 1723799743441101689361041)
                    ·
                      refine ⟨1292849807580826267020781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1723799743441101689361041 1292849807580826267020781)
                      ·
                        rfl

theorem cell23_2517816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 3, 3, 3, 2].length) (baseStart_2517816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2517816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2517816 prefixEnd_2517816 := by exact prefixLift 2517816
  have htrace : WordTrace (prefixWord ++ tailWord_2517816) baseStart_2517816 baseEnd_2517816 := by
    simpa [prefixWord, tailWord_2517816, baseEnd_2517816] using wordTrace_append hprefix tailTrace_2517816
  have hstable : (prefixWord ++ tailWord_2517816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2517816).length < 2 ^ (prefixWord ++ tailWord_2517816).sum := by decide
  have hdescent : baseEnd_2517816 < baseStart_2517816 := by decide
  rcases family_descends (prefixWord ++ tailWord_2517816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2517833 : List Nat := [1, 2, 1, 1, 2, 6, 1, 3, 1, 3, 2]
def baseStart_2517833 : Nat := 118140960795 + 2517833 * 2 ^ 59
def prefixEnd_2517833 : Nat := 4983230072969 + 3 ^ 40 * 2517833 * 2
def baseEnd_2517833 : Nat := 1292858536751952700508203

theorem tailTrace_2517833 : CollatzResearch.WordTrace tailWord_2517833 prefixEnd_2517833 1292858536751952700508203 := by
  unfold tailWord_2517833
  simp only [CollatzResearch.WordTrace]
  refine ⟨91832913887328527486534153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61221942591552351657689435 91832913887328527486534153)
  ·
    refine ⟨68874685415496395614900615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91832913887328527486534153 68874685415496395614900615)
    ·
      refine ⟨103312028123244593422350923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68874685415496395614900615 103312028123244593422350923)
      ·
        refine ⟨154968042184866890133526385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103312028123244593422350923 154968042184866890133526385)
        ·
          refine ⟨116226031638650167600144789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 154968042184866890133526385 116226031638650167600144789)
          ·
            refine ⟨5448095233061726606256787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 116226031638650167600144789 5448095233061726606256787)
            ·
              refine ⟨8172142849592589909385181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5448095233061726606256787 8172142849592589909385181)
              ·
                refine ⟨3064553568597221216019443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8172142849592589909385181 3064553568597221216019443)
                ·
                  refine ⟨4596830352895831824029165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3064553568597221216019443 4596830352895831824029165)
                  ·
                    refine ⟨1723811382335936934010937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4596830352895831824029165 1723811382335936934010937)
                    ·
                      refine ⟨1292858536751952700508203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1723811382335936934010937 1292858536751952700508203)
                      ·
                        rfl

theorem cell23_2517833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 3, 1, 3, 2].length) (baseStart_2517833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2517833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2517833 prefixEnd_2517833 := by exact prefixLift 2517833
  have htrace : WordTrace (prefixWord ++ tailWord_2517833) baseStart_2517833 baseEnd_2517833 := by
    simpa [prefixWord, tailWord_2517833, baseEnd_2517833] using wordTrace_append hprefix tailTrace_2517833
  have hstable : (prefixWord ++ tailWord_2517833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2517833).length < 2 ^ (prefixWord ++ tailWord_2517833).sum := by decide
  have hdescent : baseEnd_2517833 < baseStart_2517833 := by decide
  rcases family_descends (prefixWord ++ tailWord_2517833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2517863 : List Nat := [1, 1, 5, 1, 2, 2, 3, 1, 1, 4, 2]
def baseStart_2517863 : Nat := 118140960795 + 2517863 * 2 ^ 59
def prefixEnd_2517863 : Nat := 4983230072969 + 3 ^ 40 * 2517863 * 2
def baseEnd_2517863 : Nat := 1292873941171587583133065

theorem tailTrace_2517863 : CollatzResearch.WordTrace tailWord_2517863 prefixEnd_2517863 1292873941171587583133065 := by
  unfold tailWord_2517863
  simp only [CollatzResearch.WordTrace]
  refine ⟨91834008077219842610126243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61222672051479895073417495 91834008077219842610126243)
  ·
    refine ⟨137751012115829763915189365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91834008077219842610126243 137751012115829763915189365)
    ·
      refine ⟨12914157385859040367049003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 137751012115829763915189365 12914157385859040367049003)
      ·
        refine ⟨19371236078788560550573505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12914157385859040367049003 19371236078788560550573505)
        ·
          refine ⟨14528427059091420412930129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19371236078788560550573505 14528427059091420412930129)
          ·
            refine ⟨10896320294318565309697597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14528427059091420412930129 10896320294318565309697597)
            ·
              refine ⟨4086120110369461991136599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10896320294318565309697597 4086120110369461991136599)
              ·
                refine ⟨6129180165554192986704899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4086120110369461991136599 6129180165554192986704899)
                ·
                  refine ⟨9193770248331289480057349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6129180165554192986704899 9193770248331289480057349)
                  ·
                    refine ⟨1723831921562116777510753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9193770248331289480057349 1723831921562116777510753)
                    ·
                      refine ⟨1292873941171587583133065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1723831921562116777510753 1292873941171587583133065)
                      ·
                        rfl

theorem cell23_2517863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 3, 1, 1, 4, 2].length) (baseStart_2517863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2517863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2517863 prefixEnd_2517863 := by exact prefixLift 2517863
  have htrace : WordTrace (prefixWord ++ tailWord_2517863) baseStart_2517863 baseEnd_2517863 := by
    simpa [prefixWord, tailWord_2517863, baseEnd_2517863] using wordTrace_append hprefix tailTrace_2517863
  have hstable : (prefixWord ++ tailWord_2517863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2517863).length < 2 ^ (prefixWord ++ tailWord_2517863).sum := by decide
  have hdescent : baseEnd_2517863 < baseStart_2517863 := by decide
  rcases family_descends (prefixWord ++ tailWord_2517863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2517879 : List Nat := [1, 1, 3, 1, 1, 2, 1, 4, 1, 5, 3]
def baseStart_2517879 : Nat := 118140960795 + 2517879 * 2 ^ 59
def prefixEnd_2517879 : Nat := 4983230072969 + 3 ^ 40 * 2517879 * 2
def baseEnd_2517879 : Nat := 1292882156862059520532991

theorem tailTrace_2517879 : CollatzResearch.WordTrace tailWord_2517879 prefixEnd_2517879 1292882156862059520532991 := by
  unfold tailWord_2517879
  simp only [CollatzResearch.WordTrace]
  refine ⟨91834591645161877342708691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61223061096774584895139127 91834591645161877342708691)
  ·
    refine ⟨137751887467742816014063037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91834591645161877342708691 137751887467742816014063037)
    ·
      refine ⟨51656957800403556005273639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137751887467742816014063037 51656957800403556005273639)
      ·
        refine ⟨77485436700605334007910459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51656957800403556005273639 77485436700605334007910459)
        ·
          refine ⟨116228155050908001011865689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77485436700605334007910459 116228155050908001011865689)
          ·
            refine ⟨87171116288181000758899267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116228155050908001011865689 87171116288181000758899267)
            ·
              refine ⟨130756674432271501138348901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87171116288181000758899267 130756674432271501138348901)
              ·
                refine ⟨24516876456050906463440419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 130756674432271501138348901 24516876456050906463440419)
                ·
                  refine ⟨36775314684076359695160629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24516876456050906463440419 36775314684076359695160629)
                  ·
                    refine ⟨3447685751632158721421309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36775314684076359695160629 3447685751632158721421309)
                    ·
                      refine ⟨1292882156862059520532991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3447685751632158721421309 1292882156862059520532991)
                      ·
                        rfl

theorem cell23_2517879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 4, 1, 5, 3].length) (baseStart_2517879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2517879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2517879 prefixEnd_2517879 := by exact prefixLift 2517879
  have htrace : WordTrace (prefixWord ++ tailWord_2517879) baseStart_2517879 baseEnd_2517879 := by
    simpa [prefixWord, tailWord_2517879, baseEnd_2517879] using wordTrace_append hprefix tailTrace_2517879
  have hstable : (prefixWord ++ tailWord_2517879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2517879).length < 2 ^ (prefixWord ++ tailWord_2517879).sum := by decide
  have hdescent : baseEnd_2517879 < baseStart_2517879 := by decide
  rcases family_descends (prefixWord ++ tailWord_2517879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2517899 : List Nat := [1, 1, 1, 1, 4, 2, 3, 1, 4, 5]
def baseStart_2517899 : Nat := 118140960795 + 2517899 * 2 ^ 59
def prefixEnd_2517899 : Nat := 4983230072969 + 3 ^ 40 * 2517899 * 2
def baseEnd_2517899 : Nat := 430964142158383147427633

theorem tailTrace_2517899 : CollatzResearch.WordTrace tailWord_2517899 prefixEnd_2517899 430964142158383147427633 := by
  unfold tailWord_2517899
  simp only [CollatzResearch.WordTrace]
  refine ⟨91835321105089420758436751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61223547403392947172291167 91835321105089420758436751)
  ·
    refine ⟨137752981657634131137655127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91835321105089420758436751 137752981657634131137655127)
    ·
      refine ⟨206629472486451196706482691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137752981657634131137655127 206629472486451196706482691)
      ·
        refine ⟨309944208729676795059724037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206629472486451196706482691 309944208729676795059724037)
        ·
          refine ⟨58114539136814399073698257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 309944208729676795059724037 58114539136814399073698257)
          ·
            refine ⟨43585904352610799305273693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58114539136814399073698257 43585904352610799305273693)
            ·
              refine ⟨16344714132229049739477635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43585904352610799305273693 16344714132229049739477635)
              ·
                refine ⟨24517071198343574609216453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16344714132229049739477635 24517071198343574609216453)
                ·
                  refine ⟨4596950849689420239228085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24517071198343574609216453 4596950849689420239228085)
                  ·
                    refine ⟨430964142158383147427633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4596950849689420239228085 430964142158383147427633)
                    ·
                      rfl

theorem cell23_2517899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 1, 4, 5].length) (baseStart_2517899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2517899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2517899 prefixEnd_2517899 := by exact prefixLift 2517899
  have htrace : WordTrace (prefixWord ++ tailWord_2517899) baseStart_2517899 baseEnd_2517899 := by
    simpa [prefixWord, tailWord_2517899, baseEnd_2517899] using wordTrace_append hprefix tailTrace_2517899
  have hstable : (prefixWord ++ tailWord_2517899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2517899).length < 2 ^ (prefixWord ++ tailWord_2517899).sum := by decide
  have hdescent : baseEnd_2517899 < baseStart_2517899 := by decide
  rcases family_descends (prefixWord ++ tailWord_2517899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2517909 : List Nat := [1, 3, 2, 1, 1, 4, 1, 1, 1, 1, 7]
def baseStart_2517909 : Nat := 118140960795 + 2517909 * 2 ^ 59
def prefixEnd_2517909 : Nat := 4983230072969 + 3 ^ 40 * 2517909 * 2
def baseEnd_2517909 : Nat := 1292897561281694403157853

theorem tailTrace_2517909 : CollatzResearch.WordTrace tailWord_2517909 prefixEnd_2517909 1292897561281694403157853 := by
  unfold tailWord_2517909
  simp only [CollatzResearch.WordTrace]
  refine ⟨91835685835053192466300781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61223790556702128310867187 91835685835053192466300781)
  ·
    refine ⟨34438382188144947174862793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91835685835053192466300781 34438382188144947174862793)
    ·
      refine ⟨25828786641108710381147095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34438382188144947174862793 25828786641108710381147095)
      ·
        refine ⟨38743179961663065571720643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25828786641108710381147095 38743179961663065571720643)
        ·
          refine ⟨58114769942494598357580965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38743179961663065571720643 58114769942494598357580965)
          ·
            refine ⟨10896519364217737192046431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58114769942494598357580965 10896519364217737192046431)
            ·
              refine ⟨16344779046326605788069647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10896519364217737192046431 16344779046326605788069647)
              ·
                refine ⟨24517168569489908682104471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16344779046326605788069647 24517168569489908682104471)
                ·
                  refine ⟨36775752854234863023156707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24517168569489908682104471 36775752854234863023156707)
                  ·
                    refine ⟨55163629281352294534735061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36775752854234863023156707 55163629281352294534735061)
                    ·
                      refine ⟨1292897561281694403157853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 55163629281352294534735061 1292897561281694403157853)
                      ·
                        rfl

theorem cell23_2517909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 1, 1, 1, 7].length) (baseStart_2517909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2517909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2517909 prefixEnd_2517909 := by exact prefixLift 2517909
  have htrace : WordTrace (prefixWord ++ tailWord_2517909) baseStart_2517909 baseEnd_2517909 := by
    simpa [prefixWord, tailWord_2517909, baseEnd_2517909] using wordTrace_append hprefix tailTrace_2517909
  have hstable : (prefixWord ++ tailWord_2517909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2517909).length < 2 ^ (prefixWord ++ tailWord_2517909).sum := by decide
  have hdescent : baseEnd_2517909 < baseStart_2517909 := by decide
  rcases family_descends (prefixWord ++ tailWord_2517909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
